import data.int.modeq
import data.int.parity
import tactic.omega.main
import tactic
import ring_theory.int.basic
import ring_theory.coprime
import tactic.slim_check
import data.real.basic
import tactic.ring_exp

/-
Proof that p ∣ a^2 + b^2 where a b are coprime → p = x^2 + y^2

This is known as descent step, used by Euler proving p ≡ 1 [MOD 4] ↔ p = x^2 + y^2. Descent step
combined with reciprocity step, p ≡ 1 [MOD 4] → p ∣ a^2 + b^2 where a b are coprime, finishes
the proof. This method can be generalise for x^2 + 2y^2 and x^2 + 3y^2. More of this can be found
in "Primes of the Form x^2 + ny^2" by David A. Cox.

The proof is actually elementary, but it took me almost 1k lines because I was not yet familiar
with how lean defines nat, int, divide and mod etc and I was stuck switching between nat and int. I shorten it down to 600 lines. Although I
think I can do better than that, I will advance to other topics rather than spending a lot of time
on redundancy because this method is quite elementary and just solves for n = 1, 2, 3 and I just
do it for practice.

I am not sure if I can formalise the whole book in lean because it requires stuffs like genus
theory, higher reciprocity and class field theory.
-/

open int

--definition of prime in ring theory implies that in natural number
theorem prime_pos_int {n : ℤ} (npos : n > 0) (h : prime n) :
  2 ≤ n ∧ ∀ (m : ℤ), m > 0 → m ∣ n → m = 1 ∨ m = n :=
begin
  have hneq : n ≠ 1,
    intro hn, apply h.2.1, rw hn, norm_num,
  split, omega,
  intros m mpos hm,
  cases hm with k hk,
  have hdvd : m * k ∣ m ∨ m * k ∣ k,
    rw ←hk, apply h.2.2, rw hk,
  cases hdvd with hdvd hdvd,
  { right,
    suffices : m*k = m*1,
      replace : k = 1, from (mul_right_inj' (by linarith)).mp this,
      rw [hk, this], simp,
    simp,
    exact dvd_antisymm (by linarith) (by linarith) hdvd ⟨k, by simp⟩ },
  left,
  apply dvd_antisymm; try {linarith},
  { have : k ≠ 0,
      intro hf, rw hf at hk, rw hk at h, simp at h, exact h,
    apply (mul_dvd_mul_iff_right this).mp,
    simp, exact hdvd },
  { exact ⟨m, by simp⟩ }
end

--this helps when we lift a prime number in int
theorem int_prime_eq_nat_prime {a : ℕ} : nat.prime a ↔ prime (a : ℤ) :=
begin
  split; intro hp,
  cases hp with a2 advd,
  split, linarith,
  split,
  { intro hf,
    rw is_unit_iff_exists_inv at hf,
    cases hf with b hf,
    replace hf : (a : ℤ) ∣ 1, from ⟨b, hf.symm⟩,
    norm_cast at hf,
    have hf : a = 1, from nat.dvd_one.mp hf,
    linarith },
  { intros b c hdvd, by_contradiction hf, push_neg at hf,
    cases hf with h₁ h₂,
    have : is_coprime ↑a b,
      rw ←gcd_eq_one_iff_coprime,
      have leftdvd : ↑(int.gcd ↑a b) ∣ (a : ℤ), from (a : ℤ).gcd_dvd_left b,
      norm_cast at leftdvd,
      cases advd ((a : ℤ).gcd b) leftdvd with ht hf,
      exact ht,
      have : ↑(int.gcd ↑a b) ∣ b, from (a : ℤ).gcd_dvd_right b,
      rw hf at this, exact absurd this h₁,
    have hac : ↑a ∣ c, from is_coprime.dvd_of_dvd_mul_left this hdvd,
    exact h₂ hac },
  have apos : (a : ℤ) > 0,
    norm_cast,
    have := hp.1, norm_cast at this,
    exact pos_iff_ne_zero.mpr this,
  cases prime_pos_int (apos) hp with a2 advd,
  split; zify,
  { exact a2 },
  { intros m hm,
    apply advd,
    norm_cast, rw pos_iff_ne_zero,
    intro m0,
    rw [m0, zero_dvd_iff] at hm,
    linarith,
    norm_cast, exact hm}
end

lemma int_dvd_one (x k : ℤ) (h : 1 = k*x) (xnonneg : x ≥ 0) : x = 1 :=
begin
  replace h : x ∣ 1, from ⟨k, by {rw h, ring}⟩,
  lift x to ℕ using xnonneg,
  norm_cast at *,
  exact nat.dvd_one.mp h
end

lemma sq_prime {x : ℤ} (h : prime (x^2)) : false :=
begin
  cases em (x = 0) with hn ht,
    rw hn at h, norm_num at h, exact h,
  replace h := prime_pos_int (pow_bit0_pos ht 1) h,
  rw ←sqr_abs at h,
  cases h with h2 h,
  cases (h (abs x) (abs_pos.2 ht) (by {rw pow_two, exact dvd.intro (abs x) rfl})) with hx hx,
  rw hx at h2, linarith,
  replace hx := eq.trans (mul_one (abs x)) hx, rw [pow_two] at hx,
  replace ht := abs_pos.2 ht,
  have := (mul_right_inj' (by linarith)).1 hx,
  rw ←this at h2, linarith
end

lemma prime_sq_sq (x y : ℤ) (h : prime (x^2 + y^2)) : is_coprime x y :=
begin
  rw ←gcd_eq_one_iff_coprime,
  cases (int.gcd_dvd_left x y) with n hn,
  cases (int.gcd_dvd_right x y) with m hm,
  have cal : x^2 + y^2 = ↑(x.gcd y) * (n * ↑(x.gcd y) * n + m * ↑(x.gcd y) * m),
    have hx2 : x^2 = (↑(x.gcd y) * n)^2, begin conv begin to_lhs, rw hn, end, end,
    have hy2 : y^2 = (↑(x.gcd y) * m)^2, begin conv begin to_lhs, rw hm, end, end,
    rw [hx2, hy2, pow_two, pow_two],
    rw [mul_assoc, mul_assoc, mul_add], ring,
  cases em (x = 0 ∧ y = 0) with hn ht,
  rw [hn.1, hn.2] at h, norm_num at h, exfalso, exact h,
  have sumpos : x^2 + y^2 > 0,
    rw not_and_distrib at ht, cases ht with ht ht;
    have := pow_bit0_pos ht 1; have := pow_two_nonneg x; have := pow_two_nonneg y;
    linarith,
  cases (prime_pos_int sumpos h) with h₁ h₂,
  have gcdpos : ((x.gcd y) : ℤ) > 0,
    have hnonneg : ((x.gcd y) : ℤ) ≥ 0,
      have := zero_le (gcd x y), linarith,
    have hnonzero : ((x.gcd y) : ℤ) ≠ 0,
      simp, intro hn, rw int.gcd_eq_zero_iff at hn, exact ht hn,
    exact (ne.symm hnonzero).le_iff_lt.1 hnonneg,
  specialize h₂ ↑(x.gcd y) gcdpos (dvd.intro _ (eq.symm cal)),
  clear ht,
  cases h₂ with h₂ h₂, linarith,
  cases em (x = 0 ∨ y = 0) with hf ht,
  cases hf with hf hf; rw hf at h; norm_num at h; exfalso; exact sq_prime h,
  replace ht : x ≠ 0 ∧ y ≠ 0, exact not_or_distrib.1 ht,
  replace cal := eq.trans h₂ cal,
  replace cal : 1 = (n * ↑(x.gcd y) * n + m * ↑(x.gcd y) * m),
    replace cal := eq.trans (mul_one ↑(x.gcd y)) cal,
    exact (mul_right_inj' (by linarith)).1 cal,
  rw h₂ at cal,
  rw [mul_assoc, mul_assoc, mul_comm (x ^ 2 + y ^ 2) n, mul_comm (x ^ 2 + y ^ 2) m,
      ←mul_assoc, ←mul_assoc] at cal,
  rw [←add_mul, ←h₂] at cal, have := int_dvd_one _ _ cal (by linarith), linarith
end

lemma sq_sq_zero (x y : ℤ) (h : x^2 + y^2 = 0) : x = 0 ∧ y = 0 :=
begin
  by_contradiction hn,
  cases (not_and_distrib.1 hn) with h0 h0;
  have := pow_bit0_pos h0 1; have := pow_two_nonneg x; have := pow_two_nonneg y;
  linarith
end

lemma neg_coprime {x y : ℤ} (h : is_coprime x y) : is_coprime (-x) y :=
begin
  unfold is_coprime at *,
  rcases h with ⟨a, b, h⟩,
  use (-a), use b,
  simp, exact h
end

lemma abs_coprime {x y : ℤ} (h : is_coprime x y) : is_coprime (abs x) (abs y) :=
begin
  unfold is_coprime at *,
  rcases h with ⟨a, b, h⟩,
  cases em (x ≥ 0) with hx hx;
  cases em (y ≥ 0) with hy hy,
  use a, use b, rw [abs_of_nonneg hx, abs_of_nonneg hy], exact h,
  push_neg at hy, use a, use (-b), rw [abs_of_nonneg hx, abs_of_neg hy], rw ←h, ring,
  push_neg at hx, use (-a), use b, rw [abs_of_neg hx, abs_of_nonneg hy], rw ←h, ring,
  push_neg at hx, push_neg at hy, use (-a), use (-b), rw [abs_of_neg hx, abs_of_neg hy], rw ←h, ring
end

lemma qr_thm_alter (a p : ℤ) (h0 : p > 0) : ∃ q r : ℤ, a = p*q + r ∧ (abs r : ℝ) ≤ (p : ℝ)/2 :=
begin
  have key := (div_add_mod a p).symm,
  cases em ((↑(a % p) : ℝ) ≤ (p/2 : ℝ)) with hl hl,
  use a / p, use a % p, split, exact key,
  rw abs_of_nonneg, exact hl, simp, exact mod_nonneg a (show p ≠ 0, by linarith),
  use ((a / p) + 1), use (a % p - p), split,
  ring, rw mul_comm, exact key,
  push_neg at hl, rw abs_of_neg, simp, linarith,
  simp, exact mod_lt_of_pos a h0
end

theorem sum_of_sq_dvd_sum_of_sq {N q : ℤ}
(hN : ∃ a b : ℤ, (is_coprime a b ∧ N = a^2 + b^2))
(hpd : prime q ∧ q ∣ N) (hq : ∃ x y : ℤ, q = x^2 + y^2) :
∃ c d : ℤ, is_coprime c d ∧ N/q = c^2 + d^2 :=
begin
  rcases hN with ⟨a, b, hab, hN⟩,
  rcases hq with ⟨x, y, hq⟩,
  have h₁ : q ∣ x^2 * N - a^2 * q,
    cases hpd.2 with k hk, use x^2 * k - a^2,
    rw [mul_sub_left_distrib, hk, mul_left_comm (x^2) q k, mul_comm (a^2) q],
  have h₂ : x^2 * N - a^2 * q = (x*b + a*y) * (x*b - a*y),
    calc x^2 * N - a^2 * q = x^2 * (a^2 + b^2) - a^2 * (x^2 + y^2) : by rw [hN, hq]
                       ... = x^2 * b^2 - a^2 * y^2                 : by {rw [mul_add, mul_add, ←sub_sub, mul_comm], simp}
                       ... = (x*b)^2 - (a*y)^2                     : by rw [←(mul_pow x b 2), ←(mul_pow a y 2)]
                       ... = (x*b + a*y) * (x*b - a*y)             : sq_sub_sq _ _,
  rw h₂ at h₁, clear h₂,
  revert a, have key : ∀ (a : ℤ), is_coprime a b → N = a ^ 2 + b ^ 2
                      → q ∣ (x * b + a * y)
                      → (∃ (c d : ℤ), is_coprime c d ∧ N / q = c ^ 2 + d ^ 2),
  intros a hab hN h,
  cases h with d hd,
  have cal : (a - d*y)*y = a*y - d*y^2, by ring,
        rw [(eq_sub_of_add_eq' hd), hq, (add_mul (x^2) (y^2) d), (mul_comm (y^2) d),
            ←add_sub, ←add_sub, sub_sub, (add_comm (x*b) (d * y^2)), ←sub_sub] at cal,
        simp at cal,
        rw [tactic.ring.add_neg_eq_sub, pow_two, mul_assoc, ←mul_sub] at cal,
  have h₃ : x ∣ a - d*y,
    have : x ∣ (a - d*y)*y,
    rw cal, exact dvd.intro (x*d - b) rfl,
  exact is_coprime.dvd_of_dvd_mul_right (prime_sq_sq x y (by {rw ←hq, exact hpd.1})) this,
  cases h₃ with c hc,
  rw hc at cal,
  cases em (x = 0 ∨ y = 0) with hf ht,
  cases hf with hf hf; rw hq at hpd; rw hf at hpd; norm_num at hpd; exfalso; exact sq_prime hpd.1,
  replace ht : x ≠ 0 ∧ y ≠ 0, exact not_or_distrib.1 ht,
  rw mul_assoc at cal, replace cal := (mul_right_inj' ht.1).1 cal,
  have ha : a = x*c + d*y, by linarith, have hb : b = x*d - c*y, by linarith,
  have key : N = q * (c^2 + d^2),
    calc N = a^2 + b^2                             : hN
       ... = (x*c + d*y)^2 + (x*d - c*y)^2         : by rw [ha, hb]
       ... = x^2*c^2 + x^2*d^2 + y^2*c^2 + y^2*d^2 : by ring
       ... = x^2*(c^2 + d^2) + y^2*(c^2 + d^2)     : by ring
       ... = (x^2 + y^2) * (c^2 + d^2)             : by ring
       ... = q * (c^2 + d^2)                       : by rw ←hq,
  use c, use d,
  split,
  cases (int.gcd_dvd_left c d) with n hn,
  cases (int.gcd_dvd_right c d) with m hm,
  rw hn at ha, rw hn at hb,
  have : d * y = ↑(c.gcd d) * m * y, begin conv begin to_lhs, rw hm, end, end, rw this at ha, clear this,
  have : x * d = x * (↑(c.gcd d) * m), begin conv begin to_lhs, rw hm, end, end, rw this at hb, clear this,
  rw [←mul_assoc, mul_comm x _, mul_assoc, mul_assoc, ←mul_add] at ha,
  rw [←mul_assoc, mul_comm x _, mul_assoc, mul_assoc, ←mul_sub] at hb,
  replace ha := dvd.intro _ (eq.symm ha),
  replace hb := dvd.intro _ (eq.symm hb),
  have gcd_dvd := int.dvd_gcd ha hb,
  rw ←gcd_eq_one_iff_coprime,
  rw ←gcd_eq_one_iff_coprime at hab,
  cases gcd_dvd with k hk,
  rw [hab, mul_comm] at hk, have := zero_le (c.gcd d), simp at hk,
  have := int_dvd_one _ _ hk (by linarith), linarith,
  rw key, cases em (q = 0) with hw hr, rw hw at hpd, unfold prime at hpd, exact absurd (rfl) (hpd.1.1),
  rw mul_comm, exact int.mul_div_cancel (c^2 + d^2) hr,
  intros a hab hN h,
  cases (prime.div_or_div hpd.1 h) with h h, exact key a hab hN h,
  apply (key (-a)), exact neg_coprime hab, rw hN, ring, simp, exact h
end

lemma dvd_leq {a b : ℤ} (anonneg : a ≥ 0) (bpos : b > 0)
(hdvd : a ∣ b) : a ≤ b :=
begin
  lift a to ℕ using anonneg,
  lift b to ℕ using (show b ≥ 0, by linarith),
  norm_cast at *,
  exact nat.le_of_dvd bpos hdvd
end

lemma dvd_abs {a b : ℤ} (h : a ∣ b) : a ∣ abs b :=
begin
  cases em (b ≥ 0) with hb hb,
  rw abs_of_nonneg hb, exact h,
  push_neg at hb, rw abs_of_neg hb, exact (dvd_neg a b).2 h
end

--some calculations involving inequality, not really important as it's easy for people
lemma simp_cal {m n p : ℤ} (habsm: ((abs m) : ℝ) ≤ ↑p / 2) (habsn: ((abs n) : ℝ) ≤ ↑p / 2) (ppos : p ≥ 0)
: ((m^2) : ℝ) + ((n^2) : ℝ) ≤ (p^2/2 : ℝ) :=
begin
  rw [pow_two, pow_two, ←abs_mul_abs_self ↑m, ←abs_mul_abs_self ↑n],
  have hm : (abs ↑m) * (abs ↑m ) ≤ ((p / 2) : ℝ) * ((p / 2) : ℝ),
    have absm : ((abs m) : ℝ) ≥ 0, from abs_nonneg ↑m,
    exact mul_self_le_mul_self absm habsm,
  have hn : (abs ↑n) * (abs ↑n) ≤ ((p / 2) : ℝ) * ((p / 2) : ℝ),
    have absn : ((abs n) : ℝ) ≥ 0, from abs_nonneg ↑n,
    exact mul_self_le_mul_self absn habsn,
  have : ((p ^ 2 / 2) : ℝ) = ((p / 2) : ℝ) * ((p / 2) : ℝ) + ((p / 2) : ℝ) * ((p / 2) : ℝ), ring,
  rw this,
  exact add_le_add hm hn
end

lemma largest_divisor {p q N : ℤ} (hdvd: p*q ∣ N) (hp : p > 0) (hq : q > 0) (hN : N > 0)
(hleq : (N : ℝ) ≤ (p^2/2 : ℝ) ) : q < p :=
begin
  cases hdvd with k hdvd,
  rw hdvd at hleq,
  rw pow_two at hleq,
  simp at hleq,
  have ppos : (p : ℝ) > 0,
    simp, linarith,
  rw mul_assoc at hleq,
  have : (q : ℝ) * (k : ℝ) ≤ (p : ℝ) / 2,
    apply (mul_le_mul_left ppos).1, linarith,
  have hk : k > 0,
    have : p*q > 0, exact mul_pos hp hq,
    by_contradiction hk, push_neg at hk,
    have : N ≤ 0, rw hdvd, exact linarith.mul_nonpos hk this,
    linarith,
  have h₁ : (q : ℝ) ≤ (q : ℝ)*(k : ℝ),
    have hk1 : (k : ℝ) ≥ 1, norm_cast, linarith,
    suffices : (q : ℝ)*1 ≤ (q : ℝ)*(k : ℝ), linarith,
    have hq1 : (q : ℝ) > 0, simp, exact hq,
    exact (mul_le_mul_left hq1).2 hk1,
  have h₂ : (p : ℝ)/2 ≤ (p : ℝ),
    linarith,
  have leq : (q : ℝ) ≤ (p : ℝ), by linarith, simp at leq,
  have neq : q ≠ p, intro hf, rw hf at hleq, rw hf at this, rw hf at h₁, linarith,
  exact (ne.le_iff_lt neq).1 leq
end

lemma descent_wlog {p : ℤ} (hp : prime p) (ho : odd p) (ppos : p > 0) :
(∃ a b : ℤ, int.gcd a b = 1 ∧ p ∣ a^2 + b^2)
→ (∃ m n : ℤ, int.gcd m n = 1 ∧ p ∣ m^2 + n^2 ∧ (m^2 + n^2 : ℝ) ≤ (p^2/2 : ℝ)) :=
begin
  intro h,
  rcases h with ⟨a, b, hab, hdvd⟩,
  rcases qr_thm_alter (abs a) p ppos with ⟨q, r, hqr, hr⟩,
  rcases qr_thm_alter (abs b) p ppos with ⟨q', r', hqr', hr'⟩,
  have hdvd : p ∣ r^2 + r'^2,
    cases hdvd with k hk,
    have : a^2 = (abs a)^2, by norm_num, rw this at hk, clear this,
    have : b^2 = (abs b)^2, by norm_num, rw this at hk, clear this,
    rw [hqr, hqr'] at hk,
    have key : p * (k - (q*p*q + 2*q*r + q'*p*q' + 2*q'*r')) = r^2 + r'^2,
      rw [mul_sub, ←hk], ring,
    rw ←key, exact dvd.intro _ rfl,
  cases em (r = 0 ∨ r' = 0) with hl h0,
  cases hl with h0 h0;
  rw h0 at *; norm_num at *,
  have : p ∣ r' → false,
    intro hpr,
    cases hpr with k hpr,
    rw hpr at *,
    rw ←mul_add at hqr',
    have hn : p ∣ int.gcd a b,
      have := gcd_eq_one_iff_coprime.2 (abs_coprime (gcd_eq_one_iff_coprime.1 hab)),
      rw [hab, ←this],
      apply int.dvd_gcd,
      rw hqr, exact dvd.intro q rfl,
      rw hqr', exact dvd.intro (q' + k) rfl,
    rw hab at hn, cases hn with m hn, rw mul_comm at hn, exfalso, simp at hn,
    rw (int_dvd_one p m hn (by linarith)) at hp, simp at hp, exact hp,
  rw pow_two at hdvd,
  cases prime.div_or_div hp hdvd with hpr hpr;
  exact absurd hpr this,
  have : p ∣ r → false,
    intro hpr,
    cases hpr with k hpr,
    rw hpr at *,
    rw ←mul_add at hqr,
    have hn : p ∣ int.gcd a b,
      have := gcd_eq_one_iff_coprime.2 (abs_coprime (gcd_eq_one_iff_coprime.1 hab)),
      rw [hab, ←this],
      apply int.dvd_gcd,
      rw hqr, exact dvd.intro (q + k) rfl,
      rw hqr', exact dvd.intro q' rfl,
    rw hab at hn, cases hn with m hn, rw mul_comm at hn, exfalso, simp at hn,
    rw (int_dvd_one p m hn (by linarith)) at hp, simp at hp, exact hp,
  rw pow_two at hdvd,
  cases prime.div_or_div hp hdvd with hpr hpr;
  exact absurd hpr this,
  push_neg at h0,
  have gcdpos : ((int.gcd r r') : ℤ) > 0,
    have : int.gcd r r' ≠ 0, by {intro hn, rw int.gcd_eq_zero_iff at hn, exact h0.1 hn.1},
    simp, exact pos_iff_ne_zero.2 this,
  have : ¬(p ∣ ↑(int.gcd r r')),
    intro hn,
    have h₁ : (p : ℝ) ≤ (((int.gcd r r') : ℤ) : ℝ),
      have h₁ : p ≤ ↑(int.gcd r r'),
        apply dvd_leq, linarith, exact gcdpos, exact hn,
      simp, norm_cast, exact h₁,
    have h₂ : (((int.gcd r r') : ℤ) : ℝ) ≤ ((abs r) : ℝ),
      have h₂ : ↑(int.gcd r r') ≤ abs r,
        apply dvd_leq, linarith, exact abs_pos.2 h0.1, exact dvd_abs (int.gcd_dvd_left r r'),
      norm_cast, exact h₂,
    have h₃ : (p / 2 : ℝ) < (p : ℝ), from half_lt_self (show (p : ℝ) > 0, by {simp, exact ppos}),
    linarith,
  cases (int.gcd_dvd_left r r') with n hn,
  cases (int.gcd_dvd_right r r') with m hm,
  have cal : r^2 + r'^2 = (↑(r.gcd r'))^2 * (n^2 + m^2),
    calc r^2 + r'^2 = (↑(r.gcd r') * n)^2 + (↑(r.gcd r') * m)^2 : by rw [←hn, ←hm]
                ... = (↑(r.gcd r'))^2 * (n^2 + m^2)             : by ring,
  rw cal at hdvd,
  cases prime.div_or_div hp hdvd with hpdvd hpdvd,
  rw pow_two at hpdvd, cases prime.div_or_div hp hpdvd with hpdvd hpdvd; exact absurd hpdvd this,
  use m, use n, split,
  have hcoprime : ↑(int.gcd m n) = (1 : ℤ),
    cases (int.gcd_dvd_left m n) with k hk,
    cases (int.gcd_dvd_right m n) with l hl,
    rw hk at hm, rw hl at hn,
    rw ←mul_assoc at hm, rw ←mul_assoc at hn,
    have gcddvd : ↑(r.gcd r') * ↑(m.gcd n) ∣ ↑(r.gcd r'),
      apply int.dvd_gcd, use l, exact hn, use k, exact hm,
    cases gcddvd with k hk, rw mul_assoc at hk, replace hk := eq.trans (mul_one _) hk,
    have h1 := (mul_right_inj' (show ↑(r.gcd r') ≠ (0 : ℤ), by linarith)).1 hk,
    rw mul_comm at h1,
    exact int_dvd_one ↑(m.gcd n) k h1 (coe_zero_le _),
  linarith,
  split, rw add_comm, exact hpdvd,
  have habsm : (↑(abs m) : ℝ) ≤ p/2,
    suffices : (↑(abs m) : ℝ) ≤ (↑(abs r') : ℝ), simp at *, linarith,
    rw [hm, abs_mul], simp,
    have : abs (m : ℝ) > 0,
      have : (m : ℝ) ≠ 0, intro m0, simp at m0, rw m0 at hm, exact h0.2 hm,
      exact abs_pos.2 this,
    rw (le_mul_iff_one_le_left this), simp, linarith,
  have habsn : (↑(abs n) : ℝ) ≤ p/2,
    suffices : (↑(abs n) : ℝ) ≤ (↑(abs r) : ℝ), simp at *, linarith,
    rw [hn, abs_mul], simp,
    have : abs (n : ℝ) > 0,
      have : (n : ℝ) ≠ 0, intro n0, simp at n0, rw n0 at hn, exact h0.1 hn,
      exact abs_pos.2 this,
    rw (le_mul_iff_one_le_left this), simp, linarith,
  simp at habsm, simp at habsn,
  exact simp_cal habsm habsn (show p ≥ 0, by linarith)
end

lemma dvd_imp_leq_nat {a m : ℕ} (h : a ∣ m) (hm : m ≠ 0) : a ≤ m :=
begin
  cases h with k hk,
  rw hk,
  suffices : k ≥ 1, have : a*1 ≤ a*k, from (mul_le_mul_left' this a), linarith,
  by_contradiction, push_neg at h, have : k = 0, by linarith,
  rw this at *, simp at *, exact hm hk
end

lemma prime_divisor_nat {a : ℕ} (ha : a ≥ 2) : ∃ p, (nat.prime p) ∧ p ∣ a :=
begin
  induction a using nat.strong_induction_on with a hi,
  dsimp at hi,
  cases em (nat.prime a) with hpri hpri,
  use a, split, exact hpri, simp,
  unfold nat.prime at hpri, push_neg at hpri,
  cases (hpri ha) with m hm,
  have : m < a,
    have : m ≤ a, from dvd_imp_leq_nat (hm.1) (by linarith),
    exact (ne.le_iff_lt hm.2.2).1 this,
  cases em (m = 0) with h0 h0, rw h0 at *, simp at *, exfalso, apply hm.2, symmetry, exact hm.1,
  have : m ≥ 2,
    rcases hm with ⟨h₀, h₁, h₂⟩,
    by_contradiction hf, push_neg at hf, interval_cases m,  
  cases (hi m (by linarith) (by linarith)) with p hpdvd, use p, split, exact hpdvd.1,
  exact dvd_trans hpdvd.2 hm.1,
  apply h0, refl, apply h₁, refl
end

lemma prime_divisor_int {a : ℤ} (ha: a ≥ 2) : ∃ p, (prime p) ∧ p ∣ a ∧ p > 0 :=
begin
  lift a to ℕ using (show a ≥ 0, by linarith), norm_cast at ha,
  rcases (prime_divisor_nat ha) with ⟨p, hp, pdvda⟩,
  use (p : ℤ), norm_cast,
  have ppos : p ≠ 0,
    intro hf, rw hf at hp, norm_num at hp,
  exact ⟨int_prime_eq_nat_prime.mp hp, pdvda, nat.prime.pos hp⟩
end

lemma prime_parity {p : ℕ} (hp : nat.prime p) : p = 2 ∨ odd p :=
begin
  by_cases p2 : p = 2,
  left, exact p2,
  right,
  have podd : ¬even p,
    intro hdvd, replace hdvd : 2 ∣ p, from even_iff_two_dvd.mp hdvd,
    cases (hp.2 2 hdvd) with hf hf,
    linarith, apply p2, rw hf,
  exact nat.odd_iff_not_even.mpr podd
end

lemma exists_prime_divisor
{a : ℕ} (leq : 2 ≤ a) : (∃ n : ℕ, a = 2 ^ n) ∨ ∃ p, nat.prime p ∧ p ∣ a ∧ odd p :=
begin
  induction a using nat.strong_induction_on with a hi, dsimp at hi,
  rcases (prime_divisor_nat leq) with ⟨p, hp, k, hk⟩,
  by_cases k2 : k < 2,
  { by_cases kval : k = 0, rw kval at hk, simp at hk, linarith,
    have knonneg : k > 0, exact pos_iff_ne_zero.mpr kval,replace kval : k = 1, by linarith,
    rw kval at hk, simp at hk, rw hk,
    cases (prime_parity hp) with p2 podd, 
    { left, use 1, rw p2, simp},
    { right, use p, exact ⟨hp, by simp, podd⟩} },
  push_neg at k2,
  have ka : k < a,
    have ka : k ≤ a, apply dvd_imp_leq_nat, use p, rw hk, ring, linarith,
    have : k ≠ a,
      intro hf, rw hf at hk,
      replace hf : p = 1,
        suffices : 1*a = p*a, from (mul_left_inj' (by linarith)).mp (eq.symm this),
        simp, exact hk,
      rw hf at hp, norm_num at hp,
    exact (ne.le_iff_lt this).mp ka,
  cases (hi k ka k2) with hn hq,
  cases hn with n hn,
  cases (prime_parity hp) with p2 podd,
  left, use (n + 1), rw [hk, hn, p2], ring_exp,
  right, use p, rw hk, exact ⟨hp, dvd.intro k rfl, podd⟩,
  rcases hq with ⟨q, hq, qdvd, qodd⟩, right, use q,
  rw hk, exact ⟨hq, dvd_mul_of_dvd_right qdvd p, qodd⟩
end

lemma sum_sq_zero {a b : ℤ} (h : a^2 + b^2 = 0) : a = 0 ∧ b = 0 :=
begin
  have hal : a^2 ≥ 0, from pow_two_nonneg a,
  have hbl : b^2 ≥ 0, from pow_two_nonneg b,
  have hau : a^2 ≤ a^2 + b^2, linarith,
  have hbu : b^2 ≤ a^2 + b^2, linarith,
  rw h at hau, rw h at hbu,
  split, suffices : a^2 = 0, exact pow_eq_zero this, interval_cases (a^2),
  suffices : b^2 = 0, exact pow_eq_zero this, interval_cases (b^2),
  all_goals{assumption}
end

lemma sub_descent_step {p : ℕ} (hp : nat.prime p) (ho : odd p) : 
(∃ a b : ℤ, ∃ n : ℕ, int.gcd a b = 1 ∧ (p : ℤ) * (2^n) = a^2 + b^2) → (∃ x y : ℤ, ↑p = x^2 + y^2) :=
begin
  rintros ⟨a, b, n, gcdab, hpdvd⟩,
  induction n with n hi generalizing a b,
  simp at hpdvd, exact ⟨a, b, hpdvd⟩,
  rw nat.succ_eq_add_one at hpdvd,
  have key : ∃ a b : ℤ, int.gcd a b = 1 ∧ ↑p*2^n = a^2 + b^2,
    have prime_two : prime (2 : ℤ), apply int_prime_eq_nat_prime.mp, norm_num,
    have two_dvd : 2 ∣ (p : ℤ)*2^(n+1), use (↑p*2^n), ring_exp,
    rcases (sum_of_sq_dvd_sum_of_sq ⟨a, b,
      gcd_eq_one_iff_coprime.mp gcdab, hpdvd⟩ ⟨prime_two, two_dvd⟩ ⟨1, 1, by norm_num⟩)
      with ⟨c, d, gcdcd, h⟩,
    use [c, d], split, exact gcd_eq_one_iff_coprime.mpr gcdcd,
    rw ←h, rw [pow_add, ←mul_assoc], simp,
    rw (int.mul_div_cancel (↑p * 2 ^ n) (show (2 : ℤ) ≠ 0, by linarith)),
  rcases key with ⟨c, d, gcdcd, h⟩, exact hi c d gcdcd h
end

theorem descent_step {p : ℤ} (hp : prime p) (ho : odd p) (ppos : p > 0) :
(∃ a b : ℤ, int.gcd a b = 1 ∧ p ∣ a^2 + b^2) → (∃ x y : ℤ, p = x^2 + y^2) :=
begin
  rintros ⟨a, b, gcdab, hpdvd⟩,
  lift p to ℕ using (show p ≥ 0, by linarith),
  induction p using nat.strong_induction_on with p hi generalizing a b, dsimp at hi,
  have : ∃ a b : ℤ, int.gcd a b = 1 ∧ (p : ℤ) ∣ a^2 + b^2,
    use a, use b, exact ⟨gcdab, hpdvd⟩,
  have hmn := (descent_wlog hp ho ppos this), clear this,
  rcases hmn with ⟨a', b', gcdab', hpdvd', ineq⟩,
  have hab : a'^2 + b'^2 > 0,
    have hab : a'^2 + b'^2 ≥ 0,
      have a_sq' := pow_two_nonneg a', have b_sq' := pow_two_nonneg b', linarith,
    have ab0 : a'^2 + b'^2 ≠ 0,
      intro hf, rw (int.gcd_eq_zero_iff.mpr (sum_sq_zero hf)) at gcdab', linarith,
    exact (ne.symm ab0).le_iff_lt.mp hab,
  obtain ⟨N, hN⟩ := hpdvd',
  have Nnonneg : N ≥ 0,
    by_contradiction hf, push_neg at hf,
    have habf : a'^2 + b'^2 < 0, rw hN, exact linarith.mul_neg hf ppos,
    linarith,
  lift N to ℕ using Nnonneg,
  induction N using nat.strong_induction_on with N hii generalizing a' b', dsimp at hii,
  by_cases Nval : N < 2,
  { replace Nval : N = 0 ∨ N = 1, by omega, cases Nval with Nval Nval;
    rw Nval at hN; simp at hN,
    rcases (sum_sq_zero hN) with ⟨rfl, rfl⟩, simp at gcdab', exfalso, exact gcdab',
    use a', use b', rw hN},
  push_neg at Nval,
  rcases (exists_prime_divisor Nval) with ⟨n, hn⟩ | ⟨q, hq, hqdvd, hqodd⟩,
  replace hp : nat.prime p, from int_prime_eq_nat_prime.mpr hp,
  simp at ho, replace ho : odd p, from nat.odd_iff_not_even.mpr ho,
  apply (sub_descent_step hp ho),
  use [a', b', n], exact ⟨gcdab', by {rw [hN, hn], simp}⟩,
  cases hqdvd with k hk, rw mul_comm at hk,
  have kle : k < N,
    have kleq := dvd_imp_leq_nat ⟨q, hk⟩ (show N ≠ 0, by linarith),
    have kneq : k ≠ N, intro hf, rw hf at hk, have equi : N*1 = N*q, simp, rw ←hk,
      have qvalue := (mul_right_inj' (show N ≠ 0, by linarith)).1 equi,
      rw ←qvalue at hq, norm_num at hq,
    exact (ne.le_iff_lt kneq).mp kleq,
  have key : ∃ (a b : ℤ), is_coprime a b ∧ a^2 + b^2 = ↑p*k,
    have qdvd : ↑q ∣ a'^2 + b'^2,
      use ↑p*k, rw [hN, hk], simp, ring,
    have qpos : (q : ℤ) > 0,
      have q0 : q ≠ 0,
        intro hf, rw hf at hk, simp at hk, rw hk at Nval, linarith,
        norm_cast, exact nat.prime.pos hq,
    have q_sq : ∃ a b : ℤ, (q : ℤ) = a^2 + b^2,
      have qle : q < p,
        have qdvd : (p : ℤ)*q ∣ a'^2 + b'^2,
          use k, rw [hN, hk], norm_cast, ring,
        have Npos : a'^2 + b'^2 > 0, from hab,
        have Nleq : (a'^2 + b'^2 : ℝ) ≤ (p^2/2 : ℝ), from ineq,
        zify, exact (largest_divisor qdvd ppos qpos Npos (by {simp, exact Nleq})),
      have hq' : prime ↑q, from int_prime_eq_nat_prime.mp hq,
      have hqodd' : odd (q : ℤ),
        simp, exact nat.odd_iff_not_even.mp hqodd,
      apply (hi q qle hq' hqodd' qpos a' b'),
      exact gcdab', rw [hN, hk], use ↑p*k, simp, ring,
    have key := sum_of_sq_dvd_sum_of_sq ⟨a', b',
      gcd_eq_one_iff_coprime.mp gcdab', show a'^2 + b'^2 = a'^2 + b'^2, by refl⟩
      ⟨int_prime_eq_nat_prime.mp hq, qdvd⟩ q_sq,
    rw [hN, hk] at key, rcases key with ⟨c, d, gcdcd, eq⟩, use [c, d], split,
    exact gcdcd, rw ←eq,
    simp, rw ←mul_assoc, exact ((p : ℤ) * ↑k).mul_div_cancel (by linarith),
  rcases key with ⟨c, d, gcdcd, cd_sq⟩,
  rw ←gcd_eq_one_iff_coprime at gcdcd,
  have sumineq : (c^2 : ℝ) + ↑d^2 ≤ a'^2 + b'^2,
    norm_cast, rw [cd_sq, hN],
    exact (mul_le_mul_left (ppos)).mpr (by linarith),
  have pos : c^2 + d^2 > 0,
    have nonneg : c^2 + d^2 ≥ 0,
      have := pow_two_nonneg c, have := pow_two_nonneg d, linarith,
    have nonzero : c^2 + d^2 ≠ 0,
      intro hf, rw (int.gcd_eq_zero_iff.mpr (sum_sq_zero hf)) at gcdcd, linarith,
    exact (ne.symm nonzero).le_iff_lt.mp nonneg,
  simp at ineq, exact hii k kle c d gcdcd (by linarith) pos cd_sq
end
