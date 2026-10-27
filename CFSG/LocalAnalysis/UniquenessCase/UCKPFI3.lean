module

public import CFSG.LocalAnalysis.UniquenessCase.UCKPFI2
public import CFSG.LocalAnalysis.UniquenessCase.UCKP1
public import CFSG.LocalAnalysis.UniquenessCase.UCKP3Abs
public import CFSG.LocalAnalysis.UniquenessCase.UCKPCenter

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem prime_dvd_two_pow_sub_one_odd {s r : ℕ} (hs : Odd s) (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1) :
    3 ≤ r ∧ r ≠ 3 := by
  obtain ⟨t, rfl⟩ := hs
  have h2 : 2 ^ (2 * t + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have h2' : 2 ^ (2 * t + 1) % 2 = 0 := by
    rw [pow_succ]
    simp
  have hpos : 1 ≤ 2 ^ (2 * t + 1) := Nat.one_le_two_pow
  have hr2 := hr.two_le
  generalize 2 ^ (2 * t + 1) = N at h2 h2' hpos hrs
  have hne2 : r ≠ 2 := by
    rintro rfl
    have := Nat.mod_eq_zero_of_dvd hrs
    omega
  have hne3 : r ≠ 3 := by
    rintro rfl
    have := Nat.mod_eq_zero_of_dvd hrs
    omega
  exact ⟨by omega, hne3⟩

theorem two_pow_mod_eq_one {s n r : ℕ} (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1) (hsn : s ∣ n) :
    2 ^ n % r = 1 := by
  obtain ⟨m, rfl⟩ := hsn
  have h1 : 1 ≤ 2 ^ s := Nat.one_le_two_pow
  have h2 : 2 ^ s ≡ 1 [MOD r] := ((Nat.modEq_iff_dvd' h1).2 hrs).symm
  have h3 : (2 ^ s) ^ m ≡ 1 ^ m [MOD r] := h2.pow m
  rw [one_pow] at h3
  rw [pow_mul]
  have : (2 ^ s) ^ m % r = 1 % r := h3
  rw [this]
  exact Nat.one_mod_eq_one.2 hr.one_lt.ne'

theorem exists_inner_gen_pow_eq_one {X : Type*} [Group X] (hZ3 : ∀ z ∈ center X, z ^ 3 = 1) {r : ℕ}
    (hr : 1 < r) (hcop : Nat.Coprime 3 r) {α : MulAut X} (hαr : α ^ r = 1)
    (hα : α ∈ (MulAut.conj : X →* MulAut X).range) :
    ∃ x : X, MulAut.conj x = α ∧ x ^ r = 1 := by
  obtain ⟨x, hx⟩ := hα
  obtain ⟨t, -, ht⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hr
  have hxr : x ^ r ∈ center X := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : (MulAut.conj x) ^ r = 1 := by rw [hx]; exact hαr
    have h2 : ((MulAut.conj x) ^ r) g = g := by rw [h1]; rfl
    rw [← map_pow, MulAut.conj_apply] at h2
    calc g * x ^ r = (x ^ r * g * (x ^ r)⁻¹) * x ^ r := by rw [h2]
      _ = x ^ r * g := by group
  refine ⟨x ^ (3 * t), ?_, ?_⟩
  · rw [map_pow, hx]
    calc α ^ (3 * t) = α ^ (r * (3 * t / r) + 3 * t % r) := by rw [Nat.div_add_mod]
      _ = α := by rw [pow_add, pow_mul, hαr, one_pow, one_mul, ht, pow_one]
  · rw [← pow_mul, mul_comm (3 * t) r, pow_mul, pow_mul, hZ3 _ hxr, one_pow]

theorem exists_prime_order_lift {X : Type*} [Group X] (hZ3 : ∀ z ∈ center X, z ^ 3 = 1) {q : ℕ}
    (hq : q.Prime) (hq3 : 3 < q) {zb : X ⧸ center X} (hzb : orderOf zb = q) :
    ∃ z : X, orderOf z = q ∧ (QuotientGroup.mk z : X ⧸ center X) = zb := by
  obtain ⟨z₀, rfl⟩ := QuotientGroup.mk_surjective zb
  haveI : Fact q.Prime := ⟨hq⟩
  have hz₀q : z₀ ^ q ∈ center X := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hzb]
    exact pow_orderOf_eq_one _
  have hcop : Nat.Coprime 3 q := (Nat.coprime_primes Nat.prime_three hq).2 (by omega)
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hq.one_lt
  have himg : (QuotientGroup.mk (z₀ ^ (3 * u)) : X ⧸ center X) = QuotientGroup.mk z₀ := by
    rw [QuotientGroup.mk_pow, ← pow_mod_orderOf, hzb, hu, pow_one]
  have hpow : (z₀ ^ (3 * u)) ^ q = 1 := by
    rw [← pow_mul, mul_comm (3 * u) q, pow_mul, pow_mul, hZ3 _ hz₀q, one_pow]
  have hne : z₀ ^ (3 * u) ≠ 1 := by
    intro h
    have h1 : (QuotientGroup.mk (z₀ ^ (3 * u)) : X ⧸ center X) = 1 := by rw [h, QuotientGroup.mk_one]
    rw [himg] at h1
    have : orderOf (QuotientGroup.mk z₀ : X ⧸ center X) = 1 := orderOf_eq_one_iff.2 h1
    rw [hzb] at this
    exact hq.one_lt.ne' this
  exact ⟨z₀ ^ (3 * u), orderOf_eq_prime hpow hne, himg⟩

theorem conj_eq_of_commute_mod_center {X : Type*} [Group X] (hZ3 : ∀ z ∈ center X, z ^ 3 = 1) {q : ℕ}
    (hq : q.Prime) (hq3 : 3 < q) {x z : X} (hzq : z ^ q = 1)
    (hcomm : (QuotientGroup.mk z : X ⧸ center X) * QuotientGroup.mk x =
      QuotientGroup.mk x * QuotientGroup.mk z) : x * z * x⁻¹ = z := by
  have hc : x * z * x⁻¹ * z⁻¹ ∈ center X := by
    rw [← QuotientGroup.eq_one_iff]
    have h1 : (QuotientGroup.mk x : X ⧸ center X) * QuotientGroup.mk z * (QuotientGroup.mk x)⁻¹ *
        (QuotientGroup.mk z)⁻¹ = 1 := by
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul, hcomm]
    simpa only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] using h1
  have hxz : x * z * x⁻¹ = (x * z * x⁻¹ * z⁻¹) * z := by group
  have hcz : Commute (x * z * x⁻¹ * z⁻¹) z := (Subgroup.mem_center_iff.1 hc z).symm
  have hcq : (x * z * x⁻¹ * z⁻¹) ^ q = 1 := by
    have h1 : ((x * z * x⁻¹ * z⁻¹) * z) ^ q = 1 := by
      rw [← hxz, conj_pow, hzq]
      group
    rwa [hcz.mul_pow, hzq, mul_one] at h1
  have hcop : Nat.Coprime 3 q := (Nat.coprime_primes Nat.prime_three hq).2 (by omega)
  have h3 := hZ3 _ hc
  have hdiv : orderOf (x * z * x⁻¹ * z⁻¹) ∣ Nat.gcd 3 q :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one hcq)
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at hdiv
  rw [hxz, hdiv, one_mul]

theorem u3FixInner_of (hCen : U3Center) : U3FixInner := by
  intro X _ _ n hX s hs hsn r hr hrs α hαr hα q hq hq3 hqn
  have hn2 : 2 ≤ n := u3Range X n hX
  have hZ : Nat.card (center X) ∣ 3 := hCen X n hX
  have hZ3 : ∀ z ∈ center X, z ^ 3 = 1 := fun z hz => pow_three_eq_one_of_mem_center hZ hz
  obtain ⟨hr3, hr3'⟩ := prime_dvd_two_pow_sub_one_odd hs hr hrs
  have hrq : 2 ^ n % r = 1 := two_pow_mod_eq_one hr hrs hsn
  have hcop : Nat.Coprime 3 r := (Nat.coprime_primes Nat.prime_three hr).2 (Ne.symm hr3')
  obtain ⟨x, hx, hxr⟩ := exists_inner_gen_pow_eq_one hZ3 hr.one_lt hcop hαr hα
  have hxbar : (QuotientGroup.mk x : X ⧸ center X) ^ r = 1 := by
    rw [← QuotientGroup.mk_pow, hxr, QuotientGroup.mk_one]
  obtain ⟨zb, hzb, hzbx⟩ := fixed_inner_of_isU3 hn2 hX.2 hr hr3 hrq hxbar hq hq3 hqn
  obtain ⟨z, hz, hzmk⟩ := exists_prime_order_lift hZ3 hq hq3 hzb
  refine ⟨z, hz, ?_⟩
  have hzq : z ^ q = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  rw [← hx, MulAut.conj_apply]
  exact conj_eq_of_commute_mod_center hZ3 hq hq3 hzq (by rw [hzmk]; exact hzbx)

theorem u3FixInner_of_griess (hG : CFSG.Open.GriessAllModelsStatement) : U3FixInner :=
  u3FixInner_of (u3Center_of_griess hG)

end CFSG.LocalAnalysis.UniquenessCase.UCK
