module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.WeakClosure81.A6Case

theorem commute_mul_conj_of_pow_three {G : Type*} [Group G] {x y : G} (hx : x ^ 3 = 1)
    (hy : y ^ 3 = 1) (hyx : (y * x⁻¹) ^ 3 = 1) :
    Commute (x * y) (x * (x * y) * x⁻¹) := by
  have hx2 : x⁻¹ = x * x := by
    rw [← mul_eq_one_iff_inv_eq]
    simpa [pow_succ, pow_two, mul_assoc] using hx
  have hy2 : y⁻¹ = y * y := by
    rw [← mul_eq_one_iff_inv_eq]
    simpa [pow_succ, pow_two, mul_assoc] using hy
  have hxA : x * (x * y) * x⁻¹ = x⁻¹ * y * x⁻¹ := by
    rw [hx2]
    group
  have hyx3 : y * x⁻¹ * y * x⁻¹ * y = x := by
    have h : y * x⁻¹ * y * x⁻¹ * y * x⁻¹ = 1 := by
      simpa [pow_succ, pow_two, mul_assoc] using hyx
    calc y * x⁻¹ * y * x⁻¹ * y = y * x⁻¹ * y * x⁻¹ * y * x⁻¹ * x := by group
      _ = 1 * x := by rw [h]
      _ = x := one_mul x
  have h2 : (x * y) * (x⁻¹ * y * x⁻¹) * (y * x) = 1 := by
    calc (x * y) * (x⁻¹ * y * x⁻¹) * (y * x)
        = x * (y * x⁻¹ * y * x⁻¹ * y) * x := by group
      _ = x * x * x := by rw [hyx3]
      _ = 1 := by simpa [pow_succ, pow_two, mul_assoc] using hx
  have h1 : (x⁻¹ * y * x⁻¹) * (x * y) = x⁻¹ * y⁻¹ := by
    rw [hy2]
    group
  have h3 : (x * y) * (x⁻¹ * y * x⁻¹) = x⁻¹ * y⁻¹ := by
    have h := (mul_eq_one_iff_eq_inv.mp h2 : (x * y) * (x⁻¹ * y * x⁻¹) = (y * x)⁻¹)
    rw [h, mul_inv_rev]
  show (x * y) * (x * (x * y) * x⁻¹) = (x * (x * y) * x⁻¹) * (x * y)
  rw [hxA, h3, h1]

private theorem pow_ker_sq_pow_three_eq_one {K : Type*} [Group K] [Finite K] {J : Subgroup K}
    {c : K} (hc : c ^ 3 ∈ J) : (c ^ (Nat.card J) ^ 2) ^ 3 = 1 := by
  have hdvd : orderOf (c ^ 3) ∣ (Nat.card J) ^ 2 := by
    have h := orderOf_dvd_natCard (⟨c ^ 3, hc⟩ : J)
    rw [Subgroup.orderOf_mk] at h
    refine h.trans ?_
    rw [pow_two]
    exact dvd_mul_right _ _
  rw [← pow_mul, Nat.mul_comm, pow_mul]
  exact orderOf_dvd_iff_pow_eq_one.mp hdvd

private theorem pow_card_sq_mod_three {K : Type*} [Group K] [Finite K] {J : Subgroup K}
    (hJ : IsPGroup 2 J) : (Nat.card J) ^ 2 % 3 = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hJ
  rw [hn]
  have h1 : (2 ^ n) ^ 2 ≡ ((2 : ℕ) ^ 2) ^ n [MOD 3] := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
  have h2 := (show (2 : ℕ) ^ 2 ≡ 1 [MOD 3] by decide).pow n
  rw [one_pow] at h2
  simpa [Nat.ModEq] using h1.trans h2

private theorem map_pow_card_ker {K Q : Type*} [Group K] [Finite K] [Group Q]
    (ψ : K →* Q) (hker : IsPGroup 2 ψ.ker) {c : K} (hc : ψ c ^ 3 = 1) :
    ψ (c ^ (Nat.card ψ.ker) ^ 2) = ψ c := by
  have hm3 : (Nat.card ψ.ker) ^ 2 % 3 = 1 := pow_card_sq_mod_three hker
  have hmk : (Nat.card ψ.ker) ^ 2 = 3 * ((Nat.card ψ.ker) ^ 2 / 3) + 1 := by
    have := Nat.div_add_mod ((Nat.card ψ.ker) ^ 2) 3
    omega
  calc ψ (c ^ (Nat.card ψ.ker) ^ 2) = (ψ c) ^ (Nat.card ψ.ker) ^ 2 := map_pow ψ c _
    _ = ψ c := by
        conv_lhs => rw [hmk]
        rw [pow_add, pow_one, pow_mul, hc, one_pow, one_mul]

private theorem commute_pow_card_ker {K Q : Type*} [Group K] [Finite K] [Group Q]
    (ψ : K →* Q) (hker : IsPGroup 2 ψ.ker) {ρ c : K} (hc : ψ c ^ 3 = 1)
    (hcc : Commute c (ρ * c * ρ⁻¹)) (hcomm : Commute (ψ ρ) (ψ c)) :
    Commute ρ (c ^ (Nat.card ψ.ker) ^ 2) := by
  have hc3 : c ^ 3 ∈ ψ.ker := by rw [MonoidHom.mem_ker, map_pow, hc]
  have hcm3 : (c ^ (Nat.card ψ.ker) ^ 2) ^ 3 = 1 := pow_ker_sq_pow_three_eq_one hc3
  have hconjpow : (ρ * c * ρ⁻¹) ^ (Nat.card ψ.ker) ^ 2 =
      ρ * c ^ (Nat.card ψ.ker) ^ 2 * ρ⁻¹ := by
    rw [← MulAut.conj_apply ρ c, ← map_pow, MulAut.conj_apply]
  have hconj3 : (ρ * c ^ (Nat.card ψ.ker) ^ 2 * ρ⁻¹) ^ 3 = 1 := by
    rw [← MulAut.conj_apply ρ (c ^ (Nat.card ψ.ker) ^ 2), ← map_pow, hcm3, map_one]
  have hconjcomm : Commute (ρ * c ^ (Nat.card ψ.ker) ^ 2 * ρ⁻¹) (c ^ (Nat.card ψ.ker) ^ 2) := by
    have h := (hcc.pow_left ((Nat.card ψ.ker) ^ 2)).pow_right ((Nat.card ψ.ker) ^ 2)
    rw [hconjpow] at h
    exact h.symm
  set u : K := (ρ * c ^ (Nat.card ψ.ker) ^ 2 * ρ⁻¹) * (c ^ (Nat.card ψ.ker) ^ 2)⁻¹ with hu
  have hu3 : u ^ 3 = 1 := by
    rw [hu, hconjcomm.inv_right.mul_pow 3, hconj3, inv_pow, hcm3, inv_one, mul_one]
  have hψu : ψ u = 1 := by
    have hconjψ : ψ (ρ * c ^ (Nat.card ψ.ker) ^ 2 * ρ⁻¹) =
        ψ (c ^ (Nat.card ψ.ker) ^ 2) := by
      rw [map_mul, map_mul, map_inv, map_pow]
      rw [(hcomm.pow_right ((Nat.card ψ.ker) ^ 2)).eq, mul_assoc, mul_inv_cancel, mul_one]
    rw [hu, map_mul, map_inv, hconjψ, mul_inv_cancel]
  have humem : u ∈ ψ.ker := MonoidHom.mem_ker.mpr hψu
  have hcop : (orderOf (⟨u, humem⟩ : ψ.ker)).Coprime 3 :=
    hker.orderOf_coprime (by norm_num) ⟨u, humem⟩
  rw [Subgroup.orderOf_mk] at hcop
  have hu1 : u = 1 :=
    orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd (orderOf_dvd_of_pow_eq_one hu3))
  have hconj_eq : ρ * c ^ (Nat.card ψ.ker) ^ 2 * ρ⁻¹ = c ^ (Nat.card ψ.ker) ^ 2 := by
    have h := hu1
    rw [hu] at h
    simpa using (mul_inv_eq_iff_eq_mul.mp h)
  show ρ * c ^ (Nat.card ψ.ker) ^ 2 = c ^ (Nat.card ψ.ker) ^ 2 * ρ
  have h := congrArg (· * ρ) hconj_eq
  simpa [mul_assoc] using h

theorem commute_pow_card_ker_of_commute_conj {K Q : Type*} [Group K] [Finite K] [Group Q]
    (ψ : K →* Q) (hker : IsPGroup 2 ψ.ker) {ρ c : K} (hc : ψ c ^ 3 = 1)
    (hcc : Commute c (ρ * c * ρ⁻¹)) (hcomm : Commute (ψ ρ) (ψ c)) :
    Commute ρ (c ^ (Nat.card ψ.ker) ^ 2) ∧ (c ^ (Nat.card ψ.ker) ^ 2) ^ 3 = 1 ∧
      ψ (c ^ (Nat.card ψ.ker) ^ 2) = ψ c := by
  have hc3 : c ^ 3 ∈ ψ.ker := by rw [MonoidHom.mem_ker, map_pow, hc]
  exact ⟨commute_pow_card_ker ψ hker hc hcc hcomm, pow_ker_sq_pow_three_eq_one hc3,
    map_pow_card_ker ψ hker hc⟩

end CFSG.LocalAnalysis.WeakClosure81.A6Case
