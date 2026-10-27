module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddAutSylow
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Kernel
import CFSG.Permutation.SylowTwoNormalizer.Sym

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup
open CFSG.ComponentClassification.AS81.Sec2 (conjSetStab conjPermHom)

theorem normSylowAt_of_pPow {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (h : ∀ S : Subgroup X, CFSG.ABGLocalTools.IsSylowOf 2 S ⊤ → ∀ y ∈ normalizer (S : Set X),
      (∃ j : ℕ, y ^ p ^ j = 1) → y ^ p ∈ centralizer (S : Set X) →
        y ∈ centralizer (S : Set X)) :
    NormSylowAt X p := by
  intro S hS y hyN hyp
  obtain ⟨a, m, hndvd, hm⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y).ne' p hp.ne_one
  have hm0 : m ≠ 0 := fun h0 => hndvd (h0.symm ▸ dvd_zero p)
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  set y' : X := y ^ m with hy'def
  have hdvd : m ∣ orderOf y := ⟨p ^ a, by rw [hm, Nat.mul_comm]⟩
  have hga : orderOf y' = p ^ a := by
    rw [hy'def, orderOf_pow_of_dvd hm0 hdvd, hm, Nat.mul_comm (p ^ a) m]
    exact Nat.mul_div_right (p ^ a) hmpos
  have hpow : y' ^ p ^ a = 1 := by
    have h1 := pow_orderOf_eq_one y'
    rwa [hga] at h1
  have hy'N : y' ∈ normalizer (S : Set X) := pow_mem hyN m
  have hy'p : y' ^ p = (y ^ p) ^ m := by
    rw [hy'def, ← pow_mul, Nat.mul_comm, pow_mul]
  have hy'C : y' ∈ centralizer (S : Set X) :=
    h S hS y' hy'N ⟨a, hpow⟩ (by rw [hy'p]; exact pow_mem hyp m)
  have hcop : Nat.Coprime m p := (hp.coprime_iff_not_dvd.mpr hndvd).symm
  have hu : ((m : ℕ) : ℤ) * (Nat.gcdA m p : ℤ) +
      (p : ℤ) * (Nat.gcdB m p : ℤ) = 1 := by
    have h1 := Nat.gcd_eq_gcd_ab m p
    rw [hcop.gcd_eq_one, Nat.cast_one] at h1
    exact h1.symm
  have h1 : y' ^ (Nat.gcdA m p : ℤ) =
      y ^ (((m : ℕ) : ℤ) * (Nat.gcdA m p : ℤ)) := by
    rw [hy'def, ← zpow_natCast,
      (zpow_mul y ((m : ℕ) : ℤ) (Nat.gcdA m p : ℤ)).symm]
  have h2 : (y ^ p) ^ (Nat.gcdB m p : ℤ) =
      y ^ ((p : ℤ) * (Nat.gcdB m p : ℤ)) := by
    rw [← zpow_natCast, (zpow_mul y (p : ℤ) (Nat.gcdB m p : ℤ)).symm]
  have hy : y = y' ^ (Nat.gcdA m p : ℤ) * (y ^ p) ^ (Nat.gcdB m p : ℤ) := by
    rw [h1, h2, ← zpow_add, hu, zpow_one]
  rw [hy]
  exact mul_mem (zpow_mem hy'C _) (zpow_mem hyp _)

theorem mem_normalizer_of_conjSetStab_quot {X : Type} [Group X] [Finite X]
    {Δ : Set (Subgroup X)} (S : Sylow 2 X) (hS : (S : Subgroup X) ≤ conjSetStab Δ)
    {α : Type} [Finite α] (N : Subgroup (conjPermHom (le_refl (conjSetStab Δ))).range)
    [N.Normal] (hN : IsPGroup 2 N)
    (e : (conjPermHom (le_refl (conjSetStab Δ))).range ⧸ N ≃* Equiv.Perm α)
    {y : X} (hyΔ : y ∈ conjSetStab Δ) (hyS : y ∈ normalizer ((S : Subgroup X) : Set X))
    (hy : Odd (orderOf y)) : ∀ J ∈ Δ, y ∈ normalizer (J : Set X) := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ρ : ↥(conjSetStab Δ) →* Equiv.Perm ↥Δ := conjPermHom (le_refl (conjSetStab Δ))
  let φ : ↥(conjSetStab Δ) →* ρ.range := ρ.rangeRestrict
  let ψ : ↥(conjSetStab Δ) →* Equiv.Perm α :=
    e.toMonoidHom.comp ((QuotientGroup.mk' N).comp φ)
  have hψ : Function.Surjective ψ :=
    e.surjective.comp ((QuotientGroup.mk'_surjective N).comp ρ.rangeRestrict_surjective)
  let S' : Sylow 2 ↥(conjSetStab Δ) := S.subtype hS
  let R : Sylow 2 (Equiv.Perm α) := S'.mapSurjective (f := ψ) hψ
  let ty : ↥(conjSetStab Δ) := ⟨y, hyΔ⟩
  have hS'coe : (S' : Subgroup ↥(conjSetStab Δ)) =
      (S : Subgroup X).subgroupOf (conjSetStab Δ) := Sylow.coe_subtype S hS
  have htyN : ty ∈ normalizer (S' : Set ↥(conjSetStab Δ)) := by
    have hset : (S' : Set ↥(conjSetStab Δ)) =
        (((S : Subgroup X).subgroupOf (conjSetStab Δ) : Subgroup ↥(conjSetStab Δ)) :
          Set ↥(conjSetStab Δ)) :=
      congrArg (fun H : Subgroup ↥(conjSetStab Δ) => (H : Set ↥(conjSetStab Δ))) hS'coe
    rw [hset, Subgroup.mem_normalizer_iff]
    intro s
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    constructor
    · intro hs
      have h := (Subgroup.mem_normalizer_iff.mp hyS (s : X)).mp hs
      simpa [ty] using h
    · intro hs
      have h : y * (s : X) * y⁻¹ ∈ (S : Subgroup X) := by simpa [ty] using hs
      exact (Subgroup.mem_normalizer_iff.mp hyS (s : X)).mpr h
  have hτN : ψ ty ∈ normalizer (R : Set (Equiv.Perm α)) := by
    have hRcoe : (R : Subgroup (Equiv.Perm α)) = (S' : Subgroup ↥(conjSetStab Δ)).map ψ :=
      Sylow.coe_mapSurjective hψ S'
    have hset : (R : Set (Equiv.Perm α)) =
        (((S' : Subgroup ↥(conjSetStab Δ)).map ψ : Subgroup (Equiv.Perm α)) :
          Set (Equiv.Perm α)) :=
      congrArg (fun H : Subgroup (Equiv.Perm α) => (H : Set (Equiv.Perm α))) hRcoe
    rw [hset]
    exact Subgroup.le_normalizer_map ψ (Subgroup.mem_map_of_mem ψ htyN)
  have hτodd : Odd (orderOf (ψ ty)) := by
    have h1 : orderOf (ψ ty) ∣ orderOf ty := orderOf_map_dvd ψ ty
    have h2 : orderOf ty = orderOf y := Subgroup.orderOf_mk y hyΔ
    rw [h2] at h1
    exact Odd.of_dvd_nat hy h1
  have hτ1 : ψ ty = 1 :=
    CFSG.Permutation.SylowTwoNormalizer.eq_one_of_mem_normalizer R.isPGroup' R.not_dvd_index
      hτodd hτN
  have hquot1 : (QuotientGroup.mk' N) (φ ty) = 1 := by
    apply e.injective
    simpa [ψ] using hτ1
  have hφN : φ ty ∈ N := (QuotientGroup.eq_one_iff (φ ty)).mp hquot1
  have hdvdφ : orderOf (φ ty) ∣ orderOf y := by
    have h1 := orderOf_map_dvd ρ.rangeRestrict ty
    rwa [Subgroup.orderOf_mk y hyΔ] at h1
  have hcop : Nat.Coprime (orderOf (φ ty)) (orderOf y) := by
    have h := hN.orderOf_coprime (Nat.coprime_two_left.mpr hy) ⟨φ ty, hφN⟩
    rwa [Subgroup.orderOf_mk] at h
  have hφ1 : φ ty = 1 := by
    exact orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd hdvdφ)
  have hρ1 : ρ ty = 1 := by
    have h := congrArg Subtype.val hφ1
    simpa [φ] using h
  exact (CFSG.ComponentClassification.AS81.Sec2.conjPermHom_eq_one_iff
    (le_refl (conjSetStab Δ)) ty).mp hρ1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
