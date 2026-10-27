module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixKInv
public import CFSG.LocalAnalysis.SteinbergSFSingleCommModel3Bridge
public import CFSG.LocalAnalysis.SteinbergSFSingleCommModel3Use
public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixKInvol
public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixKRank
public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixKConj
public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixKCent

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

section Steps

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {K : Type} [Field K]
  [CharP K 2] [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G} {i : Axis}

theorem sixK_k10_conj_S (hH : SixHConclusion φ t i) (htT : t ∈ Tplus φ t i) :
    ∀ x ∈ S φ t i, t * x * t⁻¹ ∈ S φ t i := by
  have hconj_Mhat : ∀ k : Axis, ∀ x ∈ Mhat φ t i k, t * x * t⁻¹ ∈ Mhat φ t i k := by
    intro k x hx
    have hxT : x ∈ Tplus φ t i := (hH.normal_Mhat k).1 hx
    have hmem : (⟨x, hxT⟩ : ↥(Tplus φ t i)) ∈ (Mhat φ t i k).subgroupOf (Tplus φ t i) :=
      Subgroup.mem_subgroupOf.mpr hx
    have h := (hH.normal_Mhat k).2.1.conj_mem _ hmem ⟨t, htT⟩
    exact Subgroup.mem_subgroupOf.mp h
  intro x hx
  exact RootAxisTwoCore.conj_mem_sup (H₁ := Mhat φ t i Axis.one) (H₂ := Mhat φ t i Axis.two)
    (hconj_Mhat Axis.one) (hconj_Mhat Axis.two) hx

theorem sixK_k10_zpowers_le_normalizer (hH : SixHConclusion φ t i) (htt : t * t = 1)
    (htT : t ∈ Tplus φ t i) :
    Subgroup.zpowers t ≤ normalizer ((S φ t i : Subgroup G) : Set G) := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hconj := sixK_k10_conj_S hH htT
  have htn : t ∈ normalizer ((S φ t i : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hconj h hh, fun hh => ?_⟩
    have h' := hconj (t * h * t⁻¹) hh
    have heq : t * (t * h * t⁻¹) * t⁻¹ = h := by
      rw [htinv]
      calc t * (t * h * t) * t = (t * t) * h * (t * t) := by group
        _ = h := by simp [htt]
    rw [heq] at h'
    exact h'
  exact Subgroup.zpowers_le.mpr htn

theorem sixK_k10 (hS : SCSetting L K n φ t i) (hH : SixHConclusion φ t i)
    (k3 : K3Concl φ t i) (k9 : K9Concl φ t i) : ∀ g : G, g⁻¹ * t * g ∈ Tplus φ t i → ∃ s ∈ S φ t i, g⁻¹ * t * g = s⁻¹ * t * s := by
  have ht2 : orderOf t = 2 := hS.fc.setup.order_t
  have htt : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht2, pow_two] at h
    exact h
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have htT : t ∈ Tplus φ t i := by
    rw [← hH.sup_t]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hconj_S := sixK_k10_conj_S hH htT
  have hnorm := sixK_k10_zpowers_le_normalizer hH htt htT
  intro g hg
  have hu : g⁻¹ * t * g ∈ ((S φ t i ⊔ Subgroup.zpowers t : Subgroup G) : Set G) := by
    rw [SetLike.mem_coe, hH.sup_t]
    exact hg
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm] at hu
  obtain ⟨s, hs, z, hz, hsz⟩ := Set.mem_mul.mp hu
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (SetLike.mem_coe.mp hz)
  have hmod : t ^ (m % 2) = t ^ m := by
    have h := zpow_mod_orderOf t m
    rw [ht2] at h
    exact_mod_cast h
  have hm : t ^ m = 1 ∨ t ^ m = t := by
    rcases Int.emod_two_eq_zero_or_one m with h0 | h1
    · left
      rw [← hmod, h0, zpow_zero]
    · right
      rw [← hmod, h1, zpow_one]
  rcases hm with hm | hm
  · exfalso
    rw [hm, mul_one] at hsz
    exact k9 g (by rw [← hsz]; exact SetLike.mem_coe.mp hs)
  · rw [hm] at hsz
    have hxS : t * s * t⁻¹ ∈ S φ t i := hconj_S s (SetLike.mem_coe.mp hs)
    have hkey : t * (t * s * t⁻¹) = g⁻¹ * t * g := by
      rw [← hsz, htinv]
      calc t * (t * s * t) = (t * t) * s * t := by simp only [mul_assoc]
        _ = s * t := by rw [htt, one_mul]
    have hsq : g⁻¹ * t * g * (g⁻¹ * t * g) = 1 := by
      calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
        _ = 1 := by rw [htt]; simp
    obtain ⟨s', hs', hs'eq⟩ := k3 (t * s * t⁻¹) hxS (by rw [hkey]; exact hsq)
    exact ⟨s', hs', (hs'eq.trans hkey).symm⟩

end Steps

theorem six_K
    (hSel : CFSG.LocalAnalysis.EvenBN.GMSK.FixedRootSelector fun D _ => CFSG.Blueprint.Catalog D) :
    SixKStatement := by
  intro G _ _ _ L K _ _ _ n φ t i hS hH hE
  have k1 := sixK_k1 hS hH
  have k2 := sixK_k2 hS hH
  have k3 := sixK_k3 hS hH hE k1 k2
  have k4a := sixK_k4a_of_model3 hS hH (sc_model3_sub hSel hS)
  have k4b := sixK_k4b hH
  have k4 := sixK_k4 hS hH hE k4a k4b
  have k5 := sixK_k5 hS
  have k6 := sixK_k6 hS
  have k7 := sixK_k7 hS hH k6
  have k8 := sixK_k8 hS hH k5
  have k9 := sixK_k9 hS hH hE k4 k7 k8
  have k10 := sixK_k10 hS hH k3 k9
  have k11 := sixK_k11 hS hH hE
  exact ⟨k10, k11, sixK_k12 hH k11⟩

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
