module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rg
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
public import CFSG.GroupTheory.CartanComplement
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoSyl
public import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem oinf_le_normalizer_inf_sylow {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M) :
    OInf L ≤ Subgroup.normalizer ((D.T ⊓ L : Subgroup G) : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq := hL.2.2
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ L) L :=
    uc22p22r_fo_sylow_inf D.sylowM hL.1
  have hO2 : pCoreOf 2 L ≤ D.T ⊓ L := s16c7_pCoreOf_le_of_isSylowOf hTsyl
  have key : ∀ a ∈ OInf L, ∀ b ∈ L, a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 L := by
    intro a ha b hb
    have haL : a ∈ L := Subgroup.map_subtype_le _ ha
    obtain ⟨y, hy, hya⟩ := Subgroup.mem_map.mp ha
    have haeq : (⟨a, haL⟩ : ↥L) = y := Subtype.ext hya.symm
    have hcen : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ⟨a, haL⟩ ∈
        Subgroup.center (Bar2 L) := by
      rw [← uc22p21k_map_solvableRadical_eq_center hq, haeq]
      exact Subgroup.mem_map_of_mem _ hy
    have hmemL : a * b * a⁻¹ * b⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem (L.mul_mem haL hb) (L.inv_mem haL)) (L.inv_mem hb)
    have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
        (⟨a * b * a⁻¹ * b⁻¹, hmemL⟩ : ↥L) = 1 := by
      have hcomm : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ⟨b, hb⟩ *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ⟨a, haL⟩ =
          (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ⟨a, haL⟩ *
            (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ⟨b, hb⟩ :=
        Subgroup.mem_center_iff.1 hcen _
      have helem : (⟨a * b * a⁻¹ * b⁻¹, hmemL⟩ : ↥L) =
          (⟨a, haL⟩ : ↥L) * ⟨b, hb⟩ * (⟨a, haL⟩ : ↥L)⁻¹ * (⟨b, hb⟩ : ↥L)⁻¹ := rfl
      rw [helem, map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm]
      group
    have hmem : (⟨a * b * a⁻¹ * b⁻¹, hmemL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L :=
      (QuotientGroup.eq_one_iff _).mp h1
    exact (CFSG.mem_openPCoreOf_iff (⟨a * b * a⁻¹ * b⁻¹, hmemL⟩ : ↥L)).2 hmem
  intro z hz
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    have hwT : w ∈ D.T ⊓ L := hw
    have h1 : z * w * z⁻¹ = (z * w * z⁻¹ * w⁻¹) * w := by group
    rw [h1]
    exact (D.T ⊓ L).mul_mem (hO2 (key z hz w hwT.2)) hwT
  · intro hw
    have hz' : z⁻¹ ∈ OInf L := (OInf L).inv_mem hz
    have h2 := key z⁻¹ hz' (z * w * z⁻¹) hw.2
    have h3 : z⁻¹ * (z * w * z⁻¹) * (z⁻¹)⁻¹ = w := by group
    rw [h3] at h2
    have h4 : w = (w * (z * w * z⁻¹)⁻¹) * (z * w * z⁻¹) := by group
    rw [h4]
    exact (D.T ⊓ L).mul_mem (hO2 h2) hw

theorem exists_cIsCartanOf {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M) :
    ∃ C : Subgroup G, CIsCartanOf D.T L C := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T0 : Subgroup G := D.T ⊓ L with hT0def
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 T0 L := uc22p22r_fo_sylow_inf D.sylowM hL.1
  set B : Subgroup G := L ⊓ Subgroup.normalizer (T0 : Set G) with hBdef
  have hT0B : T0 ≤ B := fun x hx => ⟨hTsyl.le hx, Subgroup.le_normalizer hx⟩
  have hBL : B ≤ L := inf_le_left
  have hBN : B ≤ Subgroup.normalizer (T0 : Set G) := inf_le_right
  have hOle : OInf L ≤ L := Subgroup.map_subtype_le _
  have hON : OInf L ≤ Subgroup.normalizer (T0 : Set G) := oinf_le_normalizer_inf_sylow hL
  have hOB : OInf L ≤ B := fun x hx => ⟨hOle hx, hON hx⟩
  have hBsyl : CFSG.ABGLocalTools.IsSylowOf 2 T0 B :=
    CFSG.ABGLocalTools.IsSylowOf.of_le hTsyl hT0B hBL
  have hPn : (T0.subgroupOf B).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hT0B).mpr hBN
  have hOn : ((OInf L).subgroupOf B).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOB).mpr
      (hBL.trans (uc22p20a_le_normalizer_oinf L))
  have hP2 : IsPGroup 2 (T0.subgroupOf B) := hTsyl.isPGroup.comap_subtype
  have hPodd : Odd (T0.subgroupOf B).index := by
    have hidx : (T0.subgroupOf B).index = T0.relIndex B := by
      have h := Subgroup.relIndex_subgroupOf (H := T0) (K := B) (L := B) (le_refl B)
      rw [Subgroup.subgroupOf_self, Subgroup.relIndex_top_right] at h
      exact h
    rw [hidx]
    refine Nat.not_even_iff_odd.mp fun he => ?_
    exact (CFSG.ABGLocalTools.isSylowOf_iff.mp hBsyl).2.2 (even_iff_two_dvd.mp he)
  haveI := hOn
  haveI := hPn
  obtain ⟨C0, hNC0, hodd0, k, hk⟩ :=
    CFSG.GroupTheory.exists_cartan_complement ((OInf L).subgroupOf B) (T0.subgroupOf B)
      hPn hP2 hPodd
  have hCsub : (C0.map B.subtype).subgroupOf B = C0 :=
    Subgroup.comap_map_eq_self_of_injective B.subtype_injective C0
  refine ⟨C0.map B.subtype, (Subgroup.map_subtype_le C0).trans hBL, ?_,
    (Subgroup.map_subtype_le C0).trans hBN, ?_, ?_⟩
  · rw [← Subgroup.map_subgroupOf_eq_of_le hOB]
    exact Subgroup.map_mono hNC0
  · have hrel : (OInf L).relIndex (C0.map B.subtype) =
        ((OInf L).subgroupOf B).relIndex C0 := by
      have h := Subgroup.relIndex_subgroupOf (H := OInf L) (K := C0.map B.subtype) (L := B)
        (Subgroup.map_subtype_le C0)
      rw [hCsub] at h
      exact h.symm
    rw [hrel]
    exact hodd0
  · refine ⟨k, ?_⟩
    have hrelB : (C0.map B.subtype).relIndex B = C0.index := by
      have h := Subgroup.relIndex_subgroupOf (H := C0.map B.subtype) (K := B) (L := B)
        (le_refl B)
      rw [Subgroup.subgroupOf_self, Subgroup.relIndex_top_right] at h
      rw [← h, hCsub]
    exact hrelB.trans hk

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
