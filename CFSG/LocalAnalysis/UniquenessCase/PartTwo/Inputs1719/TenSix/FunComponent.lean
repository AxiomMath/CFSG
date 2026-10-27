module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront14
public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLie

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirteenFund
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.LocalAnalysis.ComponentClassification.CommutingComponentFamily

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F14 (FunSet)
open CFSG.LocalAnalysis.UniquenessCase (fundPred)

private noncomputable def conjAct {G : Type} [Group G] {L T : Subgroup G}
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) : T →* MulAut ↥L :=
  (Subgroup.normalizerMonoidHom (H := L)).comp (Subgroup.inclusion hTL)

private theorem conjAct_coe {G : Type} [Group G] {L T : Subgroup G}
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (t : T) (x : ↥L) :
    (((conjAct hTL t).toMonoidHom x : ↥L) : G) = (t : G) * (x : G) * (t : G)⁻¹ := by
  rw [conjAct, MonoidHom.comp_apply]
  exact Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨t, hTL t.2⟩ x

private theorem map_conjAct_subgroupOf {G : Type} [Group G] {L T : Subgroup G}
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (t : T) :
    (T.subgroupOf L).map (conjAct hTL t).toMonoidHom = T.subgroupOf L := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxT : (x : G) ∈ T := Subgroup.mem_subgroupOf.mp hx
    refine Subgroup.mem_subgroupOf.mpr ?_
    rw [conjAct_coe]
    exact T.mul_mem (T.mul_mem t.2 hxT) (T.inv_mem t.2)
  · intro hy
    have hyT : (y : G) ∈ T := Subgroup.mem_subgroupOf.mp hy
    refine ⟨conjAct hTL t⁻¹ y, ?_, ?_⟩
    · refine Subgroup.mem_subgroupOf.mpr ?_
      change (((conjAct hTL t⁻¹).toMonoidHom y : ↥L) : G) ∈ T
      rw [conjAct_coe]
      simpa only [Subgroup.coe_inv, inv_inv] using
        T.mul_mem (T.mul_mem (T.inv_mem t.2) hyT) t.2
    · have h1 : conjAct hTL t⁻¹ = (conjAct hTL t)⁻¹ := map_inv _ _
      rw [h1]
      simp

private theorem map_conjAct_one {G : Type} [Group G] {L T : Subgroup G}
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (K : Subgroup ↥L) :
    K.map (conjAct hTL (1 : T)).toMonoidHom = K := by
  rw [map_one]
  exact Subgroup.map_id K


theorem exists_isComponentOf_of_mem_funSet {G : Type} [Group G] [Finite G] {L T : Subgroup G}
    {q : ℕ} (hTL : T ≤ Subgroup.normalizer (L : Set G)) (P : Sylow 2 ↥L)
    (hP : (P : Subgroup ↥L) = T.subgroupOf L)
    (hcomm : ∀ K₁ ∈ FunSet (fundPred q) ↥L (P : Subgroup ↥L),
      ∀ K₂ ∈ FunSet (fundPred q) ↥L (P : Subgroup ↥L), K₁ ≠ K₂ → ⁅K₁, K₂⁆ = ⊥)
    {K : Subgroup ↥L} (hK : K ∈ FunSet (fundPred q) ↥L (P : Subgroup ↥L))
    (hKq : IsQuasisimple ↥K) :
    ∃ H : Subgroup G, T ≤ H ∧ IsComponentOf (K.map L.subtype) H := by
  classical
  have hKP : ∀ t : T,
      (P : Subgroup ↥L).map (conjAct hTL t).toMonoidHom = (P : Subgroup ↥L) := by
    intro t
    rw [hP]
    exact map_conjAct_subgroupOf hTL t
  have hKt : ∀ t : T,
      K.map (conjAct hTL t).toMonoidHom ∈ FunSet (fundPred q) ↥L (P : Subgroup ↥L) := by
    intro t
    have h := CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.funSet_map_mulEquiv
      (q := q) (conjAct hTL t) hK
    rwa [hKP t] at h
  let 𝒞 : Set (Subgroup G) :=
    Set.range fun t : T => (K.map (conjAct hTL t).toMonoidHom).map L.subtype
  have hcommute : ∀ X ∈ 𝒞, ∀ Y ∈ 𝒞, X ≠ Y → ⁅X, Y⁆ = ⊥ := by
    rintro X ⟨s, rfl⟩ Y ⟨t, rfl⟩ hne
    have hst : K.map (conjAct hTL s).toMonoidHom ≠ K.map (conjAct hTL t).toMonoidHom :=
      fun h => hne (by simp only [h])
    have hc := hcomm _ (hKt s) _ (hKt t) hst
    rw [← Subgroup.map_commutator (f := L.subtype), hc, Subgroup.map_bot]
  have hKq' : CFSG.Open.IsQuasisimple ↥K :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥K).mpr hKq
  have hquasi : ∀ X ∈ 𝒞, CFSG.Open.IsQuasisimple X := by
    rintro X ⟨t, rfl⟩
    exact CFSG.Open.IsQuasisimple.of_mulEquiv
      (Subgroup.equivMapOfInjective _ L.subtype L.subtype_injective).symm
      (CFSG.Open.IsQuasisimple.of_mulEquiv
        (MulEquiv.subgroupMap (conjAct hTL t) K).symm hKq')
  have hpres : ∀ t : T, ∀ X ∈ 𝒞, X.map (MulAut.conj (t : G)).toMonoidHom ∈ 𝒞 := by
    rintro t X ⟨s, rfl⟩
    refine ⟨t * s, ?_⟩
    have hcomp : (MulAut.conj (t : G)).toMonoidHom.comp L.subtype =
        L.subtype.comp (conjAct hTL t).toMonoidHom := by
      ext x
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
      change (MulAut.conj (t : G)) (x : G) =
        (((conjAct hTL t).toMonoidHom x : ↥L) : G)
      rw [MulAut.conj_apply, conjAct_coe]
    have hmul : ((conjAct hTL t).toMonoidHom.comp (conjAct hTL s).toMonoidHom) =
        (conjAct hTL (t * s)).toMonoidHom := by
      rw [map_mul]
      rfl
    have hcalc : ((K.map (conjAct hTL s).toMonoidHom).map L.subtype).map
          (MulAut.conj (t : G)).toMonoidHom
        = K.map (L.subtype.comp (conjAct hTL (t * s)).toMonoidHom) := by
      calc ((K.map (conjAct hTL s).toMonoidHom).map L.subtype).map
            (MulAut.conj (t : G)).toMonoidHom
          = (K.map (conjAct hTL s).toMonoidHom).map
              ((MulAut.conj (t : G)).toMonoidHom.comp L.subtype) := by
            rw [Subgroup.map_map]
        _ = (K.map (conjAct hTL s).toMonoidHom).map
              (L.subtype.comp (conjAct hTL t).toMonoidHom) := by rw [hcomp]
        _ = K.map ((L.subtype.comp (conjAct hTL t).toMonoidHom).comp
              (conjAct hTL s).toMonoidHom) := by rw [Subgroup.map_map]
        _ = K.map (L.subtype.comp (conjAct hTL (t * s)).toMonoidHom) := by
            rw [MonoidHom.comp_assoc, hmul]
    show (K.map (conjAct hTL (t * s)).toMonoidHom).map L.subtype
      = ((K.map (conjAct hTL s).toMonoidHom).map L.subtype).map
          (MulAut.conj (t : G)).toMonoidHom
    rw [hcalc, Subgroup.map_map]
  let M : Subgroup G := CFSG.ComponentClassification.CommutingComponentFamily.generated 𝒞
  have hTnorm : T ≤ Subgroup.normalizer (M : Set G) := by
    intro t ht
    exact (CFSG.ComponentClassification.CommutingComponentFamily.normalizer_iff_preserves_family
      𝒞 hcommute hquasi t).mpr (hpres ⟨t, ht⟩)
  have hKC : K.map L.subtype ∈ 𝒞 := by
    refine ⟨1, ?_⟩
    show (K.map (conjAct hTL (1 : T)).toMonoidHom).map L.subtype = K.map L.subtype
    rw [map_conjAct_one hTL K]
  have hcomp := CFSG.ComponentClassification.CommutingComponentFamily.factor_component_normalizer
    𝒞 hcommute hquasi (K.map L.subtype) hKC
  have hle : K.map L.subtype ≤ Subgroup.normalizer (M : Set G) :=
    le_trans (le_sSup hKC) le_normalizer
  obtain ⟨hsub, hq'⟩ :=
    (CFSG.ComponentClassification.OrdinaryComponentTransport.subgroupOf_iff
      (K.map L.subtype) (Subgroup.normalizer (M : Set G)) hle).mp hcomp
  have hsub' : CFSG.Open.IsSubnormal (K.map L.subtype)
      (Subgroup.normalizer (M : Set G)) :=
    (CFSG.Open.IsSubnormal.iff_subgroupOf hle).mpr hsub
  exact ⟨Subgroup.normalizer (M : Set G), hTnorm, hle, hsub', hq'⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
