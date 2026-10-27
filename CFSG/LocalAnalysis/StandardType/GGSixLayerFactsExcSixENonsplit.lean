module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixEMain
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcPilotNonsplit
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotNonsplit
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviModel

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.SeitzReduction

namespace LayerSixE

theorem autFix_map_conj {C : Type*} [Group C] (Y : Subgroup C) :
    autFix (Y.map (MulAut.conj : C →* MulAut C)) = Subgroup.centralizer (Y : Set C) := by
  ext x
  rw [mem_autFix, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx y hy
    have h := hx _ ⟨y, hy, rfl⟩
    rw [MulAut.conj_apply] at h
    calc y * x = y * x * y⁻¹ * y := by group
      _ = x * y := by rw [h]
  · rintro hx _ ⟨y, hy, rfl⟩
    rw [MulAut.conj_apply, hx y hy, mul_inv_cancel_right]

end LayerSixE

section Defs

@[expose] def GGE6InndiagHighNonsplit
    (K : Type) [Field K] (A : Subgroup (MulAut ↥(adjointGroup .E6 K))) : Prop :=
  ∃ (g : ↥(adjointGroup .E6 K)) (X : Subgroup ↥(adjointGroup .E6 K)),
    X ≤ (EPilot.highRootSL2 .E6 K).subgroupOf (adjointGroup .E6 K) ∧ IsCyclic X ∧
      Nat.card X = Nat.card K + 1 ∧
        A = (X.map (MulAut.conj g⁻¹).toMonoidHom).map
          (MulAut.conj : ↥(adjointGroup .E6 K) →* MulAut ↥(adjointGroup .E6 K))

end Defs

section Nonsplit


theorem LayerSixE.exists_subCoreFamily_autFix_highNonsplit_E6 {K : Type} [Field K] [Finite K]
    [CharP K 2] (A : Subgroup (MulAut ↥(adjointGroup .E6 K))) (h : GGE6InndiagHighNonsplit K A) :
    ∃ (β : Type) (S : β → Subgroup ↥(adjointGroup .E6 K)), LayerCores.IsSubCoreFamily (autFix A) S := by
  obtain ⟨g, X, hXJ, hcyc, hX, rfl⟩ := h
  rw [autFix_map_conj]
  refine LayerExc.exists_subCoreFamily_centralizer_of_conj g _ ?_
  have hmap : (X.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = X := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id X
    refine MonoidHom.ext fun x => ?_
    change g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x
    group
  rw [hmap]
  obtain ⟨hC, -, hXD⟩ := E6Pilot.centralizer_nonsplit_E6 hXJ hX hcyc
  rw [hC]
  exact ⟨Unit, fun _ => E6Pilot.a5Levi K, LayerExc.isSubCoreFamily_sup_of_centralizer
    (LayerExc.commute_of_isCyclic hcyc) hXD E6Pilot.isQuasisimple_a5Levi
    E6Pilot.center_a5Levi_eq_bot⟩

@[expose] def GGE6InndiagCoreNonToralRestInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ), p.Prime → p ≠ 2 →
    ∀ A : Subgroup (MulAut ↥(adjointGroup .E6 K)), IsPGroup p A →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → A ≤ LayerSixE.inndiagAut .E6 K →
        ¬ LayerSixE.GGInndiagToral .E6 K A → ¬ GGE6InndiagHighNonsplit K A →
          ∃ (β : Type) (S : β → Subgroup ↥(adjointGroup .E6 K)),
            LayerCores.IsSubCoreFamily (LayerSixE.autFix A) S

theorem ggE6InndiagCoreNonToralInput_of_rest (h : GGE6InndiagCoreNonToralRestInput) :
    GGE6InndiagCoreNonToralInput := by
  intro K _ _ _ p hp hp2 A hA hAc hAD ht
  by_cases hn : GGE6InndiagHighNonsplit K A
  · exact LayerSixE.exists_subCoreFamily_autFix_highNonsplit_E6 A hn
  · exact h K p hp hp2 A hA hAc hAD ht hn

theorem ggLayerTags_E6_of_rest (hW : GGWeylFamQuotSolvInput .E6)
    (h : GGE6InndiagCoreNonToralRestInput) : GGLayerCentreOddTag .E6 ∧ GGLayerPerfectTag .E6 :=
  ggLayerTags_E6_of_nonToral hW (ggE6InndiagCoreNonToralInput_of_rest h)

end Nonsplit

end CFSG.StandardType
