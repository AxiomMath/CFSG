module

public import CFSG.OddTranspositions.PartThree.Twelve.Minimal
import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveGlue
import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveRecog
import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveModel
public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveModelCentralizer
public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFivePlumbing
import CFSG.OddTranspositions.PartThree.Twelve.NineFive
import CFSG.OddTranspositions.PartThree.Twelve.NineCenter
import CFSG.OddTranspositions.PartThree.Nine.NineFiveGraph

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.PartFour
open CFSG.LocalAnalysis.WeakClosure81 CFSG.Fischer

theorem fiveReflections_nonempty_of_model {G : Type} [Group G] {D : Set G} {n : ℕ} {ε π : Bool}
    (hD : D.Nonempty) (h : IsFiveReflectionModel n ε π D) : (fiveReflections n ε π).Nonempty := by
  obtain ⟨φ, hφ⟩ := isFiveReflectionModel_iff_proj.1 h
  obtain ⟨g, hg⟩ := hD
  obtain ⟨r, hr, -⟩ := (hφ g).1 hg
  exact ⟨r, hr⟩

theorem commSet_nonempty_of_fiveLocalModel {G : Type} [Group G] {D : Set G} {x : G} {k : ℕ}
    {ε π : Bool} (c : FiveLocalModel D x k ε π) (hR : (fiveReflections k ε π).Nonempty) :
    (commSet D x).Nonempty := by
  obtain ⟨r, hr⟩ := hR
  have hrR : r ∈ fiveReflectionGroup k ε π := Subgroup.subset_closure hr
  refine ⟨(c.toMulEquiv.symm ⟨r, hrR⟩ : G), ?_⟩
  rw [c.mem_iff, MulEquiv.apply_symm_apply]
  exact hr

section Certs


theorem twelveEleven_five (h87 : Theorem8_7) {G : Type} [Group G] [Finite G] {D : Set G}
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {k : ℕ} (hk : 4 ≤ k) {ε π : Bool} (hm : IsFiveReflectionModel k ε π (imageClass hC)) :
    IsFiveReflectionModel (k + 1) (ε == π) π D := by
  have hα : hC.alpha = {hC.d} := alpha_eq_singleton_five hC hMZ hk hm
  have hZ : Subgroup.center G = ⊥ := hrad _ inferInstance inferInstance
  have hO4 : ¬ CFSG.OddTranspositions.QZ.O4PairData G D := not_o4PairData_five hC hMZ hα hk hm
  have hdiamD : ∀ a ∈ D, ∀ b ∈ D, ¬ Commute a b → (commSet D a ∩ commSet D b).Nonempty :=
    fun a ha b hb hab =>
      Nine.commSet_inter_nonempty_of_theorem8_7 h87 hC hα hrad hO4 ha hb hab
  have hdiam : ∀ w ∈ D, ¬ Commute w hC.d → (commSet D hC.d ∩ commSet D w).Nonempty :=
    fun w hw hwd => hdiamD hC.d hC.hd w hw (fun h => hwd h.symm)
  have haxis : ∀ u : D, ∀ σ : commGraph D ≃g commGraph D,
      (∀ v : D, Commute (v : G) u → σ v = v) →
      (∀ v : D, σ v = v) ∨ ∀ v : D, (σ v : G) = (u : G) * v * u :=
    fun u σ hσ => twelveNine_five hC hMZ hα hk hm hdiam u σ hσ
  have hcen : ∀ z ∈ Subgroup.center (Halpha D hC.alpha), (z : G) = 1 ∨ (z : G) = hC.d :=
    fun z hz => center_Halpha_le hC hα hZ (haxis ⟨hC.d, hC.hd⟩) hz
  obtain ⟨cu⟩ := fiveLocalModel_of_center hC hMZ hα hk hm hcen
  have hD : FiveLocalData D k ε π :=
    fiveLocalData_of_pivot hC.setup hC.hd ⟨cu⟩
      (fun c => fiveHyperplaneData_of_twelveSix hC hα hk hdiam hcen c)
  obtain ⟨A⟩ := nonempty_fiveAdjoin k ε π
  obtain ⟨r, hr, ⟨cu'⟩⟩ := exists_fiveLocalModel_proj hk A
  have hrmem : (r : GL (Fin (k + 2)) (ZMod 5)) ∈ fiveReflections (k + 1) (ε == π) π :=
    ⟨A.a, A.sign_a.1, A.sign_a.2, hr⟩
  have hu' : (QuotientGroup.mk r : fiveProjective (k + 1) (ε == π) π) ∈
      fiveProjClass (k + 1) (ε == π) π := ⟨r, hrmem, rfl⟩
  have hS' := setup_fiveProjClass (n := k + 1) (by omega) (ε == π) π
  have hZ' := center_fiveProjective_eq_bot (n := k + 1) (by omega) (ε == π) π
  have hD' : FiveLocalData (fiveProjClass (k + 1) (ε == π) π) k ε π :=
    fiveLocalData_of_pivot hS' hu' ⟨cu'⟩ (fun c => fiveHyperplaneData_proj hk ε π hu' c)
  have hR : (fiveReflections k ε π).Nonempty :=
    fiveReflections_nonempty_of_model (imageClass_nonempty hC) hm
  obtain ⟨β⟩ := nonempty_commGraphIso_five hk hC.setup hS' hD hD' hdiamD
    (diameter_two_fiveProjClass (n := k + 1) (by omega) (ε == π) π) hC.hd hu' cu cu'
    (commSet_nonempty_of_fiveLocalModel cu hR)
    (fun s hs hsu => centralizer_eq_hypLineGroup_five hC hMZ hα hk hm hdiam hcen hD hs hsu)
    (fun s hs hsu => centralizer_eq_hypLineGroup_proj hk ε π hu' hs hsu)
  exact isFiveReflectionModel_of_commGraphIso hC.setup hS' hZ hZ' β haxis

theorem twelveEleven_five_conclusion (h87 : Theorem8_7) {G : Type} [Group G] [Finite G]
    {D : Set G} (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {k : ℕ} (hk : 4 ≤ k) {ε π : Bool} (hm : IsFiveReflectionModel k ε π (imageClass hC)) :
    TheoremFourConclusion hC := by
  have h : ((ε == π) == π) = ε := by
    cases ε <;> cases π <;> rfl
  refine Or.inr (Or.inl ⟨k, ε == π, π, by omega, ?_,
    twelveEleven_five h87 hC hrad hMZ hk hm⟩)
  rw [h]
  exact hm

end Certs

end CFSG.OddTranspositions.PartThree

end
