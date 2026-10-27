module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcPilotRest
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotNonsplit
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2Neighbour
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotNeighbourLevi
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotLeviNonsplit
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotLevi
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviPerp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.SeitzReduction

namespace LayerExc

theorem commute_of_isCyclic {L : Type*} [Group L] {X : Subgroup L} (hX : IsCyclic X) :
    ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := fun a ha b hb =>
  congrArg Subtype.val (hX.commGroup.mul_comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem isSubCoreFamily_sup_of_centralizer {L : Type*} [Group L] {X D : Subgroup L}
    (hXc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) (hXD : X ≤ Subgroup.centralizer (D : Set L))
    (hq : CFSG.IsQuasisimple D) (hZ : Subgroup.center D = ⊥) :
    LayerCores.IsSubCoreFamily (X ⊔ D) (fun _ : Unit => D) := by
  have hXN : X ≤ Subgroup.normalizer (D : Set L) := fun x hx =>
    Subgroup.mem_normalizer_iff.2 fun h => by
      constructor
      · intro hh
        rw [(Subgroup.mem_centralizer_iff.1 (hXD hx) h hh).symm, mul_inv_cancel_right]
        exact hh
      · intro hh
        have e := Subgroup.mem_centralizer_iff.1 (hXD hx) _ hh
        have e2 : h = x * h * x⁻¹ := by
          calc h = x⁻¹ * (x * h * x⁻¹ * x) := by group
            _ = x⁻¹ * (x * (x * h * x⁻¹)) := by rw [e]
            _ = x * h * x⁻¹ := by group
        rw [e2]
        exact hh
  have hDN : X ⊔ D ≤ Subgroup.normalizer (D : Set L) := sup_le hXN Subgroup.le_normalizer
  have hXX : ⁅X, X⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hXc b hb a ha
  refine ⟨fun _ => le_sup_right, fun _ => LayerCores.ggSubnormal_of_normal le_sup_right
    (fun u hu s hs => (Subgroup.mem_normalizer_iff.1 (hDN hu) s).1 hs), fun _ => hq, ⟨1, ?_⟩,
    fun z hz hzc _ => ?_⟩
  · rw [LayerFacts.ggDer_succ, LayerFacts.ggDer_zero, iSup_const, sup_comm]
    have h := commutator_sup_le_of_le_normalizer hXN
    rwa [hXX, sup_bot_eq] at h
  · rw [iSup_const] at hz hzc
    have hc : (⟨z, hz⟩ : D) ∈ Subgroup.center D :=
      Subgroup.mem_center_iff.2 fun y => Subtype.ext (hzc y y.2).symm
    rw [hZ, Subgroup.mem_bot] at hc
    exact congrArg Subtype.val hc

end LayerExc

section Defs

@[expose] def GGExcHighNonsplit
    (τ : Tag) (K : Type) [Field K] (A : Subgroup ↥(adjointGroup τ K)) : Prop :=
  ∃ (g : ↥(adjointGroup τ K)) (X : Subgroup ↥(adjointGroup τ K)),
    X ≤ (EPilot.highRootSL2 τ K).subgroupOf (adjointGroup τ K) ∧ IsCyclic X ∧
      Nat.card X = Nat.card K + 1 ∧ A.map (MulAut.conj g).toMonoidHom = X

end Defs

section Tags


theorem exists_subCoreFamily_centralizer_highNonsplit_F4 {K : Type} [Field K] [Finite K]
    [CharP K 2] (A : Subgroup ↥(adjointGroup .F4 K)) (h : GGExcHighNonsplit .F4 K A) :
    ∃ (β : Type) (S : β → Subgroup ↥(adjointGroup .F4 K)),
      LayerCores.IsSubCoreFamily (Subgroup.centralizer (A : Set ↥(adjointGroup .F4 K))) S := by
  obtain ⟨g, X, hXJ, hcyc, hX, hAX⟩ := h
  refine LayerExc.exists_subCoreFamily_centralizer_of_conj g A ?_
  rw [hAX]
  have hXJ' : X ≤ (F4Pilot.highestRootRankOne K).subgroupOf (adjointGroup .F4 K) := by
    rw [F4Pilot.highestRootRankOne_eq_rootSL2R]
    exact hXJ
  obtain ⟨hC, -, hXD⟩ := F4Pilot.centralizer_nonsplit hXJ' hcyc hX
  rw [hC]
  exact ⟨Unit, fun _ => F4Pilot.C3Levi K, LayerExc.isSubCoreFamily_sup_of_centralizer
    (LayerExc.commute_of_isCyclic hcyc) hXD F4Pilot.isQuasisimple_C3Levi
    F4Pilot.center_C3Levi_eq_bot⟩

theorem exists_subCoreFamily_centralizer_highNonsplit_E7 {K : Type} [Field K] [Finite K]
    [CharP K 2] (A : Subgroup ↥(adjointGroup .E7 K)) (h : GGExcHighNonsplit .E7 K A) :
    ∃ (β : Type) (S : β → Subgroup ↥(adjointGroup .E7 K)),
      LayerCores.IsSubCoreFamily (Subgroup.centralizer (A : Set ↥(adjointGroup .E7 K))) S := by
  obtain ⟨g, X, hXJ, hcyc, hX, hAX⟩ := h
  refine LayerExc.exists_subCoreFamily_centralizer_of_conj g A ?_
  rw [hAX]
  obtain ⟨hC, -, hXD⟩ := E6Pilot.centralizer_nonsplit_of_descent (Or.inr (Or.inl rfl))
    E7Pilot.perpLeviFrobDescent_E7_of_finite hXJ hcyc hX
  rw [hC]
  exact ⟨Unit, fun _ => EPilot.perpLevi .E7 K, LayerExc.isSubCoreFamily_sup_of_centralizer
    (LayerExc.commute_of_isCyclic hcyc) hXD E7Pilot.isQuasisimple_perpLevi_E7
    E7Pilot.center_perpLevi_E7_eq_bot⟩

theorem exists_subCoreFamily_centralizer_highNonsplit_E8 {K : Type} [Field K] [Finite K]
    [CharP K 2] (A : Subgroup ↥(adjointGroup .E8 K)) (h : GGExcHighNonsplit .E8 K A) :
    ∃ (β : Type) (S : β → Subgroup ↥(adjointGroup .E8 K)),
      LayerCores.IsSubCoreFamily (Subgroup.centralizer (A : Set ↥(adjointGroup .E8 K))) S := by
  obtain ⟨g, X, hXJ, hcyc, hX, hAX⟩ := h
  refine LayerExc.exists_subCoreFamily_centralizer_of_conj g A ?_
  rw [hAX]
  obtain ⟨hC, -, hXD⟩ := E8Pilot.centralizer_nonsplit_E8 hXJ hX hcyc
  rw [hC]
  exact ⟨Unit, fun _ => E8Pilot.e7Levi K, LayerExc.isSubCoreFamily_sup_of_centralizer
    (LayerExc.commute_of_isCyclic hcyc) hXD E8Pilot.isQuasisimple_e7Levi
    E8Pilot.center_e7Levi_eq_bot⟩

@[expose] def GGExcAdjCoreNonToralRestInput (τ : Tag) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ), p.Prime → p ≠ 2 →
    ∀ A : Subgroup ↥(adjointGroup τ K), IsPGroup p A → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      ¬ GGExcToral τ K A → ¬ GGExcHighNonsplit τ K A →
        ∃ (β : Type) (S : β → Subgroup ↥(adjointGroup τ K)),
          LayerCores.IsSubCoreFamily (Subgroup.centralizer (A : Set ↥(adjointGroup τ K))) S

theorem ggExcAdjCoreNonToralInput_of_rest_F4 (h : GGExcAdjCoreNonToralRestInput .F4) :
    GGExcAdjCoreNonToralInput .F4 := by
  intro K _ _ _ p hp hp2 A hA hAc ht
  by_cases hn : GGExcHighNonsplit .F4 K A
  · exact exists_subCoreFamily_centralizer_highNonsplit_F4 A hn
  · exact h K p hp hp2 A hA hAc ht hn

theorem ggExcAdjCoreNonToralInput_of_rest_E7 (h : GGExcAdjCoreNonToralRestInput .E7) :
    GGExcAdjCoreNonToralInput .E7 := by
  intro K _ _ _ p hp hp2 A hA hAc ht
  by_cases hn : GGExcHighNonsplit .E7 K A
  · exact exists_subCoreFamily_centralizer_highNonsplit_E7 A hn
  · exact h K p hp hp2 A hA hAc ht hn

theorem ggExcAdjCoreNonToralInput_of_rest_E8 (h : GGExcAdjCoreNonToralRestInput .E8) :
    GGExcAdjCoreNonToralInput .E8 := by
  intro K _ _ _ p hp hp2 A hA hAc ht
  by_cases hn : GGExcHighNonsplit .E8 K A
  · exact exists_subCoreFamily_centralizer_highNonsplit_E8 A hn
  · exact h K p hp hp2 A hA hAc ht hn

end Tags

end CFSG.StandardType
