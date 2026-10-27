module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitz
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionAltDefining

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.AGLEmbeddingD2

@[expose] def GGKFSeitzLTwoEight (i : TauCeti.CFSGIndex) (p : ℕ) : Prop :=
  p = 3 ∧ ∃ (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower), i = .lie d ∧ q.p = 2 ∧
    q.exponent = 3 ∧ d.1 = .A 1 q

@[expose] def GGKFSeitzLThreeFour (i : TauCeti.CFSGIndex) (p : ℕ) : Prop :=
  p = 3 ∧ ∃ (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower), i = .lie d ∧ q.p = 2 ∧
    q.exponent = 2 ∧ d.1 = .A 2 q

@[expose] def GGKFSeitzUFourTwo (i : TauCeti.CFSGIndex) (p : ℕ) : Prop :=
  p = 3 ∧ ∃ (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower), i = .lie d ∧ q.p = 2 ∧
    q.exponent = 1 ∧ d.1 = .twistedA 3 q

@[expose] def GGKFSeitzSpSixTwo (i : TauCeti.CFSGIndex) (p : ℕ) : Prop :=
  p = 3 ∧ ∃ (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower), i = .lie d ∧ q.p = 2 ∧
    q.exponent = 1 ∧ d.1 = .B 3 q

@[expose] def GGKFSeitzSpEightTwo (i : TauCeti.CFSGIndex) (p : ℕ) : Prop :=
  p = 3 ∧ ∃ (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower), i = .lie d ∧ q.p = 2 ∧
    q.exponent = 1 ∧ d.1 = .B 4 q

@[expose] def GGKFSeitzTitsThree (i : TauCeti.CFSGIndex) (p : ℕ) : Prop :=
  p = 3 ∧ ∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧ d.1 = .tits

@[expose] def GGKFSeitzTitsFive (i : TauCeti.CFSGIndex) (p : ℕ) : Prop :=
  p = 5 ∧ ∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧ d.1 = .tits

@[expose] def GGKFSeitzSzThirtyTwo (i : TauCeti.CFSGIndex) (p : ℕ) : Prop :=
  p = 5 ∧ ∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧ d.1 = .suzuki 2

theorem ggKGroupFusionAt_seitzException_of (h₁ : GGKGroupFusionAt GGKFSeitzLTwoEight)
    (h₂ : GGKGroupFusionAt GGKFSeitzLThreeFour) (h₃ : GGKGroupFusionAt GGKFSeitzUFourTwo)
    (h₄ : GGKGroupFusionAt GGKFSeitzSpSixTwo) (h₅ : GGKGroupFusionAt GGKFSeitzSpEightTwo)
    (h₆ : GGKGroupFusionAt GGKFSeitzTitsThree) (h₇ : GGKGroupFusionAt GGKFSeitzTitsFive)
    (h₈ : GGKGroupFusionAt GGKFSeitzSzThirtyTwo) : GGKGroupFusionAt GGKFLieSeitzException := by
  intro W _ _ p H E i ⟨d, hi, hex⟩ hyp hL hK he
  rcases hex with ⟨rfl, ⟨q, hq2, hq3, hd⟩ | ⟨q, hq2, hq3, hd⟩ | ⟨q, hq2, hq3, hd⟩ |
    ⟨q, hq2, hq3, hd | hd⟩ | hd⟩ | ⟨rfl, hd | hd⟩
  · exact h₁ W 3 H E i ⟨rfl, d, q, hi, hq2, hq3, hd⟩ hyp hL hK he
  · exact h₂ W 3 H E i ⟨rfl, d, q, hi, hq2, hq3, hd⟩ hyp hL hK he
  · exact h₃ W 3 H E i ⟨rfl, d, q, hi, hq2, hq3, hd⟩ hyp hL hK he
  · exact h₄ W 3 H E i ⟨rfl, d, q, hi, hq2, hq3, hd⟩ hyp hL hK he
  · exact h₅ W 3 H E i ⟨rfl, d, q, hi, hq2, hq3, hd⟩ hyp hL hK he
  · exact h₆ W 3 H E i ⟨rfl, d, hi, hd⟩ hyp hL hK he
  · exact h₇ W 5 H E i ⟨rfl, d, hi, hd⟩ hyp hL hK he
  · exact h₈ W 5 H E i ⟨rfl, d, hi, hd⟩ hyp hL hK he

section Common

variable {W : Type} [Group W] {p : ℕ} {H E : Subgroup W}

theorem ggSeitzExc_subgroupOf_ne_top (hKH : ¬ CFSG.generalizedFitting W ≤ H) :
    H.subgroupOf (CFSG.generalizedFitting W) ≠ ⊤ := fun h =>
  hKH (Subgroup.subgroupOf_eq_top.mp h)

theorem ggNot_isSolvable_of_layer_ne_bot (hL : LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) ≠ ⊥) :
    ¬ Group.IsSolvable ↥H := by
  intro hH
  apply hL
  refine sSup_eq_bot.mpr fun C hC => ?_
  exfalso
  have : Group.IsSolvable (GGHypQuot H) := inferInstance
  exact ggComponent_not_le_of_isSolvable hC (A := ⊤) inferInstance le_top

variable [Finite W]

theorem ggHypThreeSixteen_exists_ne_one (hyp : GGHypThreeSixteen p H E) : ∃ e ∈ E, e ≠ 1 := by
  obtain ⟨⟨hp, -, -, hEcard, -⟩, -⟩ := hyp
  by_contra hcon
  push Not at hcon
  have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr hcon
  rw [hbot, Subgroup.card_bot] at hEcard
  have h1 := hp.one_lt
  have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) h1
  omega

theorem ggSeitzExc_not_dvd_index (hyp : GGHypThreeSixteen p H E) :
    ¬ p ∣ (H.subgroupOf (CFSG.generalizedFitting W)).index := by
  obtain ⟨e, heE, he1⟩ := ggHypThreeSixteen_exists_ne_one hyp
  obtain ⟨⟨hp, -, hE, -, hfus⟩, -⟩ := hyp
  have : Fact p.Prime := ⟨hp⟩
  have : (CFSG.generalizedFitting W).Normal :=
    CFSG.LocalCores.generalized_fitting_characteristic.2
  have h := hfus.not_dvd_relIndex_inf hE heE he1 (CFSG.generalizedFitting W)
  rwa [Subgroup.relIndex, Subgroup.inf_subgroupOf_right] at h

theorem ggSeitzExc_not_isSolvable (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor InCatalog)
    (hyp : GGHypThreeSixteen p H E) (hL : LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) ≠ ⊥) :
    ¬ Group.IsSolvable ↥(H.subgroupOf (CFSG.generalizedFitting W)) := by
  intro hX
  have : (CFSG.generalizedFitting W).Normal :=
    CFSG.LocalCores.generalized_fitting_characteristic.2
  set N := ((QuotientGroup.mk' (CFSG.generalizedFitting W)).comp H.subtype).ker
  have hN : Group.IsSolvable ↥N :=
    Group.isSolvable_of_isSolvable_injective
      (f := (ggSubgroupOfEquivKer H (CFSG.generalizedFitting W)).symm.toMonoidHom)
      (ggSubgroupOfEquivKer H (CFSG.generalizedFitting W)).symm.injective
  have hQ := ggIsSolvable_quot_inf_generalizedFitting hSch hyp
  exact ggNot_isSolvable_of_layer_ne_bot hL (Group.isSolvable_of_subgroup_quotient N)

theorem ggKGroupFusionAt_of_solvable
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor InCatalog)
    {S : TauCeti.CFSGIndex → ℕ → Prop}
    (h : ∀ (i : TauCeti.CFSGIndex) (p : ℕ), S i p → ∀ (K : Type) [Group K] [Finite K],
      IsSimpleGroup K → Nonempty (K ≃* i.Group) →
        ∀ X : Subgroup K, X ≠ ⊤ → ¬ p ∣ X.index → Group.IsSolvable ↥X) :
    GGKGroupFusionAt S := by
  intro W _ _ p H E i hi hyp hL hKH he
  exact (ggSeitzExc_not_isSolvable hSch hyp hL (h i p hi _ hyp.2.1.1 he _
    (ggSeitzExc_subgroupOf_ne_top hKH) (ggSeitzExc_not_dvd_index hyp))).elim

end Common

end CFSG.StandardType
