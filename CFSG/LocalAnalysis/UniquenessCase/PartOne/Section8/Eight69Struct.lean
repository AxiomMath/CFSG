module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69R874
public import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data Bar2 IsSL3 IsSU3)

@[expose] def R873Mod {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ L X H : Subgroup G, MinCex869 D L X H →
    2 ≤ CFSG.Open.pRank 3 X ∧ (IsSL3 (Bar2 X) 2 ∨ IsSU3 (Bar2 X) 3)

@[expose] def R875O2HM {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ L X H : Subgroup G, MinCex869 D L X H → pCoreOf 2 (H ⊓ D.M) = ⊥

theorem r873M3_of_r873Mod {G : Type} [Group G] [Finite G] {D : Data G} (h : R873Mod D) :
    R873M3 D :=
  fun L X H hmin => (h L X H hmin).1

private theorem r873s52_pCoreOf_le_pCoreOf_of_isSubnormal {G : Type} [Group G] {A B : Subgroup G}
    (h : IsSubnormal A B) : pCoreOf 2 A ≤ pCoreOf 2 B := by
  induction h with
  | refl => exact le_rfl
  | @step H M K hle hN _ ih =>
    refine le_trans ?_ ih
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H).trans hle) ?_
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H)
    intro m hm
    have hmH : m ∈ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hN hm
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 H hmH

private theorem r873s52_pCoreOf_le_pCoreOf_of_eq_sup {G : Type} [Group G] {L X : Subgroup G}
    (hXL : X ≤ L) (hXO : X ⊔ pCoreOf 2 L = L) : pCoreOf 2 X ≤ pCoreOf 2 L := by
  have hXNL : X ≤ Subgroup.normalizer ((pCoreOf 2 L : Subgroup G) : Set G) :=
    hXL.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 L)
  have hNX : pCoreOf 2 X ≤ Subgroup.normalizer ((pCoreOf 2 L : Subgroup G) : Set G) :=
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 X).trans hXNL
  have hTp : IsPGroup 2 ↥(pCoreOf 2 X ⊔ pCoreOf 2 L) :=
    IsPGroup.to_sup_of_normal_right'
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 X)
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 L) hNX
  have hXnormT : X ≤
      Subgroup.normalizer (((pCoreOf 2 X ⊔ pCoreOf 2 L) : Subgroup G) : Set G) :=
    (le_inf (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 X) hXNL).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hpLnormT : pCoreOf 2 L ≤
      Subgroup.normalizer (((pCoreOf 2 X ⊔ pCoreOf 2 L) : Subgroup G) : Set G) :=
    le_sup_right.trans Subgroup.le_normalizer
  have hLnormT : L ≤
      Subgroup.normalizer (((pCoreOf 2 X ⊔ pCoreOf 2 L) : Subgroup G) : Set G) := by
    calc L = X ⊔ pCoreOf 2 L := hXO.symm
      _ ≤ _ := sup_le hXnormT hpLnormT
  have hTle : (pCoreOf 2 X ⊔ pCoreOf 2 L) ≤ pCoreOf 2 L :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (sup_le ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 X).trans hXL)
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 L)) hLnormT hTp
  exact le_sup_left.trans hTle

private theorem r873s52_pCoreOf_inf_le_pCoreOf_inf {G : Type} [Group G] {L H M : Subgroup G}
    (hsub : IsSubnormal L M) : pCoreOf 2 L ⊓ H ≤ pCoreOf 2 (H ⊓ M) := by
  have hLM : L ≤ M := hsub.le
  have hsub' : IsSubnormal (L ⊓ H) (H ⊓ M) := by
    have hEq : L ⊓ (H ⊓ M) = L ⊓ H := by
      rw [← inf_assoc, inf_eq_left.mpr ((inf_le_left : L ⊓ H ≤ L).trans hLM)]
    simpa only [hEq] using IsSubnormal.inf_of_le hsub (inf_le_right : H ⊓ M ≤ M)
  have hSle : pCoreOf 2 L ⊓ H ≤ L ⊓ H :=
    le_inf (inf_le_left.trans (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 L)) inf_le_right
  have hnorm : L ⊓ H ≤ Subgroup.normalizer ((pCoreOf 2 L ⊓ H : Subgroup G) : Set G) :=
    (le_inf (inf_le_left.trans
        (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 L))
      (inf_le_right.trans Subgroup.le_normalizer)).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := pCoreOf 2 L) (K := H))
  have hS2 : IsPGroup 2 ↥(pCoreOf 2 L ⊓ H) :=
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 L).to_le inf_le_left
  exact (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hSle hnorm hS2).trans
    (r873s52_pCoreOf_le_pCoreOf_of_isSubnormal hsub')

theorem pCoreOf_two_le_pCoreOf_inf {G : Type} [Group G] [Finite G] {D : Data G} {L X H : Subgroup G}
    (h : MinCex869 D L X H) : pCoreOf 2 X ≤ pCoreOf 2 (H ⊓ D.M) := by
  have hLsub : IsSubnormal L D.M := by
    rcases h.hyp.1 with hL | ⟨hLM, hMn, -⟩
    · exact hL.1
    · exact IsSubnormal.step hLM ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).2 hMn)
        (IsSubnormal.refl D.M)
  have hXL : X ≤ L := h.hyp.2.1
  have hXO : X ⊔ pCoreOf 2 L = L := h.hyp.2.2.1
  have hXH : X ≤ H := h.mem.2
  have h1 : pCoreOf 2 X ≤ pCoreOf 2 L := r873s52_pCoreOf_le_pCoreOf_of_eq_sup hXL hXO
  have h2 : pCoreOf 2 X ≤ pCoreOf 2 L ⊓ H :=
    le_inf h1 ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 X).trans hXH)
  exact h2.trans (r873s52_pCoreOf_inf_le_pCoreOf_inf hLsub)

private theorem r873s58_pCoreOf_eq_bot {G : Type} [Group G] [Finite G] {D : Data G}
    {L X H : Subgroup G} (hmin : MinCex869 D L X H) (hO2 : R875O2HM D) :
    pCoreOf 2 X = ⊥ :=
  le_bot_iff.1 ((pCoreOf_two_le_pCoreOf_inf hmin).trans (le_of_eq (hO2 L X H hmin)))

private theorem r873s58_pCore_eq_bot {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (h : pCoreOf 2 X = ⊥) : CFSG.pCore 2 ↥X = ⊥ := by
  rw [CFSG.Open.pCoreOf] at h
  exact (Subgroup.map_eq_bot_iff_of_injective (CFSG.pCore 2 ↥X) X.subtype_injective).1 h

private noncomputable def r873s58_bar2_equiv {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (h : CFSG.pCore 2 ↥X = ⊥) : Bar2 X ≃* ↥X :=
  (QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot

private theorem r873s58_isQuasisimple_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.Open.IsQuasisimple A) : CFSG.Open.IsQuasisimple B := by
  obtain ⟨hperf, hsimple⟩ := h
  refine ⟨?_, ?_⟩
  · have h1 : (commutator A).map e.toMonoidHom = commutator B := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ e.surjective]
    rw [← h1, hperf]
    exact Subgroup.map_top_of_surjective _ e.surjective
  · have hc : (Subgroup.center A).map e.toMonoidHom = Subgroup.center B :=
      Subgroup.map_center_eq e
    have := hsimple
    exact (QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e hc).symm.isSimpleGroup

private theorem r873s58_isSL3_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) {f : ℕ}
    (h : IsSL3 A f) : IsSL3 B f :=
  ⟨r873s58_isQuasisimple_of_mulEquiv e h.1,
    CFSG.Blueprint.LieModel.quotient_center_of_mulEquiv e h.2⟩

private theorem r873s58_isSU3_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) {f : ℕ}
    (h : IsSU3 A f) : IsSU3 B f :=
  ⟨r873s58_isQuasisimple_of_mulEquiv e h.1,
    CFSG.Blueprint.LieModel.quotient_center_of_mulEquiv e h.2⟩

theorem r873_of_r873Mod {G : Type} [Group G] [Finite G] {D : Data G} (hMod : R873Mod D)
    (hO2 : R875O2HM D) : R873 D := by
  intro L X H hmin
  have hbot : pCoreOf 2 X = ⊥ := r873s58_pCoreOf_eq_bot hmin hO2
  have e : Bar2 X ≃* ↥X := r873s58_bar2_equiv (r873s58_pCore_eq_bot hbot)
  refine ⟨?_, hbot⟩
  rcases (hMod L X H hmin).2 with hSL | hSU
  · exact Or.inl (r873s58_isSL3_of_mulEquiv e hSL)
  · exact Or.inr (r873s58_isSU3_of_mulEquiv e hSU)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
