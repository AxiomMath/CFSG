module

public import CFSG.RankThree.PartTwo.Sec15.Item158StepsProof159
public import CFSG.RankThree.PartTwo.Sec17.RouteForms
import CFSG.RankThree.PartTwo.Sec16.Item169StepsProof1612
import CFSG.RankThree.PartTwo.Sec16.Item163StepsQProof
import CFSG.RankThree.PartTwo.Sec17.Item171GenProofA7
import CFSG.RankThree.PartTwo.Sec12.Item122

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

@[expose] noncomputable def Step159Y0Gen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx159 G A c L → CFSG.Open.pCoreOf 2 L ≠ ⊥ →
    IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) →
      L ≤ sSup (invariantPiSubgroups L A (piCompl 3))

@[expose] noncomputable def Step159Y0Odd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx159 G A c L → CFSG.Open.pCoreOf 2 L = ⊥ → (scriptY0 A (lB A)).Nonempty

variable {G : Type} [Group G] [Finite G]

theorem mem_scriptY0_of_ctx159
    (h135 : Item135) (h142 : Item142R) (hgen : Step159Y0Gen)
    {A L : Subgroup G} {c : G} (ctx : Ctx159 G A c L) (hO : CFSG.Open.pCoreOf 2 L ≠ ⊥) :
    L ∈ scriptY0 A (lB A) := by
  have h := ctx.toSec15R
  have hD := h.toSec13Data
  have hY : L ∈ scriptY A := by
    refine ⟨fun htop => ?_, hD.le_normalizer⟩
    apply Sec12.centralizer_ne_top_of_theoremFourHyp h.toTheoremFourHyp hD.ne_one
    exact top_le_iff.mp (htop ▸ hD.le_centralizer)
  have hgen' : L ≤ sSup (invariantPiSubgroups L A (piCompl 3)) := by
    by_cases h7 : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7))
    · exact Sec17.Proof171Gen.le_sSup_invariantPiSubgroups_of_sec13Data hD h7
    · exact hgen G A c L ctx hO (not_nonempty_iff.mp h7)
  exact ⟨⟨hY, Sec16.eq_oPrimeResidualOf_of_sec15R h,
    Sec16.Proof1612.eq_delta_of_gen h (h142 G A c L h) hgen',
    h135 G A c L hD h.hypS_or_hypT⟩, hY, hO⟩

theorem step159Y0_of
    (h135 : Item135) (h142 : Item142R) (hgen : Step159Y0Gen)
    (hodd : Step159Y0Odd) : Step159Y0 := by
  intro G _ _ A c L ctx
  by_cases hO : CFSG.Open.pCoreOf 2 L = ⊥
  · exact hodd G A c L ctx hO
  · exact ⟨L, mem_scriptY0_of_ctx159 h135 h142 hgen ctx hO⟩

end CFSG.RankThree.PartTwo.Sec15
