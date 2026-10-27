module

public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsTools

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] def Step1517Y0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y, Ctx1514 A (lB A) c L Y →
      ∀ X ∈ scriptY2 A, L ≤ X → ∃ Y₀ ∈ scriptY0Star A (lB A), L ≤ Y₀

@[expose] def Step1517Con : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y, Ctx1514 A (lB A) c L Y →
      ∀ Y₀ ∈ scriptY0Star A (lB A), Y₀ ≠ Y → ¬ L ≤ Y₀

@[expose] noncomputable def Step1517Simple : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y, Ctx1514 A (lB A) c L Y → (∀ X ∈ scriptY2 A, ¬ L ≤ X) →
      IsSimpleGroup ↥L ∧ Odd (Nat.card ↥(Subgroup.centralizer ({c} : Set G) ⊓
        Subgroup.centralizer (L : Set G)))

variable {G : Type} [Group G] [Finite G]

theorem rank3II_15_17_of {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (hY0 : Step1517Y0) (hcon : Step1517Con) (hsimp : Step1517Simple) :
    Step1517 A (lB A) c L := by
  intro Y hctx
  have hno : ∀ X ∈ scriptY2 A, ¬ L ≤ X := by
    intro X hX hLX
    obtain ⟨Y₀, hY₀, hLY₀⟩ := hY0 G A c L h Y hctx X hX hLX
    by_cases hYY : Y₀ = Y
    · exact hctx.not_le (hYY ▸ hLY₀)
    · exact hcon G A c L h Y hctx Y₀ hY₀ hYY hLY₀
  exact ⟨hno, hsimp G A c L h Y hctx hno⟩

namespace Proof1514

omit [Finite G] in
theorem bot_mem_scriptQPi_two (A : Subgroup G) (LB : Subgroup G → Subgroup G) (X : Subgroup G) :
    (⊥ : Subgroup G) ∈ scriptQPi A LB X (piOf 2) := by
  refine ⟨⟨⟨bot_mem_invariantPiSubgroups ⊤ A (piCompl 3), fun B _ => ?_⟩, bot_le⟩,
    (bot_mem_invariantPiSubgroups ⊤ A (piOf 2)).2.1⟩
  rw [bot_inf_eq]
  exact bot_le

end Proof1514

open Proof1514

end CFSG.RankThree.PartTwo.Sec15
