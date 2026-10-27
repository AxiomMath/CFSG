module

public import CFSG.RankThree.PartTwo.Sec13.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Item135Simple : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L →
    (IsLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M12) ∨
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.J2)) →
    CFSG.IsQuasisimple (L ⧸ CFSG.pCore 2 L)

@[expose] def Item135SimpleReduce : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L →
    (IsLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M12) ∨
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.J2)) →
    ¬ IsQuasisimple (L ⧸ CFSG.pCore 2 L) →
      CFSG.pCore 2 L = ⊥ ∧ CFSG.Open.pRank 2 (⊤ : Subgroup L) ≤ 2 ∧
      IsQuasisimple (L ⧸ CFSG.oddCore L) ∧
      ∃ (p e : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ 1 ≤ e ∧
        Sec4.IsoLThreePi (L ⧸ aschbacherSolvableCore 3 L) p e

@[expose] def Item135SimpleL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L → ¬ IsQuasisimple (L ⧸ CFSG.pCore 2 L) →
    CFSG.pCore 2 L = ⊥ → CFSG.Open.pRank 2 (⊤ : Subgroup L) ≤ 2 →
    IsQuasisimple (L ⧸ CFSG.oddCore L) →
    (∃ (p e : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ 1 ≤ e ∧
      Sec4.IsoLThreePi (L ⧸ aschbacherSolvableCore 3 L) p e) → False

theorem item135Simple_of_steps (hR : Item135SimpleReduce) (hL3 : Item135SimpleL3) :
    Item135Simple := by
  intro G _ _ A c L h htype
  by_contra hq
  obtain ⟨hO2, hm, hO, hL⟩ := hR G A c L h htype hq
  exact hL3 G A c L h hq hO2 hm hO hL

end CFSG.RankThree.PartTwo.Sec13
