module

public import CFSG.RankThree.PartTwo.Sec13.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Item135Reduce : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L → HypS A ∨ HypT A → ¬ IsQuasisimple (L ⧸ CFSG.pCore 2 L) →
      CFSG.pCore 2 L = ⊥ ∧ CFSG.Open.pRank 2 (⊤ : Subgroup L) ≤ 2 ∧
      IsQuasisimple (L ⧸ CFSG.oddCore L) ∧
      ((∃ (p e : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ 1 ≤ e ∧
          Sec4.IsoLThreePi (L ⧸ aschbacherSolvableCore 3 L) p e) ∨
        (∃ q : ℕ, q % 2 = 1 ∧ Sec4.IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) q) ∨
        Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* alternatingGroup (Fin 7)) ∨
        Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)))

@[expose] def Item135A7Z3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L → HypS A ∨ HypT A → ¬ IsQuasisimple (L ⧸ CFSG.pCore 2 L) →
    CFSG.pCore 2 L = ⊥ → CFSG.Open.pRank 2 (⊤ : Subgroup L) ≤ 2 →
    IsQuasisimple (L ⧸ CFSG.oddCore L) →
    Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) → False

@[expose] def Item135L3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L → HypS A ∨ HypT A → ¬ IsQuasisimple (L ⧸ CFSG.pCore 2 L) →
    CFSG.pCore 2 L = ⊥ → CFSG.Open.pRank 2 (⊤ : Subgroup L) ≤ 2 →
    IsQuasisimple (L ⧸ CFSG.oddCore L) →
    ((∃ (p e : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ 1 ≤ e ∧
        Sec4.IsoLThreePi (L ⧸ aschbacherSolvableCore 3 L) p e) ∨
      (∃ q : ℕ, q % 2 = 1 ∧ Sec4.IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) q)) → False

@[expose] def Item135A7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L → HypS A ∨ HypT A → ¬ IsQuasisimple (L ⧸ CFSG.pCore 2 L) →
    CFSG.pCore 2 L = ⊥ → CFSG.Open.pRank 2 (⊤ : Subgroup L) ≤ 2 →
    IsQuasisimple (L ⧸ CFSG.oddCore L) →
    Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* alternatingGroup (Fin 7)) → False

theorem rank3II_13_5_of_steps (hR : Item135Reduce) (hA7Z3 : Item135A7Z3) (hL3 : Item135L3)
    (hA7 : Item135A7) : Item135 := by
  intro G _ _ A c L h hST
  by_contra hq
  obtain ⟨hO2, hm, hO, hL | hSL | hA | hAZ⟩ := hR G A c L h hST hq
  · exact hL3 G A c L h hST hq hO2 hm hO (Or.inl hL)
  · exact hL3 G A c L h hST hq hO2 hm hO (Or.inr hSL)
  · exact hA7 G A c L h hST hq hO2 hm hO hA
  · exact hA7Z3 G A c L h hST hq hO2 hm hO hAZ

end CFSG.RankThree.PartTwo.Sec13
