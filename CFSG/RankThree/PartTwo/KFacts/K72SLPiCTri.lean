module

public import CFSG.RankThree.PartTwo.KFacts.AutKindsStd
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
import CFSG.RankThree.PartTwo.Sec4.LThreePiKind

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial

theorem inducesStdKind_trichotomy_of_isSLThreePiAt {G : Type} [Group G] [Finite G]
    {L : Subgroup G} {n : ℕ} (hn : 1 ≤ n)
    (hL : Sec4.IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) (2 ^ (3 * n))) {x : G}
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) (hx3 : x ^ 3 = 1) :
    InducesStdKind L x .inner ∨ InducesStdKind L x .diagonal ∨ InducesStdKind L x .field := by
  obtain ⟨K, _, _, ⟨-, -, ⟨e₀⟩⟩ | ⟨hK, -, ⟨e₀⟩⟩⟩ := hL
  ·
    set e : L ⧸ aschbacherSolvableCore 3 L ≃* Matrix.SpecialLinearGroup (Fin 3) K :=
      e₀.trans (slPiTrueEquiv (2 ^ (3 * n)) K)
    rcases inducesKindSL_inner_or_diagonal_or_field L le_rfl hxN hx3 e with h | h | h
    · exact Or.inl (.sl 3 K le_rfl ⟨e, hxN, h⟩)
    · exact Or.inr (Or.inl (.sl 3 K le_rfl ⟨e, hxN, h⟩))
    · exact Or.inr (Or.inr (.sl 3 K le_rfl ⟨e, hxN, h⟩))
  ·
    have hU : UnitaryFieldData 2 (3 * n) K :=
      ⟨Nat.prime_two, by omega, by rw [hK, ← pow_mul, mul_comm]⟩
    have hq : 2 < 2 ^ (3 * n) :=
      lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ 3 * n))
    set e : L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2
        (3 * n) K 3 := e₀.trans (slPiFalseEquiv 2 (3 * n) K)
    rcases inducesKindSU3_inner_or_diagonal_or_field (h := hU) L hq hxN hx3 e with h | h | h
    · exact Or.inl (.su3 hU hq ⟨e, hxN, h⟩)
    · exact Or.inr (Or.inl (.su3 hU hq ⟨e, hxN, h⟩))
    · exact Or.inr (Or.inr (.su3 hU hq ⟨e, hxN, h⟩))

end CFSG.RankThree.PartTwo.KFacts
