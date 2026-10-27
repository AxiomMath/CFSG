module

public import CFSG.LocalAnalysis.StandardType.GGE6InnerDiagBoundThreeProof
public import CFSG.LocalAnalysis.StandardType.GGIOneExcFacts
public import CFSG.LocalAnalysis.StandardType.GGIOneExcOuterE6
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperMore

public section

namespace CFSG.StandardType.SmallExc

open CFSG.Assembly


theorem ggInnerDiagBound_E6_three {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) (h3 : 3 ∣ 2 ^ n - 1) :
    GGInnerDiagBound 3 5 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K) := by
  intro Eb Eh hEbI hEb h5 h27 hle hEh hcard hnot
  obtain ⟨φ, hφEh, hφI⟩ := Set.not_subset.1 hnot
  have h3n : 3 ∣ n := ggE6OuterThreeInput_holds K n hn hK h3 φ (hEh.2 φ hφEh) hφI
  exact ggE6InnerDiagBoundThreeInput_holds K n hn hK h3 h3n Eb Eh hEbI hEb h5 h27 hle hEh hcard
    hnot

theorem ggINormAbove_E6_three {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) (h3 : 3 ∣ 2 ^ n - 1) :
    GGINormAbove 3 5 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K) :=
  fun X hXI hX h6 _ => ggE6ThreeRankSixTwoLocal_holds K n hn hK h3 X hXI hX h6

theorem largeEvenLabelAll_bstarEq_e6Three {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGIOneMoreE6ThreeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      (∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I) ∧
        ∃ r, GGTorusLift p r R ∧ GGINormAbove p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, rfl, h3⟩ := h
  dsimp only at htag h3 hlab
  subst htag
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hK, hQK, hl⟩ := TableBExc.recipeChevalleyE6_torusLift_three h3 hQ
  exact ⟨K, inferInstance, inferInstance, hK, hQK, ⟨5, hl, ggInnerDiagBound_E6_three hn hK h3⟩,
    5, hl, ggINormAbove_E6_three hn hK h3⟩

end CFSG.StandardType.SmallExc

end
