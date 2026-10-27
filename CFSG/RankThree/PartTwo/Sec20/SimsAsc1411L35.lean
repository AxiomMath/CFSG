module

public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411Tools
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411L35Group
import CFSG.RankThree.PartTwo.KFacts.L34Sections
import CFSG.Models.PGLSimple
import CFSG.RankThree.SteinbergR3ELinearRegularUnipotent

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

variable {X : Type} [Group X] [Finite X] {L S : Subgroup X}

theorem nonempty_mulEquiv_projectiveSL_of_L3_5 {G : Type*} [Group G] [Fact (Nat.Prime 5)]
    (hL : Nonempty (G ≃* SL(3, GaloisField 5 1)) ∨
      Nonempty (G ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 5 1))) :
    Nonempty (G ≃* projectiveSL 3 (GaloisField 5 1)) := by
  rcases hL with hL | hL
  · exact ⟨hL.some.trans (MulEquiv.ofBijective (proj 3 (GaloisField 5 1))
      ⟨proj_injective_five, proj_surjective 3 _⟩)⟩
  · exact ⟨hL.some.trans (CFSG.RankThree.PartTwo.KFacts.L34.projSLEquivProjectiveSL 3 _)⟩

theorem noSmall1411_of_L3_5 [Fact (Nat.Prime 5)] (h : Hyp1411 X L S)
    (hL : Nonempty (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≃*
      projectiveSL 3 (GaloisField 5 1))) :
    NoSmall1411 X L S := by
  obtain ⟨ε⟩ := hL
  have : IsSimpleGroup (projectiveSL 3 (GaloisField 5 1)) := by
    have := CFSG.PGLModel.isSimpleGroup_projSL_of_two_le (n := 3) (GaloisField 5 1)
      (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))
    exact (CFSG.RankThree.PartTwo.KFacts.L34.projSLEquivProjectiveSL 3 _).symm.isSimpleGroup
  have hsimp : IsSimpleGroup ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) :=
    ε.isSimpleGroup
  have hZ : Subgroup.center ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) = ⊥ := by
    have e := Subgroup.map_center_eq ε
    rw [CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot le_rfl] at e
    exact (Subgroup.map_eq_bot_iff_of_injective _ ε.injective).mp e
  refine noSmall1411_of_forall_excl h hsimp hZ fun α hα => Excl1411.of_congr ε ?_
  exact excl1411_L3_5 _ (by rw [MulEquiv.orderOf_eq]; exact hα)

theorem asc82Item1411_L3_5 (X : Type) [Group X] [Finite X] (L S : Subgroup X)
    [Fact (Nat.Prime 5)] (h : Hyp1411 X L S)
    (hL : Nonempty (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 5 1)))
    (hS : IsCyclic ↥(S.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)))) :
    ∃ i₁ i₂ : Fin 4, i₁ ≠ i₂ ∧ i₁ ≠ 3 ∧ i₂ ≠ 3 ∧ (Sec18.fourChar S i₁).Normal ∧
      (Sec18.fourChar S i₂).Normal :=
  asc82Item1411_of_noSmall h (relIndex_pCore_le_two_of_isCyclic h hS)
    (noSmall1411_of_L3_5 h (nonempty_mulEquiv_projectiveSL_of_L3_5 (Or.inr hL)))

theorem asc82Item1411_L3_5_pRank (X : Type) [Group X] [Finite X] (L S : Subgroup X)
    [Fact (Nat.Prime 5)] (h : Hyp1411 X L S)
    (hL : Nonempty (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≃*
        SL(3, GaloisField 5 1)) ∨
      Nonempty (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≃*
        CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 5 1)))
    (hS : CFSG.pRank 2 ↥(S.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) ≤ 1) :
    ∃ i₁ i₂ : Fin 4, i₁ ≠ i₂ ∧ i₁ ≠ 3 ∧ i₂ ≠ 3 ∧ (Sec18.fourChar S i₁).Normal ∧
      (Sec18.fourChar S i₂).Normal :=
  asc82Item1411_of_noSmall h (relIndex_pCore_le_two_of_pRank_le_one h hS)
    (noSmall1411_of_L3_5 h (nonempty_mulEquiv_projectiveSL_of_L3_5 hL))

end CFSG.RankThree.PartTwo.Sec20
