module

public import CFSG.OddTranspositions.PartFour.ThirteenListExtTrialityOrthOtherPlus
import CFSG.Quasithin.Vol2.Ch11SecO6G
import CFSG.Quasithin.EmptyFaithful.S146zYOutComm
import CFSG.LocalAnalysis.WeakClosure81.W18ASNineOrthBridge
import CFSG.LieType.SeitzGeneration.StandardTypeOrthModel
import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.StatedOmegaScalars
import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinusSmall
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGroupProofsC

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Open
open CFSG.LieType.Universal.Spin (quadMinus nondegenerate_polarBilin_quadMinus_of_finite)
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinus
  (finrank_minusSpace_small exists_quadMinus_ne_zero_small nonempty_range_equiv_statedOmega)
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus
  (eq_one_of_mem_statedScalars_statedQuadMinus_omega)

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem statedScalars_subgroupOf_statedOmega_quadMinus_eq_bot_of_two_le {m : ℕ} (hm : 2 ≤ m)
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    (StatedScalars (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) F).subgroupOf
      (StatedOmega (StatedQuadMinus m F b c)) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  rw [Subgroup.mem_subgroupOf] at hA
  exact Subgroup.mem_bot.mpr (eq_one_of_mem_statedScalars_statedQuadMinus_omega hirr hm hA)

theorem outer_comm_commutator_orthogonalMinus_one {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    ∀ x y : Outer ↥(commutator ↥(CFSG.PGLModel.orthogonalMinus 1 F b c)), x * y = y * x := by
  obtain ⟨E, _, _, D, -, ρ, -, -, hinj, -, hcomm, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_actual_derived_extraction (quadMinus 2 F b c)
      (nondegenerate_polarBilin_quadMinus_of_finite 2 F hirr)
      (finrank_minusSpace_small (n := 2) (by norm_num))
      (fun U hU => exists_quadMinus_ne_zero_small hirr (by norm_num) U hU)
  obtain ⟨e⟩ := nonempty_range_equiv_statedOmega ρ hcomm
  have := D.finite_E
  have h4 : 4 ≤ Nat.card E := by
    rw [D.card_E]
    have h2 : 2 ≤ Nat.card F := Finite.one_lt_card
    nlinarith
  let eE : Matrix.SpecialLinearGroup (Fin 2) E ≃*
      ↥(commutator ↥(CFSG.PGLModel.orthogonalMinus 1 F b c)) :=
    ((MonoidHom.ofInjective hinj).trans e).trans
      (CFSG.LocalAnalysis.WeakClosure81.commutatorOrthogonalMinusEquiv 1 F b c).symm
  exact CFSG.Quasithin.S146zY.outer_comm_of_mulEquiv eE
    (CFSG.Quasithin.Vol2.Ch11.O6.outer_sl2_mul_comm E h4)

theorem outer_comm_of_mulEquiv_commutator_orthogonalMinus_two {X : Type} [Group X]
    (hs : IsSimpleGroup X) (hnc : ∃ a b : X, a * b ≠ b * a) {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (e : X ≃* ↥(commutator ↥(CFSG.PGLModel.orthogonalMinus 2 F b c))) :
    ∀ x y : Outer X, x * y = y * x := by
  let eX : X ≃* StatedProj (StatedOmega (StatedQuadMinus 3 F b c)) :=
    (e.trans (CFSG.LocalAnalysis.WeakClosure81.commutatorOrthogonalMinusEquiv 2 F b c)).trans
      (CFSG.RankThree.PartOne.KFU.equivProjOfScalarsBot _
        (statedScalars_subgroupOf_statedOmega_quadMinus_eq_bot_of_two_le (m := 3) (by norm_num)
          hirr))
  have hL : CFSG.Blueprint.LieModel X .PSU 4 2 n :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.kOmega6MinusU4_holds X n F b c hF hirr
      ⟨eX⟩
  have hm := hL.statedClassicalModel (by decide)
  have : Group.IsPerfect X := by
    have := hs
    refine TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative fun h => ?_
    obtain ⟨a, b, hab⟩ := hnc
    exact hab (h.is_comm.comm a b)
  have hodd : Nat.gcd 4 (2 ^ n + 1) = 1 := by
    have h2 : ¬ 2 ∣ 2 ^ n + 1 := by
      have hn : n ≠ 0 := by
        rintro rfl
        have := Finite.one_lt_card (α := F)
        rw [hF] at this
        simp at this
      have h1 : 2 ∣ 2 ^ n := dvd_pow_self 2 hn
      omega
    have hc : Nat.Coprime 2 (2 ^ n + 1) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2
    simpa using Nat.Coprime.pow_left 2 hc
  exact CFSG.Quasithin.H13.KGLieOut.outer_comm_psu hs hm hodd

theorem outer_comm_commutator_orthogonalMinus_of_three_le {k : ℕ} (hk : 3 ≤ k) {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    ∀ x y : Outer ↥(commutator ↥(CFSG.PGLModel.orthogonalMinus k F b c)), x * y = y * x := by
  let e : ↥(commutator ↥(CFSG.PGLModel.orthogonalMinus k F b c)) ≃*
      CFSG.Assembly.LargeEvenProj
        (CFSG.Assembly.LargeEvenOmega (CFSG.Assembly.LargeEvenQMinus k b c)) :=
    ((CFSG.LocalAnalysis.WeakClosure81.commutatorOrthogonalMinusEquiv k F b c).trans
      (CFSG.RankThree.PartOne.KFU.equivProjOfScalarsBot _
        (statedScalars_subgroupOf_statedOmega_quadMinus_eq_bot_of_two_le (m := k + 1) (by omega)
          hirr))).trans
      (CFSG.LieType.SeitzGeneration.standardTypeOmegaMinusEquiv k F b c).symm
  exact CFSG.Quasithin.S146zY.outer_comm_of_mulEquiv e.symm
    (outer_comm_of_ggOutComm
      (CFSG.StandardType.InndiagCommRest.ggOutComm_omegaMinus (n := k + 1) (by omega) hirr hF))

end CFSG.OddTranspositions.PartFour
