module

public import CFSG.LocalAnalysis.StandardType.GGTriD4KnownInputs
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitarySixThreeCases
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusProofClassical
public import CFSG.GroupTheory.BaerSuzuki
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.Asc83Table.Automizer
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSetting
public import CFSG.RankThree.PartOne.KC.UnitaryLiftBlocks
public import CFSG.RankThree.PartTwo.Late.GammaZero
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec13.Statements
public import CFSG.RankThree.PartTwo.Sec18.Notation
public import CFSG.RankThree.PartTwo.Sec18.Tools
public import CFSG.RankThree.PartTwo.Sec21.Item229Diagram
public import CFSG.RankThree.PartTwo.Sec21.Item23Tools
public import CFSG.RankThree.PartTwo.Sec21.Membership
public import CFSG.RankThree.PartTwo.Sec21.SylowThree
public import CFSG.RankThree.PartTwo.Sec4.Item47
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.StatementsGraphField
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.Sporadic.M23.M23Group
public import CFSG.StronglyEmbedded.ParityCriterion

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.PartOne.KCUnitaryModel

@[expose] def GGRawIThreeRankLe (b : ℕ) : LargeEvenRawCont :=
  fun R _ I _ => ∀ B : Subgroup (MulAut R), IsElemAbelian 3 B → (∀ x ∈ B, x ∈ I) →
    Nat.card B ≤ b

private theorem ggI1_congr_apply {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (f : MulAut X) (y : Y) : (MulAut.congr e f) y = e (f (e.symm y)) := rfl

private theorem ggI1_congr_symm_symm {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (f : MulAut X) : MulAut.congr e.symm (MulAut.congr e f) = f := by
  refine MulEquiv.ext fun x => ?_
  have h1 : (MulAut.congr e.symm (MulAut.congr e f)) x =
      e.symm ((MulAut.congr e f) (e x)) := by
    simpa using ggI1_congr_apply e.symm (MulAut.congr e f) x
  rw [h1, ggI1_congr_apply e f (e x), MulEquiv.symm_apply_apply e x]
  exact MulEquiv.symm_apply_apply e (f x)

private theorem ggI1_key {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) :
    GGRawIThreeRankLe 9
      (LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K (2 ^ n)))
        (LargeEvenGUSet (Fin 3) K (2 ^ n)))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 3) K (2 ^ n)))) := by
  have hn1 : 1 ≤ n := by omega
  have h : UnitaryFieldData 2 n K := unitaryFieldData_of_card hn1 hK
  have hK' : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
  have h3 : (3 : K) ≠ 0 :=
    CFSG.RankThree.PartTwo.Sec4.three_ne_zero_of_card Nat.prime_two (by norm_num) hK'
  intro B hB hBI
  let e := unitaryPSUEquiv h (by norm_num : 1 ≤ 3)
  let B' := B.map (MulAut.congr e.symm).toMonoidHom
  have hcard : Nat.card B' = Nat.card B :=
    Subgroup.card_map_of_injective (K := B) (MulAut.congr e.symm).injective
  have hB' : IsElemAbelian 3 B' :=
    CFSG.RankThree.PartTwo.Sec4.isElemAbelian_map (MulAut.congr e.symm).toMonoidHom hB
  have hB'N : B' ≤ (psuConj h).range := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨M, hM, hgraph⟩ := hBI x hx
    obtain ⟨u, hu⟩ := TableBU63.exists_unitary_of_gu h hM
    have hA : (Matrix.GeneralLinearGroup.scalar (Fin 3) u * M : GL (Fin 3) K) ∈ unitaryIsom3 h := by
      rw [mem_unitaryIsom3]
      have hmem := (mem_primeFormUnitary.mp hu)
      simpa only [idGram, Units.val_one, Matrix.mul_one] using hmem
    have hxeq : MulAut.congr e
        (psuConj h ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) u * M, hA⟩) = x := by
      refine MulEquiv.ext fun z => QuotientGroup.induction_on z fun g => ?_
      rw [ggI1_congr_apply]
      have hes : e.symm (QuotientGroup.mk g :
            CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ n) K)) = (g : unitaryPSU h 3) := by
        have h1 : (QuotientGroup.mk g :
              CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ n) K)) =
            e (unitaryProj h 3 g) :=
          (unitaryPSUEquiv_unitaryProj h (by norm_num : 1 ≤ 3) g).symm
        rw [h1, MulEquiv.symm_apply_apply]
        rfl
      rw [hes, psuConj_mk]
      have hemk : e ((suConj h ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) u * M, hA⟩ g :
            unitarySU 2 n K 3) : unitaryPSU h 3) =
          (QuotientGroup.mk (suConj h ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) u * M, hA⟩ g) :
            LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n))) :=
        unitaryPSUEquiv_unitaryProj h (by norm_num : 1 ≤ 3) _
      rw [hemk]
      have hrel : (Matrix.GeneralLinearGroup.scalar (Fin 3) u * M) * (g : GL (Fin 3) K) *
          (Matrix.GeneralLinearGroup.scalar (Fin 3) u * M)⁻¹ = M * (g : GL (Fin 3) K) * M⁻¹ := by
        rw [show (Matrix.GeneralLinearGroup.scalar (Fin 3) u * M) * (g : GL (Fin 3) K) *
              (Matrix.GeneralLinearGroup.scalar (Fin 3) u * M)⁻¹ =
            Matrix.GeneralLinearGroup.scalar (Fin 3) u * (M * (g : GL (Fin 3) K) * M⁻¹) *
              (Matrix.GeneralLinearGroup.scalar (Fin 3) u)⁻¹ by group]
        rw [(TypeA.PGLTor.commute_scalar u (M * (g : GL (Fin 3) K) * M⁻¹)).eq]
        group
      have hmem : (Matrix.GeneralLinearGroup.scalar (Fin 3) u * M) * (g : GL (Fin 3) K) *
          (Matrix.GeneralLinearGroup.scalar (Fin 3) u * M)⁻¹ ∈ LargeEvenSUGroup (Fin 3) K (2 ^ n) :=
        conj_mem_unitarySU hA g.2
      have hsu : (⟨(Matrix.GeneralLinearGroup.scalar (Fin 3) u * M) * (g : GL (Fin 3) K) *
            (Matrix.GeneralLinearGroup.scalar (Fin 3) u * M)⁻¹, hmem⟩ :
            ↥(LargeEvenSUGroup (Fin 3) K (2 ^ n))) =
          suConj h ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) u * M, hA⟩ g :=
        Subtype.ext (by rw [coe_suConj]; rfl)
      rw [← hsu]
      exact (hgraph g (⟨(Matrix.GeneralLinearGroup.scalar (Fin 3) u * M) * (g : GL (Fin 3) K) *
        (Matrix.GeneralLinearGroup.scalar (Fin 3) u * M)⁻¹, hmem⟩) hrel).symm
    refine ⟨⟨Matrix.GeneralLinearGroup.scalar (Fin 3) u * M, hA⟩, ?_⟩
    symm
    rw [← hxeq]
    exact ggI1_congr_symm_symm e (psuConj h ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) u * M, hA⟩)
  have hfin := CFSG.RankThree.PartTwo.Sec21.Item223CensusProof.card_le_nine_of_le_psuConj_range
    h3 B' hB' hB'N
  omega

theorem ggA2UnitaryIThreeRank_holds :
    ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → GGLabelA2 lab → lab.tag = .twA →
      LargeEvenLabelAll lab (GGRawIThreeRankLe 9) := by
  intro lab hlab hA2 htw
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hl, hn, hrow⟩ := hA2
  dsimp only at hl hn hrow htw
  subst hl
  subst htw
  rcases hrow with hA | htwA
  · exact absurd hA.1 (by decide)
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ
    exact recipeUnitary_and (fun K _ _ hK => ggI1_key hn hK) hQ

end CFSG.StandardType
