module

public import CFSG.Quasithin.Background.HStandard
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Open Subgroup
open scoped Matrix

variable {K : Type} [Field K] [Finite K]

theorem s16h_sl4_natNorm_transvection (hK : Nat.card K = 2 ^ 2) :
    ∃ s' : MulAut (StdMod (Fin 2) K),
      s' ∈ natNorm (CFSG.Assembly.LowTwoRank.StatedSL 2 K) ∧ s' ^ 2 = 1 ∧ s' ≠ 1 ∧
      rkIdx (fixV (Subgroup.zpowers s')) ≤ 2 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hKeven : Fintype.card K % 2 = 0 := by
    rw [Fintype.card_eq_nat_card, hK]
    norm_num
  have hchar : ringChar K = 2 := (FiniteField.even_card_iff_char_two (F := K)).mpr hKeven
  haveI : CharP K 2 := hchar ▸ ringChar.charP K
  let A : GL (Fin 2) K :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 1; 0, 1] (by simp [Matrix.det_fin_two])
  have hAval : (A : Matrix (Fin 2) (Fin 2) K) = !![1, 1; 0, 1] := rfl
  have hAdet : (A : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [hAval]
    simp [Matrix.det_fin_two]
  have hAmem : A ∈ CFSG.Assembly.LowTwoRank.StatedSL 2 K := Subgroup.subset_closure hAdet
  let s' : MulAut (StdMod (Fin 2) K) := matHom A
  have hs'mat : s' = matAut A := matHom_apply A
  have hs'mem : s' ∈ natNorm (CFSG.Assembly.LowTwoRank.StatedSL 2 K) := by
    have h1 : s' ∈ natImage (CFSG.Assembly.LowTwoRank.StatedSL 2 K) := by
      rw [natImage_eq_map]
      exact Subgroup.mem_map.mpr ⟨A, hAmem, rfl⟩
    have hle := Subgroup.le_normalizer (H := natImage (CFSG.Assembly.LowTwoRank.StatedSL 2 K))
    exact hle h1
  have hA2 : A ^ 2 = 1 := by
    rw [pow_two]
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rw [Matrix.GeneralLinearGroup.coe_mul, hAval]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  have hs'2 : s' ^ 2 = 1 := by
    change (matHom A) ^ 2 = 1
    rw [← map_pow, hA2, map_one]
  have hAne : A ≠ 1 := by
    intro hA1
    have h01 : (1 : K) = 0 := by
      simpa [hAval] using
        congrArg (fun B : GL (Fin 2) K => (B : Matrix (Fin 2) (Fin 2) K) 0 1) hA1
    exact one_ne_zero h01
  have hs'1 : s' ≠ 1 := by
    intro h
    apply hAne
    apply matHom_injective
    rw [← map_one matHom] at h
    exact h
  have hmulvec : ∀ v : Fin 2 → K,
      toAddMap s' v = (A : Matrix (Fin 2) (Fin 2) K) *ᵥ v := by
    intro v
    rw [hs'mat, toAddMap_matAut]
  have hA_mul : ∀ v : Fin 2 → K,
      (A : Matrix (Fin 2) (Fin 2) K) *ᵥ v = ![v 0 + v 1, v 1] := by
    intro v
    rw [hAval]
    ext i
    fin_cases i <;>
      simp [Matrix.mulVec, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail]
  have hfix : ∀ v : Fin 2 → K, toAddMap s' v = v ↔ v 1 = 0 := by
    intro v
    rw [hmulvec, hA_mul]
    constructor
    · intro h
      have h0 := congrFun h 0
      simp at h0
      exact h0
    · intro h
      funext i
      fin_cases i <;> simp [h]
  have hcard : Nat.card ↥(fixV (Subgroup.zpowers s')) = 2 ^ 2 := by
    rw [card_fixV_zpowers]
    have he : Nat.card {v : Fin 2 → K // toAddMap s' v = v} = Nat.card K :=
      Nat.card_congr
        { toFun := fun v => v.1 0
          invFun := fun x => ⟨![x, 0], by rw [hfix]; simp⟩
          left_inv := fun v => by
            apply Subtype.ext
            funext i
            fin_cases i
            · simp
            · have hv : v.1 1 = 0 := (hfix v.1).mp v.2
              simp [hv]
          right_inv := fun x => by simp }
    rw [he, hK]
  have hj : 2 ≤ 2 * Fintype.card (Fin 2) := by simp
  have hrk := rkIdx_fixV_of_card (ι := Fin 2) (K := K) (n := 2) hK s' hj hcard
  refine ⟨s', hs'mem, hs'2, hs'1, ?_⟩
  rw [hrk]
  simp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
