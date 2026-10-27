module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpTorusWeight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6Smith
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotOrthSL2
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeBlocks
import CFSG.LieType.Steinberg.BruhatWeyl
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpMono
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.CharacterTheory.Semidihedral.OddFieldLift
import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
import CFSG.LieType.Chevalley.C2E6StandardFixedData
import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
import CFSG.LieType.CurtisTits.SpecialLinear
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7Split
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeModel
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.Walter.JRFacts

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5 CFSG.StandardType
open CFSG.ClassicalInvolution.Models.SymplecticPairs (shortBlock longBlock)
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.SeitzReduction.LinearPilot (diagUnit)
open scoped MatrixGroups

private def spRS_longVec (n : ℕ) (k : Fin n) : Fin n → ℤ := fun a =>
  if a.val < k.val then 0 else if a.val + 1 < n then 2 else 1

private theorem spRS_toStd_longVec {n : ℕ} (k : Fin n) :
    toStd n (spRS_longVec n k) = 2 • Pi.single k 1 := by
  funext x
  simp only [toStd, spRS_longVec, Pi.smul_apply, Pi.single_apply, Fin.ext_iff, nsmul_eq_mul,
    Nat.cast_ofNat]
  split_ifs <;> omega

private theorem spRS_longVec_mem_roots {K : Type} [Field K] {n : ℕ} (k : Fin n) :
    spRS_longVec n k ∈ (rootDatum n K).roots :=
  mem_roots_of_stdVec (r := .positiveLong k) (spRS_toStd_longVec k).symm

private theorem spRS_longVec_ht_pos {K : Type} [Field K] {n : ℕ} (k : Fin n) :
    0 < CFSG.LieType.Steinberg.ht (spRS_longVec n k) :=
  CFSG.LieType.Steinberg.ht_pos_of_nonneg (D := rootDatum n K)
    (spRS_longVec_mem_roots (K := K) k) (by
      intro a
      simp only [spRS_longVec]
      split_ifs <;> norm_num)

private theorem spRS_mat_diagHom {K : Type} [Field K] {n : ℕ} (t : Fin n → Kˣ) :
    mat n K (diagHom n K t) =
      Matrix.diagonal (Sum.elim (fun i => (t i : K)) (fun i => (((t i)⁻¹ : Kˣ) : K))) := by
  change mat n K (equivStatedSp n K (TauCeti.GLSymplecticFin.diagonal t)) =
    Matrix.diagonal (Sum.elim (fun i => (t i : K)) (fun i => (((t i)⁻¹ : Kˣ) : K)))
  exact mat_equiv_diagonal (F := K) t

private theorem spRS_diagSp_eq_diagHom {K : Type} [Field K] {n : ℕ} (t : Fin n → Kˣ) :
    CFSG.SeitzReduction.SymplecticPilot.diagSp K n t = diagHom n K t := by
  apply mat_injective
  rw [CFSG.SeitzReduction.SymplecticPilot.mat_diagSp, spRS_mat_diagHom]
  rfl

private theorem spRS_single_add_self {K : Type} [Field K] [CharP K 2] {ι : Type}
    [DecidableEq ι] (x : ι) :
    ((Pi.single x (1 : K) : ι → K)) + (Pi.single x (1 : K) : ι → K) = 0 := by
  funext a
  simp [Pi.add_apply, CharTwo.add_self_eq_zero]

private theorem spRS_long_transvection_col {K : Type} [Field K] [CharP K 2] {n : ℕ}
    (k : Fin n) (x : Fin n ⊕ Fin n) :
    Matrix.mulVec
      ((1 + Matrix.single (Sum.inl k) (Sum.inr k) (1 : K)) *
       (1 + Matrix.single (Sum.inr k) (Sum.inl k) (1 : K)) *
       (1 + Matrix.single (Sum.inl k) (Sum.inr k) (1 : K)))
      (Pi.single x (1 : K)) =
    (Pi.single (spMonoPerm 1 (spSgn k) x) (1 : K) : Fin n ⊕ Fin n → K) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rcases x with i | i <;>
    (by_cases hik : i = k <;>
      simp [-Matrix.mulVec_mulVec, -Matrix.mulVec_single, hik, Matrix.add_mulVec,
        Matrix.one_mulVec, Matrix.single_mulVec_eq, spMonoPerm, spFlip, spSgn,
        spRS_single_add_self, add_comm, add_left_comm, ← add_assoc])

private theorem spRS_long_transvection_prod {K : Type} [Field K] [CharP K 2] {n : ℕ}
    (k : Fin n) :
    (1 + Matrix.single (Sum.inl k) (Sum.inr k) (1 : K)) *
    (1 + Matrix.single (Sum.inr k) (Sum.inl k) (1 : K)) *
    (1 + Matrix.single (Sum.inl k) (Sum.inr k) (1 : K)) =
    Equiv.Perm.permMatrix K (spMonoPerm 1 (spSgn k)).symm := by
  let M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
    (1 + Matrix.single (Sum.inl k) (Sum.inr k) (1 : K)) *
    (1 + Matrix.single (Sum.inr k) (Sum.inl k) (1 : K)) *
    (1 + Matrix.single (Sum.inl k) (Sum.inr k) (1 : K))
  change M = Equiv.Perm.permMatrix K (spMonoPerm 1 (spSgn k)).symm
  have hcol : ∀ b : Fin n ⊕ Fin n,
      M.col b = Pi.single (spMonoPerm 1 (spSgn k) b) (1 : K) := by
    intro b
    rw [← Matrix.mulVec_single_one]
    exact spRS_long_transvection_col (K := K) k b
  apply Matrix.ext
  intro a b
  rw [show M a b = (M.col b) a from rfl, congrFun (hcol b) a]
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Pi.single_apply, Equiv.symm_apply_eq]

theorem shortBlock_sl2Upper_mem_U {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    {k : Fin n} (hk : k.val + 1 < n) (c : K) :
    shortBlock K (ne_succ' hk) (sl2Upper c) ∈ (spCurtisDatum n K).U := by
  refine (spCurtisDatum n K).X_le k ?_
  rw [mem_X_iff]
  exact ⟨c, by
    rw [CFSG.ClassicalInvolution.Models.SymplecticPairs.shortBlock_sl2Upper, simpleIdx,
      dif_pos hk]⟩

theorem shortBlock_sl2Lower_mem_L {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    {k : Fin n} (hk : k.val + 1 < n) (c : K) :
    shortBlock K (ne_succ' hk) (sl2Lower c) ∈ (spCurtisDatum n K).L := by
  refine (spCurtisDatum n K).Y_le k ?_
  rw [spCurtisDatum_Y, CFSG.ClassicalInvolution.Models.SymplecticPairs.shortBlock_sl2Lower]
  exact elt_mem_rootGroup (F := K) (stdVec_shortNeg_eq hk) c

theorem shortBlock_diagUnit_eq_corootSp {K : Type} [Field K] {n : ℕ} {k : Fin n}
    (hk : k.val + 1 < n) (u : Kˣ) :
    shortBlock K (ne_succ' hk) (diagUnit u) = corootSp k u := by
  rw [CFSG.SeitzReduction.SymplecticPilot.shortBlock_diagUnit (ne_succ' hk) u,
    spRS_diagSp_eq_diagHom, corootSp_apply]
  congr 1
  funext a
  simp only [CFSG.SeitzReduction.SymplecticPilot.shortParam, corootVec]
  by_cases ha : a = k
  · subst ha
    simp
  · by_cases hb : a = ⟨k.val + 1, hk⟩
    · subst hb
      simp [ha]
    · have hb' : ¬a.val = k.val + 1 := fun h => hb (Fin.ext h)
      simp [ha, hb, hb']

theorem shortBlock_weyl_eq_n {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {k : Fin n}
    (hk : k.val + 1 < n) :
    shortBlock K (ne_succ' hk) (sl2Upper 1 * sl2Lower (-1) * sl2Upper 1) =
      (spCurtisDatum n K).n k := by
  rw [spCurtisDatum_n, weylRep_eq_short hk, map_mul, map_mul,
    CFSG.ClassicalInvolution.Models.SymplecticPairs.shortBlock_sl2Upper,
    CFSG.ClassicalInvolution.Models.SymplecticPairs.shortBlock_sl2Lower]

theorem longBlock_sl2Upper_mem_U {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (k : Fin n) (c : K) : longBlock K n k (sl2Upper c) ∈ (spCurtisDatum n K).U := by
  rw [CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlock_sl2Upper]
  exact CFSG.LieType.Steinberg.rootGroup_le_posUnipotent (D := rootDatum n K)
    (spRS_longVec_mem_roots (K := K) k) (spRS_longVec_ht_pos (K := K) k)
    (elt_mem_rootGroup (F := K) (r := .positiveLong k) (spRS_toStd_longVec k).symm c)

theorem longBlock_sl2Lower_mem_L {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (k : Fin n) (c : K) : longBlock K n k (sl2Lower c) ∈ (spCurtisDatum n K).L := by
  rw [CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlock_sl2Lower]
  have hr : stdVec (.negativeLong k) = toStd n (-(spRS_longVec n k)) := by
    change -(2 • Pi.single k 1) = toStd n (-(spRS_longVec n k))
    rw [toStd_neg', spRS_toStd_longVec]
  have hmem : -(spRS_longVec n k) ∈ (rootDatum n K).roots :=
    mem_roots_of_stdVec (r := .negativeLong k) hr
  have hneg : CFSG.LieType.Steinberg.ht (-(spRS_longVec n k)) < 0 :=
    CFSG.LieType.Steinberg.ht_neg_of_nonpos (D := rootDatum n K) hmem (by
      intro a
      change -(if a.val < k.val then (0 : ℤ) else if a.val + 1 < n then 2 else 1) ≤ 0
      split_ifs <;> norm_num)
  exact CFSG.LieType.Steinberg.rootGroup_le_negUnipotent (D := rootDatum n K) hmem hneg
    (elt_mem_rootGroup (F := K) (r := .negativeLong k) hr c)

theorem longBlock_diagUnit_eq_diagHom {K : Type} [Field K] {n : ℕ} (k : Fin n) (u : Kˣ) :
    longBlock K n k (diagUnit u) = diagHom n K (Pi.mulSingle k u) := by
  have h : longBlock K n k (diagUnit u) =
      CFSG.SeitzReduction.SymplecticPilot.rootTorusHom K n k u :=
    (CFSG.SeitzReduction.SymplecticPilot.rootTorusHom_eq_longBlock k u).symm
  rw [h, CFSG.SeitzReduction.SymplecticPilot.rootTorusHom_apply, spRS_diagSp_eq_diagHom]

theorem mat_longBlock_weyl {K : Type} [Field K] [CharP K 2] {n : ℕ} (k : Fin n) :
    mat n K (longBlock K n k (sl2Upper 1 * sl2Lower (-1) * sl2Upper 1)) =
      Equiv.Perm.permMatrix K (spMonoPerm 1 (spSgn k)).symm := by
  have hprod : longBlock K n k (sl2Upper 1 * sl2Lower (-1) * sl2Upper 1) =
      longBlock K n k (sl2Upper 1) * longBlock K n k (sl2Lower (-1)) *
        longBlock K n k (sl2Upper 1) := by
    rw [map_mul, map_mul]
  rw [hprod, map_mul, map_mul,
    CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlock_sl2Upper,
    CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlock_sl2Lower,
    mat_elt_positiveLong, mat_elt_negativeLong,
    show (-1 : K) = 1 from CharTwo.neg_eq 1]
  simp only [Matrix.transvection]
  exact spRS_long_transvection_prod k

end CFSG.LocalAnalysis.WeakClosure81
