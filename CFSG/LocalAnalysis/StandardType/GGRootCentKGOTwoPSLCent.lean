module

public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSLFixed
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsBasic
import CFSG.LocalAnalysis.StandardType.GGLinearFusionSLCent
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotInvolutionCentralizer
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotInvolutionCentralizerBasic
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotInvolutionCentralizerLevi
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRoots
import CFSG.GroupTheory.CentralExtensionPGroup
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Nilpotent
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommSpOTwo
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentLinUnitParabLin
import CFSG.Certificates.CosetTableShort
import CFSG.ClassicalInvolution.Models.SymplecticPairs.Pairs
import CFSG.LieType.Multipliers.ProductKernel
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
import CFSG.LocalAnalysis.AGLEmbedding.IIIaResidualDefs
import CFSG.LocalAnalysis.AGLEmbedding.J3MSideDefs
import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympCover
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommSpAut
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
import CFSG.Quasithin.Background.A1cModuleCoprime
import CFSG.Quasithin.Background.A3Components
import CFSG.Quasithin.Background.A3Structure312
import CFSG.Quasithin.Background.OrderingMax
import CFSG.Quasithin.Vol2.Ch1Local
import CFSG.Sporadic.J4Base
import Certificates.Certificate10005
import Certificates.Certificate3007
import Certificates.Certificate8026Base

public section

namespace CFSG.StandardType.KGPSL

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
open CFSG.SeitzReduction.LinearPilot

variable {m : ℕ} {K : Type} [Field K]

noncomputable abbrev r₀ (hm : 1 ≤ m) : projectiveSL (m + 1) K :=
  proj (m + 1) K (AutPSL.rootInv hm)

noncomputable abbrev dualRootInv (hm : 1 ≤ m) : SpecialLinearGroup (Fin (m + 1)) K :=
  SpecialLinearGroup.transvection (F := K) (AutPSL.last_ne_zero hm).symm 1

noncomputable abbrev y₀ (hm : 1 ≤ m) : projectiveSL (m + 1) K :=
  proj (m + 1) K (dualRootInv hm)

@[expose] noncomputable def leviSL (hm : 1 ≤ m) :
    Subgroup (SpecialLinearGroup (Fin (m + 1)) K) :=
  (LinFusion.ggTransPlacement hm).blockDiag K ⊓
    Subgroup.centralizer ({dualRootInv hm} : Set (SpecialLinearGroup (Fin (m + 1)) K))

@[expose] noncomputable def radicalSL (hm : 1 ≤ m) :
    Subgroup (SpecialLinearGroup (Fin (m + 1)) K) :=
  (LinFusion.ggTransPlacement hm).radical K

@[expose] noncomputable def leviFull (hm : 1 ≤ m) : Subgroup (projectiveSL (m + 1) K) :=
  Subgroup.centralizer {r₀ hm} ⊓ Subgroup.centralizer {y₀ hm}

@[expose] noncomputable def radical (hm : 1 ≤ m) : Subgroup (projectiveSL (m + 1) K) :=
  (radicalSL hm).map (proj (m + 1) K)

theorem mem_radicalSL {hm : 1 ≤ m} {B : SpecialLinearGroup (Fin (m + 1)) K} :
    B ∈ radicalSL hm ↔ ∀ i j, (LinFusion.ggTransPlacement hm).level j ≤
      (LinFusion.ggTransPlacement hm).level i → (B : Matrix (Fin (m + 1)) (Fin (m + 1)) K) i j =
        (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K) i j :=
  InvPlacement.mem_radical (LinFusion.ggTransPlacement hm)

theorem ggTransPlacement_mat_eq_rootInv (hm : 1 ≤ m) :
    (LinFusion.ggTransPlacement hm).mat K = AutPSL.rootInv hm :=
  (LinFusion.ggTransPlacement_mat (F := K) hm).trans (AutPSL.ggInvSL_eq_rootInv hm)

theorem rootInv_mul_self [CharP K 2] (hm : 1 ≤ m) :
    AutPSL.rootInv (K := K) hm * AutPSL.rootInv (K := K) hm =
      (1 : SpecialLinearGroup (Fin (m + 1)) K) :=
  InvPlacement.transvection_mul_self (AutPSL.last_ne_zero hm) (1 : K)

theorem radicalSL_le_centralizer (hm : 1 ≤ m) :
    radicalSL hm ≤ Subgroup.centralizer
      ({AutPSL.rootInv (K := K) hm} : Set (SpecialLinearGroup (Fin (m + 1)) K)) := by
  rw [radicalSL, ← ggTransPlacement_mat_eq_rootInv]
  exact InvPlacement.radical_le_centralizer (LinFusion.ggTransPlacement hm)

theorem isPGroup_radicalSL [CharP K 2] (hm : 1 ≤ m) :
    IsPGroup 2 (radicalSL (K := K) hm) := by
  intro x
  refine ⟨2, Subtype.ext ?_⟩
  exact InvPlacement.radical_pow_four (LinFusion.ggTransPlacement hm) x.2

theorem level_eq_zero_iff_eq_last (hm : 1 ≤ m) {i : Fin (m + 1)} :
    (LinFusion.ggTransPlacement hm).level i = 0 ↔ i = Fin.last m := by
  rw [InvPlacement.level_eq_zero_iff]
  exact ⟨fun ⟨a, ha⟩ => ha.symm.trans (LinFusion.ggTransPlacement_u hm a),
    fun h => ⟨0, by rw [LinFusion.ggTransPlacement_u, h]⟩⟩

theorem level_eq_two_iff_eq_zero (hm : 1 ≤ m) {i : Fin (m + 1)} :
    (LinFusion.ggTransPlacement hm).level i = 2 ↔ i = 0 := by
  rw [InvPlacement.level_eq_two_iff]
  exact ⟨fun ⟨a, ha⟩ => ha.symm.trans (LinFusion.ggTransPlacement_w hm a),
    fun h => ⟨0, by rw [LinFusion.ggTransPlacement_w, h]⟩⟩

theorem level_eq_one_iff_free (hm : 1 ≤ m) {i : Fin (m + 1)} :
    (LinFusion.ggTransPlacement hm).level i = 1 ↔ i ∈ (LinFusion.ggTransPlacement hm).free :=
  (InvPlacement.mem_free (LinFusion.ggTransPlacement hm)).symm

theorem level_cases (hm : 1 ≤ m) (i : Fin (m + 1)) :
    (LinFusion.ggTransPlacement hm).level i = 0 ∨
      (LinFusion.ggTransPlacement hm).level i = 1 ∨
      (LinFusion.ggTransPlacement hm).level i = 2 := by
  have h := InvPlacement.level_le_two (LinFusion.ggTransPlacement hm) i
  omega

theorem blockDiag_mem_centralizer_dual (hm : 1 ≤ m)
    {B : SpecialLinearGroup (Fin (m + 1)) K}
    (hD : B ∈ (LinFusion.ggTransPlacement hm).blockDiag K)
    (hc : (B : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.last m) (Fin.last m) =
      (B : Matrix (Fin (m + 1)) (Fin (m + 1)) K) 0 0) :
    B ∈ Subgroup.centralizer
      ({dualRootInv hm} : Set (SpecialLinearGroup (Fin (m + 1)) K)) := by
  set P := LinFusion.ggTransPlacement hm with hP
  have hD' : ∀ i j, P.level i ≠ P.level j →
      (B : Matrix (Fin (m + 1)) (Fin (m + 1)) K) i j = 0 :=
    (InvPlacement.mem_blockDiag P).1 hD
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  change (B : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
      (1 + single (0 : Fin (m + 1)) (Fin.last m) 1) =
    (1 + single (0 : Fin (m + 1)) (Fin.last m) 1) *
      (B : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul]
  congr 1
  ext i j
  by_cases hj : j = Fin.last m
  · subst hj
    rw [Matrix.mul_single_apply_same, mul_one]
    by_cases hi : i = 0
    · subst hi
      rw [Matrix.single_mul_apply_same, one_mul, hc]
    · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hi]
      refine hD' i 0 ?_
      rw [hP]
      have h2 : (LinFusion.ggTransPlacement hm).level (0 : Fin (m + 1)) = 2 :=
        (level_eq_two_iff_eq_zero hm).2 rfl
      rw [h2]
      exact fun h => hi ((level_eq_two_iff_eq_zero hm).1 h)
  · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hj]
    by_cases hi : i = 0
    · subst hi
      rw [Matrix.single_mul_apply_same, one_mul]
      exact (hD' (Fin.last m) j (by
        rw [hP]
        have h0 : (LinFusion.ggTransPlacement hm).level (Fin.last m) = 0 :=
          (level_eq_zero_iff_eq_last hm).2 rfl
        rw [h0]
        exact fun h => hj ((level_eq_zero_iff_eq_last hm).1 h.symm))).symm
    · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hi]

theorem commute_dual_facts (hm : 1 ≤ m) {B : SpecialLinearGroup (Fin (m + 1)) K}
    (hB : B ∈ Subgroup.centralizer
      ({dualRootInv hm} : Set (SpecialLinearGroup (Fin (m + 1)) K))) :
    (B : Matrix (Fin (m + 1)) (Fin (m + 1)) K) 0 0 =
        (B : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.last m) (Fin.last m) ∧
      (∀ j, j ≠ Fin.last m →
        (B : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.last m) j = 0) ∧
      (∀ i, i ≠ 0 → (B : Matrix (Fin (m + 1)) (Fin (m + 1)) K) i 0 = 0) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hB
  have h := congrArg (fun X : SpecialLinearGroup (Fin (m + 1)) K =>
    (X : Matrix (Fin (m + 1)) (Fin (m + 1)) K)) hB
  change (B : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
      (1 + single (0 : Fin (m + 1)) (Fin.last m) 1) =
    (1 + single (0 : Fin (m + 1)) (Fin.last m) 1) *
      (B : Matrix (Fin (m + 1)) (Fin (m + 1)) K) at h
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul] at h
  have hE : (B : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
      single (0 : Fin (m + 1)) (Fin.last m) 1 =
      single (0 : Fin (m + 1)) (Fin.last m) 1 *
        (B : Matrix (Fin (m + 1)) (Fin (m + 1)) K) := add_left_cancel h
  refine ⟨?_, ?_, ?_⟩
  · have h1 := congrFun (congrFun hE 0) (Fin.last m)
    rwa [Matrix.mul_single_apply_same, mul_one, Matrix.single_mul_apply_same, one_mul] at h1
  · intro j hj
    have h1 := congrFun (congrFun hE 0) j
    rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hj, Matrix.single_mul_apply_same,
      one_mul] at h1
    exact h1.symm
  · intro i hi
    have h1 := congrFun (congrFun hE i) (Fin.last m)
    rw [Matrix.mul_single_apply_same, mul_one, Matrix.single_mul_apply_of_ne _ _ _ _ _ hi] at h1
    exact h1

theorem mem_leviSL {hm : 1 ≤ m} {B : SpecialLinearGroup (Fin (m + 1)) K} :
    B ∈ leviSL hm ↔
      B ∈ (LinFusion.ggTransPlacement hm).blockDiag K ∧
        B ∈ Subgroup.centralizer
          ({dualRootInv hm} : Set (SpecialLinearGroup (Fin (m + 1)) K)) :=
  Subgroup.mem_inf

theorem leviSL_le_centralizer (hm : 1 ≤ m) :
    leviSL hm ≤ Subgroup.centralizer
      ({AutPSL.rootInv (K := K) hm} : Set (SpecialLinearGroup (Fin (m + 1)) K)) := by
  intro B hB
  obtain ⟨hD, hd⟩ := mem_leviSL.1 hB
  obtain ⟨hcorner, -, -⟩ := commute_dual_facts hm hd
  rw [← ggTransPlacement_mat_eq_rootInv, InvPlacement.mem_centralizer_mat_iff]
  refine ⟨InvPlacement.blockDiag_le_parabolic (LinFusion.ggTransPlacement hm) hD,
    fun a b => ?_⟩
  have ha : a = (0 : Fin 1) := Subsingleton.elim a 0
  have hb : b = (0 : Fin 1) := Subsingleton.elim b 0
  subst ha hb
  rw [LinFusion.ggTransPlacement_u, LinFusion.ggTransPlacement_w]
  exact hcorner

theorem centralizer_inf_centralizer_eq_leviSL (hm : 1 ≤ m) :
    Subgroup.centralizer
        ({AutPSL.rootInv (K := K) hm} : Set (SpecialLinearGroup (Fin (m + 1)) K)) ⊓
        Subgroup.centralizer ({dualRootInv hm} :
          Set (SpecialLinearGroup (Fin (m + 1)) K)) = leviSL hm := by
  refine le_antisymm ?_ ?_
  · intro B hB
    obtain ⟨hB0, hBd⟩ := Subgroup.mem_inf.1 hB
    obtain ⟨hcorner, hrow, hcol⟩ := commute_dual_facts hm hBd
    refine mem_leviSL.2 ⟨?_, hBd⟩
    rw [InvPlacement.mem_blockDiag]
    obtain ⟨hBT, -⟩ := (InvPlacement.mem_centralizer_mat_iff
      (LinFusion.ggTransPlacement hm)).1 (by
        rwa [← ggTransPlacement_mat_eq_rootInv] at hB0)
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · rcases level_cases hm i with hi | hi | hi
      ·
        have hi' : i = Fin.last m := (level_eq_zero_iff_eq_last hm).1 hi
        subst hi'
        refine hrow j ?_
        intro hj
        subst hj
        exact absurd h (lt_irrefl _)
      ·
        have hj2 : (LinFusion.ggTransPlacement hm).level j = 2 := by
          have := InvPlacement.level_le_two (LinFusion.ggTransPlacement hm) j
          omega
        have hj' : j = 0 := (level_eq_two_iff_eq_zero hm).1 hj2
        subst hj'
        refine hcol i ?_
        intro hi0
        subst hi0
        have h02 : (LinFusion.ggTransPlacement hm).level (0 : Fin (m + 1)) = 2 :=
          (level_eq_two_iff_eq_zero hm).2 rfl
        omega
      ·
        have := InvPlacement.level_le_two (LinFusion.ggTransPlacement hm) j
        omega
    · exact hBT h
  · intro B hB
    obtain ⟨hD, hd⟩ := mem_leviSL.1 hB
    obtain ⟨hcorner, -, -⟩ := commute_dual_facts hm hd
    refine Subgroup.mem_inf.2 ⟨?_, hd⟩
    rw [← ggTransPlacement_mat_eq_rootInv, InvPlacement.mem_centralizer_mat_iff]
    refine ⟨InvPlacement.blockDiag_le_parabolic (LinFusion.ggTransPlacement hm) hD,
      fun a b => ?_⟩
    have ha : a = (0 : Fin 1) := Subsingleton.elim a 0
    have hb : b = (0 : Fin 1) := Subsingleton.elim b 0
    subst ha hb
    rw [LinFusion.ggTransPlacement_u, LinFusion.ggTransPlacement_w]
    exact hcorner

private noncomputable def blockDiagPart {m : ℕ} (P : InvPlacement (m + 1) 1)
    (B : SpecialLinearGroup (Fin (m + 1)) K) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
  Matrix.of fun i j => if P.level i = P.level j then
    (B : Matrix (Fin (m + 1)) (Fin (m + 1)) K) i j else 0

private theorem blockDiagPart_apply {m : ℕ} (P : InvPlacement (m + 1) 1)
    (B : SpecialLinearGroup (Fin (m + 1)) K) (i j : Fin (m + 1)) :
    blockDiagPart P B i j = if P.level i = P.level j then
      (B : Matrix (Fin (m + 1)) (Fin (m + 1)) K) i j else 0 :=
  rfl

theorem centralizer_mat_eq_sup (hm : 1 ≤ m) :
    Subgroup.centralizer
        ({AutPSL.rootInv (K := K) hm} : Set (SpecialLinearGroup (Fin (m + 1)) K)) =
      radicalSL hm ⊔ leviSL hm := by
  set P := LinFusion.ggTransPlacement hm with hP
  refine le_antisymm ?_ ?_
  · intro B hB
    obtain ⟨hBT, hBuw⟩ := (InvPlacement.mem_centralizer_mat_iff P).1 (by
      rwa [← ggTransPlacement_mat_eq_rootInv] at hB)
    have hcorner : (B : Matrix (Fin (m + 1)) (Fin (m + 1)) K) 0 0 =
        (B : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.last m) (Fin.last m) := by
      have h := hBuw 0 0
      rwa [LinFusion.ggTransPlacement_u, LinFusion.ggTransPlacement_w] at h
    set d : Matrix (Fin (m + 1)) (Fin (m + 1)) K := blockDiagPart P B with hd
    have hdT : d.BlockTriangular P.level := by
      intro i j hij
      rw [hd, blockDiagPart_apply, if_neg (fun h => hij.ne h.symm)]
    have h1 : d (P.u 0) (P.u 0) =
        (B : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (P.u 0) (P.u 0) := by
      rw [hd, blockDiagPart_apply, if_pos rfl]
    have h2 : d.submatrix (Subtype.val : P.free → Fin (m + 1))
        (Subtype.val : P.free → Fin (m + 1)) =
        (B : Matrix (Fin (m + 1)) (Fin (m + 1)) K).submatrix
          (Subtype.val : P.free → Fin (m + 1)) (Subtype.val : P.free → Fin (m + 1)) := by
      ext i j
      rw [Matrix.submatrix_apply, Matrix.submatrix_apply, hd, blockDiagPart_apply,
        if_pos (by rw [(InvPlacement.mem_free P).1 i.2, (InvPlacement.mem_free P).1 j.2])]
    have h3 : d (P.w 0) (P.w 0) =
        (B : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (P.w 0) (P.w 0) := by
      rw [hd, blockDiagPart_apply, if_pos rfl]
    have hdetd : d.det = (B : Matrix (Fin (m + 1)) (Fin (m + 1)) K).det := by
      rw [LinFusion.det_eq_of_blockTriangular_one P hdT,
        LinFusion.det_eq_of_blockTriangular_one P hBT, h1, h2, h3]
    have hdet : d.det = 1 := by
      rw [hdetd, Matrix.SpecialLinearGroup.det_coe]
    let dSL : SpecialLinearGroup (Fin (m + 1)) K := ⟨d, hdet⟩
    have hcoe : ((dSL : SpecialLinearGroup (Fin (m + 1)) K) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) K) = d := rfl
    have hdSLD : dSL ∈ P.blockDiag K := by
      rw [InvPlacement.mem_blockDiag]
      intro i j hij
      rw [hcoe, hd, blockDiagPart_apply, if_neg hij]
    have hcd : ((dSL : SpecialLinearGroup (Fin (m + 1)) K) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.last m) (Fin.last m) =
        ((dSL : SpecialLinearGroup (Fin (m + 1)) K) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) K) 0 0 := by
      rw [hcoe, hd, blockDiagPart_apply, blockDiagPart_apply, if_pos rfl, if_pos rfl]
      exact hcorner.symm
    have hdSL : dSL ∈ leviSL hm :=
      mem_leviSL.2 ⟨hdSLD, blockDiag_mem_centralizer_dual hm hdSLD hcd⟩
    have hu : B * dSL⁻¹ ∈ radicalSL hm := by
      rw [mem_radicalSL]
      intro i j hij
      have hinvD : ∀ k, (LinFusion.ggTransPlacement hm).level k ≠
          (LinFusion.ggTransPlacement hm).level j →
          ((dSL⁻¹ : SpecialLinearGroup (Fin (m + 1)) K) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) K) k j = 0 := fun k hk =>
        (InvPlacement.mem_blockDiag P).1 ((P.blockDiag K).inv_mem hdSLD) k j hk
      have hY : ∀ k, ¬((LinFusion.ggTransPlacement hm).level i <
          (LinFusion.ggTransPlacement hm).level k) →
          ((B : Matrix (Fin (m + 1)) (Fin (m + 1)) K) - d) i k = 0 := by
        intro k hk
        rw [Matrix.sub_apply, hd, blockDiagPart_apply]
        by_cases hik : (LinFusion.ggTransPlacement hm).level i =
            (LinFusion.ggTransPlacement hm).level k
        · rw [if_pos hik, sub_self]
        · rw [if_neg hik]
          have hle : (LinFusion.ggTransPlacement hm).level k <
              (LinFusion.ggTransPlacement hm).level i := by
            rcases lt_or_gt_of_ne hik with hlt | hgt
            · exact absurd hlt hk
            · exact hgt
          rw [hBT hle, sub_zero]
      have hsum1 : (d * ((dSL⁻¹ : SpecialLinearGroup (Fin (m + 1)) K) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) K)) i j = (1 : Matrix _ _ K) i j := by
        rw [← hcoe, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.SpecialLinearGroup.coe_one]
      have hsum2 : (((B : Matrix (Fin (m + 1)) (Fin (m + 1)) K) - d) *
            ((dSL⁻¹ : SpecialLinearGroup (Fin (m + 1)) K) :
              Matrix (Fin (m + 1)) (Fin (m + 1)) K)) i j = 0 := by
        rw [Matrix.mul_apply]
        refine Finset.sum_eq_zero fun k _ => ?_
        by_cases hk : (LinFusion.ggTransPlacement hm).level i <
            (LinFusion.ggTransPlacement hm).level k
        · have hne : (LinFusion.ggTransPlacement hm).level k ≠
              (LinFusion.ggTransPlacement hm).level j := by omega
          rw [hinvD k hne, mul_zero]
        · rw [hY k hk, zero_mul]
      rw [Matrix.SpecialLinearGroup.coe_mul]
      have hBsum : (B : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
          d + ((B : Matrix (Fin (m + 1)) (Fin (m + 1)) K) - d) := by
        rw [add_sub_cancel]
      rw [hBsum, Matrix.add_mul, Matrix.add_apply, hsum1, hsum2, add_zero]
    have hEq : B = (B * dSL⁻¹) * dSL := by group
    rw [hEq]
    exact Subgroup.mul_mem _
      ((le_sup_left : radicalSL hm ≤ radicalSL hm ⊔ leviSL hm) hu)
      ((le_sup_right : leviSL hm ≤ radicalSL hm ⊔ leviSL hm) hdSL)
  · exact sup_le (radicalSL_le_centralizer hm) (leviSL_le_centralizer hm)

theorem disjoint_radicalSL_leviSL (hm : 1 ≤ m) :
    Disjoint (radicalSL (K := K) hm) (leviSL (K := K) hm) := by
  rw [disjoint_iff]
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxR, hxL⟩ := Subgroup.mem_inf.1 hx
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_one]
  have hR := (mem_radicalSL (K := K)).1 hxR i j
  have hD := (InvPlacement.mem_blockDiag (LinFusion.ggTransPlacement hm)).1
    (mem_leviSL.1 hxL).1 i j
  by_cases hij : (LinFusion.ggTransPlacement hm).level i =
      (LinFusion.ggTransPlacement hm).level j
  · exact hR (le_of_eq hij.symm)
  · have hne : i ≠ j := fun h => hij (by rw [h])
    rw [hD hij, Matrix.one_apply_ne hne]

theorem scalars_le_leviSL (hm : 1 ≤ m) :
    scalars (m + 1) K ≤ leviSL (K := K) hm := by
  intro z hz
  obtain ⟨c, -, hcoe⟩ := mem_scalars.1 hz
  refine mem_leviSL.2 ⟨?_, ?_⟩
  · rw [InvPlacement.mem_blockDiag]
    intro i j hij
    rw [hcoe, Matrix.scalar_apply, Matrix.diagonal_apply]
    by_cases h : i = j
    · exact absurd (by rw [h]) hij
    · rw [if_neg h]
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_center_iff.mp (scalars_le_center (m + 1) K hz) _).symm

private theorem scalars_le_centralizer (hm : 1 ≤ m) (T : SpecialLinearGroup (Fin (m + 1)) K) :
    scalars (m + 1) K ≤ Subgroup.centralizer
      ({T} : Set (SpecialLinearGroup (Fin (m + 1)) K)) := by
  intro z hz
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_center_iff.mp (scalars_le_center (m + 1) K hz) T).symm

theorem leviSL_le_normalizer_radicalSL (hm : 1 ≤ m) :
    leviSL (K := K) hm ≤ Subgroup.normalizer
      ((radicalSL (K := K) hm) : Set (SpecialLinearGroup (Fin (m + 1)) K)) :=
  le_trans inf_le_left (le_trans
    (InvPlacement.blockDiag_le_parabolic (LinFusion.ggTransPlacement hm))
    (InvPlacement.parabolic_le_normalizer_radical (LinFusion.ggTransPlacement hm)))

private theorem center_eq_one_of_sq_eq_one [CharP K 2] {z : SpecialLinearGroup (Fin (m + 1)) K}
    (hz : z ∈ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) K)) (hz2 : z ^ 2 = 1) :
    z = 1 := by
  have hzs : z ∈ scalars (m + 1) K := by rwa [scalars_eq_center]
  exact InvPlacement.eq_one_of_mem_scalars_of_mul_self hzs (by simpa [pow_two] using hz2)

theorem centralizer_rootInv_eq_map [CharP K 2] (hm : 1 ≤ m) :
    Subgroup.centralizer ({r₀ (K := K) hm} : Set (projectiveSL (m + 1) K)) =
      (Subgroup.centralizer ({AutPSL.rootInv (K := K) hm} :
        Set (SpecialLinearGroup (Fin (m + 1)) K))).map (proj (m + 1) K) := by
  have hker : (proj (m + 1) K).ker ≤
      Subgroup.center (SpecialLinearGroup (Fin (m + 1)) K) := by
    rw [ker_proj]
    exact scalars_le_center (m + 1) K
  have h := ggRCST_range_inf_centralizer (ψ := proj (m + 1) K) hker
    (fun z hz hz2 => center_eq_one_of_sq_eq_one hz hz2) (rootInv_mul_self hm)
  rwa [MonoidHom.range_eq_top.mpr (proj_surjective _ _), top_inf_eq] at h

private theorem centralizer_dualRootInv_eq_map [CharP K 2] (hm : 1 ≤ m) :
    Subgroup.centralizer ({y₀ (K := K) hm} : Set (projectiveSL (m + 1) K)) =
      (Subgroup.centralizer ({dualRootInv hm} :
        Set (SpecialLinearGroup (Fin (m + 1)) K))).map (proj (m + 1) K) := by
  have hker : (proj (m + 1) K).ker ≤
      Subgroup.center (SpecialLinearGroup (Fin (m + 1)) K) := by
    rw [ker_proj]
    exact scalars_le_center (m + 1) K
  have hT : dualRootInv hm * dualRootInv hm = 1 :=
    InvPlacement.transvection_mul_self (AutPSL.last_ne_zero hm).symm (1 : K)
  have h := ggRCST_range_inf_centralizer (ψ := proj (m + 1) K) hker
    (fun z hz hz2 => center_eq_one_of_sq_eq_one hz hz2) hT
  rwa [MonoidHom.range_eq_top.mpr (proj_surjective _ _), top_inf_eq] at h

private theorem map_inf_map_eq_of_ker_le {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) {A B : Subgroup G} (hA : f.ker ≤ A) :
    A.map f ⊓ B.map f = (A ⊓ B).map f := by
  refine le_antisymm ?_ (le_inf (Subgroup.map_mono inf_le_left)
    (Subgroup.map_mono inf_le_right))
  rintro x ⟨⟨a, ha, rfl⟩, ⟨b, hb, hb'⟩⟩
  have hmem : a⁻¹ * b ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hb', inv_mul_cancel]
  have hbA : b ∈ A := by
    have h := A.mul_mem ha (hA hmem)
    rwa [mul_inv_cancel_left] at h
  exact ⟨b, ⟨hbA, hb⟩, hb'⟩

private theorem disjoint_map_of_disjoint {G H : Type*} [Group G] [Group H] (f : G →* H)
    {A B : Subgroup G} (hB : f.ker ≤ B) (h : Disjoint A B) :
    Disjoint (A.map f) (B.map f) := by
  rw [Subgroup.disjoint_def] at h ⊢
  rintro x ⟨a, ha, rfl⟩ ⟨b, hb, hb'⟩
  have hmem : b⁻¹ * a ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hb', inv_mul_cancel]
  have haB : a ∈ B := by
    have hba : a = b * (b⁻¹ * a) := by group
    rw [hba]
    exact B.mul_mem hb (hB hmem)
  rw [h ha haB, map_one]

theorem leviFull_eq_map [CharP K 2] (hm : 1 ≤ m) :
    leviFull (K := K) hm =
      (leviSL (K := K) hm).map (proj (m + 1) K) := by
  rw [leviFull, centralizer_rootInv_eq_map hm, centralizer_dualRootInv_eq_map hm,
    map_inf_map_eq_of_ker_le (proj (m + 1) K) (proj_surjective _ _)
      (by rw [ker_proj]; exact scalars_le_centralizer hm (AutPSL.rootInv hm)),
    centralizer_inf_centralizer_eq_leviSL hm]

theorem centralizer_rootInv_eq_sup (hm : 2 ≤ m) [Finite K] [CharP K 2] :
    Subgroup.centralizer ({r₀ (K := K) (Nat.le_of_succ_le hm)} :
        Set (projectiveSL (m + 1) K)) =
      radical (K := K) (Nat.le_of_succ_le hm) ⊔
        leviFull (K := K) (Nat.le_of_succ_le hm) := by
  have hm1 : 1 ≤ m := Nat.le_of_succ_le hm
  calc Subgroup.centralizer ({r₀ (K := K) hm1} : Set (projectiveSL (m + 1) K))
      = (Subgroup.centralizer ({AutPSL.rootInv (K := K) hm1} :
          Set (SpecialLinearGroup (Fin (m + 1)) K))).map (proj (m + 1) K) :=
        centralizer_rootInv_eq_map hm1
    _ = ((radicalSL hm1) ⊔ leviSL hm1).map (proj (m + 1) K) := by
        rw [centralizer_mat_eq_sup]
    _ = (radicalSL hm1).map (proj (m + 1) K) ⊔
          (leviSL hm1).map (proj (m + 1) K) := Subgroup.map_sup _ _ _
    _ = radical hm1 ⊔ leviFull hm1 := by rw [leviFull_eq_map hm1]; rfl

theorem leviFull_le_normalizer_radical (hm : 2 ≤ m) [Finite K] [CharP K 2] :
    leviFull (K := K) (Nat.le_of_succ_le hm) ≤
      Subgroup.normalizer ((radical (K := K) (Nat.le_of_succ_le hm) :
        Subgroup (projectiveSL (m + 1) K)) : Set (projectiveSL (m + 1) K)) := by
  have hm1 : 1 ≤ m := Nat.le_of_succ_le hm
  rw [leviFull_eq_map hm1, radical]
  exact ggRCST_map_le_normalizer (proj (m + 1) K) (leviSL_le_normalizer_radicalSL (K := K) hm1)

theorem disjoint_radical_leviFull (hm : 2 ≤ m) [Finite K] [CharP K 2] :
    Disjoint (radical (K := K) (Nat.le_of_succ_le hm))
      (leviFull (K := K) (Nat.le_of_succ_le hm)) := by
  have hm1 : 1 ≤ m := Nat.le_of_succ_le hm
  rw [radical, leviFull_eq_map hm1]
  exact disjoint_map_of_disjoint (proj (m + 1) K)
    (by rw [ker_proj]; exact scalars_le_leviSL (K := K) hm1)
    (disjoint_radicalSL_leviSL (K := K) hm1)

noncomputable def freeEquiv (hm : 1 ≤ m) :
    (LinFusion.ggTransPlacement hm).free ≃ Fin (m - 1) :=
  (LinFusion.ggTransPlacement hm).free.equivFin.trans
    (finCongr (by rw [InvPlacement.card_free]; omega))

private theorem blockDiag_mul_apply_last (hm : 1 ≤ m)
    {C : Matrix (Fin (m + 1)) (Fin (m + 1)) K}
    (hC : ∀ i j, (LinFusion.ggTransPlacement hm).level i ≠
      (LinFusion.ggTransPlacement hm).level j → C i j = 0)
    (D : Matrix (Fin (m + 1)) (Fin (m + 1)) K) :
    (C * D) (Fin.last m) (Fin.last m) = C (Fin.last m) (Fin.last m) *
      D (Fin.last m) (Fin.last m) := by
  have hlast : (LinFusion.ggTransPlacement hm).level (Fin.last m) = 0 :=
    (level_eq_zero_iff_eq_last hm).2 rfl
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last m)]
  · intro b _ hb
    have hne : (LinFusion.ggTransPlacement hm).level (Fin.last m) ≠
        (LinFusion.ggTransPlacement hm).level b := by
      intro hlev
      exact hb ((level_eq_zero_iff_eq_last hm).1 (hlast ▸ hlev).symm)
    rw [hC (Fin.last m) b hne, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem blockDiag_pow_apply_last (hm : 1 ≤ m)
    {B : SpecialLinearGroup (Fin (m + 1)) K}
    (hD : B ∈ (LinFusion.ggTransPlacement hm).blockDiag K) (n : ℕ) :
    ((B ^ n : SpecialLinearGroup (Fin (m + 1)) K) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.last m) (Fin.last m) =
      ((B : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.last m) (Fin.last m)) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul,
      blockDiag_mul_apply_last hm (D := (B : Matrix (Fin (m + 1)) (Fin (m + 1)) K))
        ((InvPlacement.mem_blockDiag (LinFusion.ggTransPlacement hm)).1
          ((LinFusion.ggTransPlacement hm).blockDiag K |>.pow_mem hD n)), ih, pow_succ]

private theorem twoElt_mem_blockSpecialLinear (hm : 1 ≤ m) [CharP K 2]
    {B : SpecialLinearGroup (Fin (m + 1)) K}
    (hBL : B ∈ leviSL (K := K) hm) (hB : ∃ k, B ^ 2 ^ k = 1) :
    B ∈ blockSpecialLinear (K := K) (LinFusion.ggTransPlacement hm).free := by
  set P := LinFusion.ggTransPlacement hm with hP
  obtain ⟨hD, hd⟩ := mem_leviSL.1 hBL
  obtain ⟨hcorner, hrow, hcol⟩ := commute_dual_facts hm hd
  have hD' : ∀ i j, P.level i ≠ P.level j →
      (B : Matrix (Fin (m + 1)) (Fin (m + 1)) K) i j = 0 :=
    (InvPlacement.mem_blockDiag P).1 hD
  obtain ⟨k, hk⟩ := hB
  have hpow : ((B : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.last m) (Fin.last m)) ^ 2 ^ k =
      1 := by
    have h1 := congrArg (fun X : SpecialLinearGroup (Fin (m + 1)) K =>
      (X : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.last m) (Fin.last m)) hk
    rwa [blockDiag_pow_apply_last hm hD (2 ^ k), Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_apply_eq] at h1
  have hlam : (B : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.last m) (Fin.last m) = 1 := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      simpa using hpow
    · have hzero : ((B : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.last m) (Fin.last m) - 1) ^
          2 ^ k = 0 := by
        rw [sub_pow_char_pow, hpow, one_pow, sub_self]
      exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero k two_ne_zero)).mp hzero)
  have hlam0 : (B : Matrix (Fin (m + 1)) (Fin (m + 1)) K) 0 0 = 1 := by
    rw [hcorner, hlam]
  rw [CFSG.SeitzReduction.LinearPilot.mem_blockSpecialLinear]
  intro i j hij
  by_cases hlev : P.level i = P.level j
  · rcases level_cases hm i with hi | hi | hi
    · have hi' : i = Fin.last m := (level_eq_zero_iff_eq_last hm).1 hi
      have hj' : j = Fin.last m := (level_eq_zero_iff_eq_last hm).1 (by rw [← hlev, hi])
      subst hi'
      subst hj'
      rw [hlam, Matrix.one_apply_eq]
    · exfalso
      have hif : i ∈ P.free := (level_eq_one_iff_free hm).1 hi
      have hjf : j ∈ P.free := (level_eq_one_iff_free hm).1 (by rw [← hlev, hi])
      rcases hij with h | h
      · exact h hif
      · exact h hjf
    · have hi' : i = 0 := (level_eq_two_iff_eq_zero hm).1 hi
      have hj' : j = 0 := (level_eq_two_iff_eq_zero hm).1 (by rw [← hlev, hi])
      subst hi'
      subst hj'
      rw [hlam0, Matrix.one_apply_eq]
  · rw [hD' i j hlev]
    exact (Matrix.one_apply_ne (by intro h; exact hlev (by rw [h]))).symm

theorem blockSpecialLinear_le_leviSL (hm : 1 ≤ m) :
    blockSpecialLinear (K := K) (LinFusion.ggTransPlacement hm).free ≤ leviSL (K := K) hm := by
  intro A hA
  have hD : A ∈ (LinFusion.ggTransPlacement hm).blockDiag K :=
    (LinFusion.ggTransPlacement hm).blockSpecialLinear_free_le_blockDiag hA
  have h0 : (LinFusion.ggTransPlacement hm).level (Fin.last m) = 0 :=
    (level_eq_zero_iff_eq_last hm).2 rfl
  have h2 : (LinFusion.ggTransPlacement hm).level (0 : Fin (m + 1)) = 2 :=
    (level_eq_two_iff_eq_zero hm).2 rfl
  have hlast_free : (Fin.last m) ∉ (LinFusion.ggTransPlacement hm).free := by
    rw [InvPlacement.mem_free, h0]
    exact zero_ne_one
  have hzero_free : (0 : Fin (m + 1)) ∉ (LinFusion.ggTransPlacement hm).free := by
    rw [InvPlacement.mem_free, h2]
    exact (by norm_num : (2 : ℕ) ≠ 1)
  have hcorner : (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.last m) (Fin.last m) =
      (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) 0 0 := by
    rw [(CFSG.SeitzReduction.LinearPilot.mem_blockSpecialLinear).1 hA (Fin.last m) (Fin.last m)
        (Or.inl hlast_free),
      (CFSG.SeitzReduction.LinearPilot.mem_blockSpecialLinear).1 hA 0 0 (Or.inl hzero_free),
      Matrix.one_apply_eq, Matrix.one_apply_eq]
  exact mem_leviSL.2 ⟨hD, blockDiag_mem_centralizer_dual hm hD hcorner⟩

private noncomputable def leviProj (hm : 1 ≤ m) :
    leviSL (K := K) hm →* leviFull (K := K) hm where
  toFun B := ⟨proj (m + 1) K (B : SpecialLinearGroup (Fin (m + 1)) K), by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have h : (B : SpecialLinearGroup (Fin (m + 1)) K) * AutPSL.rootInv hm =
          AutPSL.rootInv hm * (B : SpecialLinearGroup (Fin (m + 1)) K) :=
        Subgroup.mem_centralizer_singleton_iff.mp (leviSL_le_centralizer hm B.2)
      show proj (m + 1) K (B : SpecialLinearGroup (Fin (m + 1)) K) * r₀ hm =
        r₀ hm * proj (m + 1) K (B : SpecialLinearGroup (Fin (m + 1)) K)
      rw [show r₀ hm = proj (m + 1) K (AutPSL.rootInv hm) from rfl, ← map_mul, ← map_mul, h]
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have h : (B : SpecialLinearGroup (Fin (m + 1)) K) * dualRootInv hm =
          dualRootInv hm * (B : SpecialLinearGroup (Fin (m + 1)) K) :=
        Subgroup.mem_centralizer_singleton_iff.mp (mem_leviSL.1 B.2).2
      show proj (m + 1) K (B : SpecialLinearGroup (Fin (m + 1)) K) * y₀ hm =
        y₀ hm * proj (m + 1) K (B : SpecialLinearGroup (Fin (m + 1)) K)
      rw [show y₀ hm = proj (m + 1) K (dualRootInv hm) from rfl, ← map_mul, ← map_mul, h]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' B C := Subtype.ext (map_mul _ _ _)

private theorem leviProj_surjective (hm : 1 ≤ m) [CharP K 2] :
    Function.Surjective (leviProj (K := K) hm) := by
  intro x
  have hx : (x : projectiveSL (m + 1) K) ∈ (leviSL (K := K) hm).map (proj (m + 1) K) := by
    rw [← leviFull_eq_map hm]
    exact x.2
  obtain ⟨B, hB, hBx⟩ := Subgroup.mem_map.1 hx
  exact ⟨⟨B, hB⟩, Subtype.ext hBx⟩

private theorem normal_twoSubgroup_leviSL_eq_bot (hm : 1 ≤ m) [Finite K] [CharP K 2]
    (H : Subgroup (leviSL (K := K) hm)) (hHn : H.Normal)
    (hH2 : IsPGroup 2 H) : H = ⊥ := by
  set P := LinFusion.ggTransPlacement hm with hP
  set H1 : Subgroup (SpecialLinearGroup (Fin (m + 1)) K) :=
    H.map (leviSL (K := K) hm).subtype with hH1
  have hH1le : H1 ≤ blockSpecialLinear (K := K) P.free := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨k, hk⟩ := hH2 ⟨y, hy⟩
    refine twoElt_mem_blockSpecialLinear hm y.2 ⟨k, ?_⟩
    have hk' : ((⟨y, hy⟩ : H) : leviSL (K := K) hm) ^ 2 ^ k = 1 := by
      simpa using congrArg (fun w : H => (w : leviSL (K := K) hm)) hk
    simpa using congrArg (fun z : leviSL (K := K) hm =>
      (z : SpecialLinearGroup (Fin (m + 1)) K)) hk'
  have hH1_2 : IsPGroup 2 H1 := hH2.map _
  have hH1conj : ∀ g ∈ blockSpecialLinear (K := K) P.free, ∀ x ∈ H1,
      g * x * g⁻¹ ∈ H1 := by
    intro g hg x hx
    have hgle : g ∈ leviSL (K := K) hm := blockSpecialLinear_le_leviSL hm hg
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    refine Subgroup.mem_map.2 ⟨(⟨g, hgle⟩ : leviSL (K := K) hm) * y *
      (⟨g, hgle⟩ : leviSL (K := K) hm)⁻¹, hHn.conj_mem y hy ⟨g, hgle⟩, ?_⟩
    rfl
  set H0 : Subgroup (SpecialLinearGroup (LinFusion.ggTransPlacement hm).free K) :=
    H1.comap (blockEmbed (K := K) (LinFusion.ggTransPlacement hm).free) with hH0
  have hH0_2 : IsPGroup 2 H0 :=
    IsPGroup.comap_of_injective hH1_2 (blockEmbed (K := K) P.free) (blockEmbed_injective P.free)
  have hH0n : H0.Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hx1 : blockEmbed (K := K) P.free x ∈ H1 := hx
    have hg : blockEmbed (K := K) P.free g ∈ blockSpecialLinear (K := K) P.free := by
      have h : blockEmbed (K := K) P.free g ∈ (blockEmbed (K := K) P.free).range := by
        rw [MonoidHom.range_eq_map]
        exact Subgroup.mem_map_of_mem (blockEmbed (K := K) P.free) (Subgroup.mem_top g)
      rwa [range_blockEmbed] at h
    have hconj := hH1conj (blockEmbed (K := K) P.free g) hg (blockEmbed (K := K) P.free x) hx1
    rw [Subgroup.mem_comap]
    simpa only [map_mul, map_inv] using hconj
  set e0 : SpecialLinearGroup (LinFusion.ggTransPlacement hm).free K ≃*
      SpecialLinearGroup (Fin (m - 1)) K := reindexSpecialLinear (K := K) (freeEquiv hm) with he0
  set H2 : Subgroup (SpecialLinearGroup (Fin (m - 1)) K) := H0.map e0.toMonoidHom with hH2def
  have hH2_2 : IsPGroup 2 H2 := hH0_2.map e0.toMonoidHom
  have hH2n : H2.Normal := hH0n.map e0.toMonoidHom e0.surjective
  have hH2bot : H2 = ⊥ := by
    have hle : H2 ≤ CFSG.pCore 2 (SpecialLinearGroup (Fin (m - 1)) K) := by
      rw [CFSG.pCore_eq_iSup]
      exact le_iSup_of_le H2 (le_iSup_of_le hH2n (le_iSup_of_le hH2_2 le_rfl))
    rw [CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp.pCore_specialLinear_eq_bot]
      at hle
    exact le_bot_iff.mp hle
  have hH0bot : H0 = ⊥ := by
    have h := hH2bot
    rw [hH2def] at h
    rw [Subgroup.map_eq_bot_iff] at h
    have hker : e0.toMonoidHom.ker = ⊥ := MonoidHom.ker_eq_bot_iff _ |>.mpr e0.injective
    rw [hker] at h
    exact le_bot_iff.mp h
  have hH1bot : H1 = ⊥ := by
    have h := Subgroup.map_comap_eq (blockEmbed (K := K) P.free) H1
    rw [show (blockEmbed (K := K) P.free).range ⊓ H1 = H1 from
      inf_eq_right.mpr (by rw [range_blockEmbed]; exact hH1le)] at h
    rw [show H1.comap (blockEmbed (K := K) P.free) = H0 from rfl, hH0bot,
      Subgroup.map_bot] at h
    exact h.symm
  have hH1bot' : H.map (leviSL (K := K) hm).subtype = ⊥ := by rwa [← hH1]
  rw [Subgroup.map_eq_bot_iff] at hH1bot'
  have hker : (leviSL (K := K) hm).subtype.ker = ⊥ :=
    MonoidHom.ker_eq_bot_iff _ |>.mpr (Subgroup.subtype_injective _)
  rw [hker] at hH1bot'
  exact le_bot_iff.mp hH1bot'

private theorem normal_twoSubgroup_leviFull_eq_bot (hm : 1 ≤ m) [Finite K] [CharP K 2]
    (H : Subgroup (leviFull (K := K) hm)) (hHn : H.Normal)
    (hH2 : IsPGroup 2 H) : H = ⊥ := by
  set T : Subgroup (leviSL (K := K) hm) := H.comap (leviProj (K := K) hm) with hT
  let f : T →* H := MonoidHom.codRestrict ((leviProj (K := K) hm).comp T.subtype) H
    (fun x => x.2)
  have hfsurj : Function.Surjective f := by
    intro a
    obtain ⟨B, hB⟩ := leviProj_surjective hm (a : leviFull (K := K) hm)
    refine ⟨⟨B, ?_⟩, Subtype.ext hB⟩
    rw [hT, Subgroup.mem_comap]
    rw [hB]
    exact a.2
  have hfker : f.ker = (leviProj (K := K) hm).ker.subgroupOf T := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hker_center : f.ker ≤ Subgroup.center T := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hx1 : (x : leviSL (K := K) hm) ∈ Subgroup.center (leviSL (K := K) hm) := by
      rw [Subgroup.mem_center_iff]
      intro z
      have hxproj : proj (m + 1) K (x : SpecialLinearGroup (Fin (m + 1)) K) = 1 := by
        have h := MonoidHom.mem_ker.mp hx
        have h2 : ((f x : H) : leviFull (K := K) hm) = 1 := by
          rw [h]
          rfl
        exact congrArg (fun w : leviFull (K := K) hm =>
          (w : projectiveSL (m + 1) K)) h2
      have hscal : (x : SpecialLinearGroup (Fin (m + 1)) K) ∈ scalars (m + 1) K :=
        proj_eq_one_iff.mp hxproj
      exact Subtype.ext (Subgroup.mem_center_iff.mp
        (scalars_le_center (m + 1) K hscal) (z : SpecialLinearGroup (Fin (m + 1)) K))
    exact Subtype.ext (Subgroup.mem_center_iff.mp hx1 (y : leviSL (K := K) hm))
  haveI : Group.IsNilpotent H := hH2.isNilpotent
  have hTnil : Group.IsNilpotent T :=
    Subgroup.isNilpotent_of_ker_le_center f hker_center
  let S : Subgroup T := CFSG.pCore 2 T
  have hSchar : S.Characteristic := CFSG.pCore_characteristic
  have hSmapn : (S.map T.subtype).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    have hcy : MulAut.conjNormal (H := T) g y ∈ S := by
      have h := hSchar.fixed (MulAut.conjNormal (H := T) g)
      have hy' : y ∈ Subgroup.comap (MulAut.conjNormal (H := T) g).toMonoidHom S := by
        rw [h]
        exact hy
      exact hy'
    exact Subgroup.mem_map.2 ⟨MulAut.conjNormal (H := T) g y, hcy, rfl⟩
  have hSbot : S.map T.subtype = ⊥ :=
    normal_twoSubgroup_leviSL_eq_bot hm _ hSmapn (CFSG.pCore_isPGroup.map _)
  have hSbot' : S = ⊥ := by
    rw [Subgroup.map_eq_bot_iff] at hSbot
    have hker : T.subtype.ker = ⊥ :=
      MonoidHom.ker_eq_bot_iff _ |>.mpr (Subgroup.subtype_injective _)
    rw [hker] at hSbot
    exact le_bot_iff.mp hSbot
  have htop := CFSG.nilpotent_top_le_pCore_sup_pPrimeCore (Q := T) (p := 2) hTnil
  rw [show CFSG.pCore 2 T = S from rfl, hSbot', bot_sup_eq] at htop
  have hprime : CFSG.pPrimeCore 2 T = ⊤ := le_antisymm le_top htop
  have hoddT : Odd (Nat.card T) := by
    have hcop := CFSG.pPrimeCore_coprime_card (p := 2) (G := T)
    rw [hprime] at hcop
    have hcard : Nat.card ↥(⊤ : Subgroup T) = Nat.card T :=
      Nat.card_congr Subgroup.topEquiv.toEquiv
    rw [hcard] at hcop
    exact Nat.coprime_two_left.mp hcop
  have hdvd : Nat.card H ∣ Nat.card T := Subgroup.card_dvd_of_surjective (f := f) hfsurj
  have hoddH : Odd (Nat.card H) := Odd.of_dvd_nat hoddT hdvd
  obtain ⟨a, ha⟩ := hH2.exists_card_eq
  rw [ha] at hoddH
  have ha0 : a = 0 := by
    rcases Nat.eq_zero_or_pos a with h | h
    · exact h
    · exact absurd (Nat.even_pow.2 ⟨even_two, h.ne'⟩) (Nat.not_even_iff_odd.mpr hoddH)
  rw [ha0, pow_zero] at ha
  exact Subgroup.eq_bot_of_card_eq H ha

private theorem isPGroup_normalizer_leviFull_eq_bot (hm : 1 ≤ m) [Finite K] [CharP K 2]
    {N : Subgroup (projectiveSL (m + 1) K)} (hN : N ≤ leviFull (K := K) hm)
    (hN2 : IsPGroup 2 N) (hNn : leviFull (K := K) hm ≤
      Subgroup.normalizer (N : Set (projectiveSL (m + 1) K))) : N = ⊥ := by
  have hHn : (N.subgroupOf (leviFull (K := K) hm)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN).mpr hNn
  have hH2 : IsPGroup 2 (N.subgroupOf (leviFull (K := K) hm)) := by
    rw [← Subgroup.comap_subtype]
    exact hN2.comap_of_injective _ (Subgroup.subtype_injective _)
  have hHbot := normal_twoSubgroup_leviFull_eq_bot hm _ hHn hH2
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hxH : (⟨x, hN hx⟩ : leviFull (K := K) hm) ∈
      N.subgroupOf (leviFull (K := K) hm) := hx
  rw [hHbot] at hxH
  exact congrArg Subtype.val (Subgroup.mem_bot.mp hxH)

theorem pCoreOf_centralizer_rootInv (hm : 2 ≤ m) [Finite K] [CharP K 2] :
    CFSG.Assembly.pCoreOf 2 (Subgroup.centralizer
      ({r₀ (K := K) (Nat.le_of_succ_le hm)} : Set (projectiveSL (m + 1) K))) =
      radical (K := K) (Nat.le_of_succ_le hm) := by
  have hm1 : 1 ≤ m := Nat.le_of_succ_le hm
  refine ggRCST_pCoreOf_eq
    (X := Subgroup.centralizer ({r₀ (K := K) hm1} : Set (projectiveSL (m + 1) K)))
    (Q := radical (K := K) hm1) (M := leviFull (K := K) hm1) ?_ ?_ ?_ ?_
  · simpa using centralizer_rootInv_eq_sup (K := K) hm
  · rw [radical]
    exact (isPGroup_radicalSL (K := K) hm1).map (proj (m + 1) K)
  · simpa using leviFull_le_normalizer_radical (K := K) hm
  · intro N hN hN2 hNn
    exact isPGroup_normalizer_leviFull_eq_bot (K := K) hm1 hN hN2 hNn

end CFSG.StandardType.KGPSL

