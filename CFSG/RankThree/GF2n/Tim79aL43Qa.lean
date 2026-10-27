module

public import CFSG.LargeExtraspecial.AS35WL43Q
public import CFSG.LargeExtraspecial.Timmesfeld.FStar

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.GF2n.Tim79a

open Subgroup Matrix CFSG.LargeExtraspecial CFSG.LargeExtraspecial.AS35W
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LargeExtraspecial.Timmesfeld (Qa IsExtraspecial2 HasWidth)

theorem orderOf_proj_dSL : orderOf (proj 4 (ZMod 3) AS35W.dSL) = 2 := by
  have hne : proj 4 (ZMod 3) AS35W.dSL ≠ 1 := by
    intro h
    obtain ⟨c, -, hc⟩ := mem_scalars.1 (proj_eq_one_iff.1 h)
    have h00 := congrFun (congrFun hc 0) 0
    have h22 := congrFun (congrFun hc 2) 2
    simp [AS35W.dSL, CFSG.ComponentClassification.CatFactsL4U4.HBlocks.X1,
      Matrix.scalar_apply] at h00 h22
    rw [← h00] at h22
    exact absurd h22 (by decide)
  refine orderOf_eq_prime ?_ hne
  rw [← map_pow]
  have : AS35W.dSL ^ 2 = 1 := by decide
  rw [this, map_one]

@[expose] def blkDiag (a b : Matrix (Fin 2) (Fin 2) (ZMod 3)) :
    Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  !![a 0 0, a 0 1, 0, 0; a 1 0, a 1 1, 0, 0; 0, 0, b 0 0, b 0 1; 0, 0, b 1 0, b 1 1]

theorem blkA_blkDiag (a b : Matrix (Fin 2) (Fin 2) (ZMod 3)) :
    blkA (blkDiag a b) = a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkDiag, blkA]

theorem blkB_blkDiag (a b : Matrix (Fin 2) (Fin 2) (ZMod 3)) :
    blkB (blkDiag a b) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkDiag, blkB]

theorem blkC_blkDiag (a b : Matrix (Fin 2) (Fin 2) (ZMod 3)) :
    blkC (blkDiag a b) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkDiag, blkC]

theorem blkD_blkDiag (a b : Matrix (Fin 2) (Fin 2) (ZMod 3)) :
    blkD (blkDiag a b) = b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkDiag, blkD]

theorem blkDiag_mul (a b c d : Matrix (Fin 2) (Fin 2) (ZMod 3)) :
    blkDiag a b * blkDiag c d = blkDiag (a * c) (b * d) := by
  refine blk_ext ?_ ?_ ?_ ?_
  · simp only [blkA_mul, blkA_blkDiag, blkB_blkDiag, blkC_blkDiag, Matrix.zero_mul,
      Matrix.mul_zero, add_zero, zero_add]
  · simp only [blkB_mul, blkA_blkDiag, blkB_blkDiag, blkD_blkDiag, Matrix.zero_mul,
      Matrix.mul_zero, add_zero, zero_add]
  · simp only [blkC_mul, blkC_blkDiag, blkD_blkDiag, blkA_blkDiag, Matrix.zero_mul,
      Matrix.mul_zero, add_zero, zero_add]
  · simp only [blkD_mul, blkD_blkDiag, blkC_blkDiag, blkB_blkDiag, Matrix.zero_mul,
      Matrix.mul_zero, add_zero, zero_add]

theorem blkDiag_one : blkDiag (1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 = 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := blk_one (R := ZMod 3)
  refine blk_ext ?_ ?_ ?_ ?_
  · rw [blkA_blkDiag, h1]
  · rw [blkB_blkDiag, h2]
  · rw [blkC_blkDiag, h3]
  · rw [blkD_blkDiag, h4]

theorem blkDiag_blkA_blkD {M : Matrix (Fin 4) (Fin 4) (ZMod 3)}
    (hB : blkB M = 0) (hC : blkC M = 0) : blkDiag (blkA M) (blkD M) = M := by
  refine blk_ext ?_ ?_ ?_ ?_
  · rw [blkA_blkDiag]
  · rw [blkB_blkDiag, hB]
  · rw [blkC_blkDiag, hC]
  · rw [blkD_blkDiag]

theorem det_blkDiag_q8 : ∀ a : {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List},
    ∀ b : {b : Matrix (Fin 2) (Fin 2) (ZMod 3) // b ∈ q8List},
    (blkDiag a.1 b.1).det = 1 := by
  decide

@[expose] def qtOf (a b : {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List}) : Qt :=
  ⟨⟨blkDiag a.1 b.1, det_blkDiag_q8 a b⟩,
    ⟨blkB_blkDiag a.1 b.1, blkC_blkDiag a.1 b.1,
      by rw [blkA_blkDiag]; exact a.2, by rw [blkD_blkDiag]; exact b.2⟩⟩

theorem qtOf_val (a b : {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List}) :
    ((qtOf a b : Qt).1 : Matrix (Fin 4) (Fin 4) (ZMod 3)) = blkDiag a.1 b.1 := rfl

theorem SL_ext {A B : SpecialLinearGroup (Fin 4) (ZMod 3)}
    (h : (A : Matrix (Fin 4) (Fin 4) (ZMod 3)) = (B : Matrix (Fin 4) (Fin 4) (ZMod 3))) :
    A = B := Subtype.ext h

theorem Qt_ext {g h : Qt}
    (H : ((g : Qt).1 : Matrix (Fin 4) (Fin 4) (ZMod 3)) =
      ((h : Qt).1 : Matrix (Fin 4) (Fin 4) (ZMod 3))) : g = h :=
  Subtype.ext (SL_ext H)

@[expose] def qtToPair (g : Qt) :
    {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List} ×
      {b : Matrix (Fin 2) (Fin 2) (ZMod 3) // b ∈ q8List} :=
  (⟨blkA (g.1 : Matrix (Fin 4) (Fin 4) (ZMod 3)), g.2.2.2.1⟩,
    ⟨blkD (g.1 : Matrix (Fin 4) (Fin 4) (ZMod 3)), g.2.2.2.2⟩)

theorem qtToPair_qtOf (a b : {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List}) :
    qtToPair (qtOf a b) = (a, b) := by
  refine Prod.ext ?_ ?_ <;> apply Subtype.ext <;>
    simp [qtToPair, qtOf, blkA_blkDiag, blkD_blkDiag]

theorem qtOf_qtToPair (g : Qt) : qtOf (qtToPair g).1 (qtToPair g).2 = g := by
  refine Qt_ext ?_
  rw [qtOf_val]
  exact blkDiag_blkA_blkD g.2.1 g.2.2.1

@[expose] def qtEquiv : Qt ≃ ({a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List} ×
    {b : Matrix (Fin 2) (Fin 2) (ZMod 3) // b ∈ q8List}) where
  toFun := qtToPair
  invFun p := qtOf p.1 p.2
  left_inv := qtOf_qtToPair
  right_inv p := qtToPair_qtOf p.1 p.2

theorem card_q8List : Nat.card {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List} = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_Qt : Nat.card Qt = 64 := by
  rw [Nat.card_congr qtEquiv, Nat.card_prod, card_q8List]

theorem scalar_mem_q8List : ∀ c : ZMod 3, scalar (Fin 2) c ∈ q8List → c = 1 ∨ c = -1 := by
  decide

theorem blkA_scalar (c : ZMod 3) : blkA (scalar (Fin 4) c) = scalar (Fin 2) c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkA, Matrix.scalar_apply]

theorem blkD_scalar (c : ZMod 3) : blkD (scalar (Fin 4) c) = scalar (Fin 2) c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkD, Matrix.scalar_apply]

theorem scalar_four_eq_blkDiag (c : ZMod 3) :
    scalar (Fin 4) c = blkDiag (scalar (Fin 2) c) (scalar (Fin 2) c) := by
  refine blk_ext ?_ ?_ ?_ ?_
  · rw [blkA_blkDiag, blkA_scalar]
  · rw [blkB_blkDiag]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blkB, Matrix.scalar_apply]
  · rw [blkC_blkDiag]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blkC, Matrix.scalar_apply]
  · rw [blkD_blkDiag, blkD_scalar]

theorem coe_one_Qt : ((1 : Qt).1 : Matrix (Fin 4) (Fin 4) (ZMod 3)) = 1 := rfl

theorem coe_one_SL :
    ((1 : SpecialLinearGroup (Fin 4) (ZMod 3)) : Matrix (Fin 4) (Fin 4) (ZMod 3)) = 1 := rfl

theorem scalar_two_one : scalar (Fin 2) (1 : ZMod 3) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, Matrix.one_apply]

theorem scalar_two_neg_one : scalar (Fin 2) (-1 : ZMod 3) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, Matrix.neg_apply, Matrix.one_apply]

theorem scalar_four_neg_one : scalar (Fin 4) (-1 : ZMod 3) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, Matrix.neg_apply, Matrix.one_apply]

theorem blkDiag_neg_one : blkDiag (-1 : Matrix (Fin 2) (Fin 2) (ZMod 3))
    (-1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) = (-1 : Matrix (Fin 4) (Fin 4) (ZMod 3)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkDiag, Matrix.neg_apply, Matrix.one_apply]

@[expose] def negOne2 : {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List} :=
  ⟨-1, by decide⟩

@[expose] def z2 : Qt := qtOf negOne2 negOne2

theorem z2_val : ((z2 : Qt).1 : Matrix (Fin 4) (Fin 4) (ZMod 3)) = -1 := by
  rw [z2, qtOf_val]
  exact blkDiag_neg_one

theorem proj_z2 : proj 4 (ZMod 3) (z2 : Qt).1 = 1 := by
  rw [proj_eq_one_iff, mem_scalars]
  have h : ((-1 : (ZMod 3)ˣ) : ZMod 3) = -1 := rfl
  refine ⟨-1, by decide, ?_⟩
  rw [h, z2_val, scalar_four_neg_one]

theorem z2_mem_ker : z2 ∈ ((proj 4 (ZMod 3)).comp Qt.subtype).ker := proj_z2

theorem z2_ne_one : z2 ≠ 1 := by decide

theorem z2_sq : z2 ^ 2 = 1 := by decide

theorem eq_one_or_z2_of_proj_eq_one {g : Qt} (h : proj 4 (ZMod 3) g.1 = 1) :
    g = 1 ∨ g = z2 := by
  obtain ⟨c, - , hgc⟩ := mem_scalars.1 (proj_eq_one_iff.1 h)
  have hA : blkA (g.1 : Matrix (Fin 4) (Fin 4) (ZMod 3)) ∈ q8List := g.2.2.2.1
  have hblk : (g.1 : Matrix (Fin 4) (Fin 4) (ZMod 3)) =
      blkDiag (scalar (Fin 2) (c : ZMod 3)) (scalar (Fin 2) (c : ZMod 3)) := by
    rw [hgc, scalar_four_eq_blkDiag]
  have hAc : blkA (g.1 : Matrix (Fin 4) (Fin 4) (ZMod 3)) = scalar (Fin 2) (c : ZMod 3) := by
    rw [hblk, blkA_blkDiag]
  rcases scalar_mem_q8List (c : ZMod 3) (hAc ▸ hA) with hc | hc
  · left
    refine Qt_ext ?_
    have hg1 : ((g : Qt).1 : Matrix (Fin 4) (Fin 4) (ZMod 3)) = 1 := by
      rw [hblk, hc, scalar_two_one, blkDiag_one]
    exact hg1.trans coe_one_Qt.symm
  · right
    refine Qt_ext ?_
    have hg1 : ((g : Qt).1 : Matrix (Fin 4) (Fin 4) (ZMod 3)) = -1 := by
      rw [hblk, hc, scalar_two_neg_one, blkDiag_neg_one]
    exact hg1.trans z2_val.symm

theorem ker_proj_Qt_eq :
    ((proj 4 (ZMod 3)).comp Qt.subtype).ker = Subgroup.zpowers z2 := by
  ext g
  constructor
  · intro hg
    rcases eq_one_or_z2_of_proj_eq_one hg with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers z2
  · intro hg
    exact Subgroup.zpowers_le.mpr z2_mem_ker hg

theorem card_ker_proj : Nat.card (((proj 4 (ZMod 3)).comp Qt.subtype).ker) = 2 := by
  rw [ker_proj_Qt_eq, Nat.card_zpowers, orderOf_eq_prime z2_sq z2_ne_one]

theorem map_eq_range : ((proj 4 (ZMod 3)).comp Qt.subtype).range =
    Qt.map (proj 4 (ZMod 3)) := by
  ext x
  simp [Subgroup.mem_map, MonoidHom.mem_range]

theorem card_Qt_map : Nat.card (Qt.map (proj 4 (ZMod 3))) = 32 := by
  have h := Subgroup.card_ker_mul_card_range ((proj 4 (ZMod 3)).comp Qt.subtype)
  rw [card_ker_proj, card_Qt, map_eq_range] at h
  omega


theorem isPGroup_two_Qt_map : IsPGroup 2 (AS35W.Qt.map (proj 4 (ZMod 3))) :=
  IsPGroup.of_card (n := 5) (by rw [card_Qt_map]; norm_num)

theorem Qt_map_le_centralizer :
    AS35W.Qt.map (proj 4 (ZMod 3)) ≤ Subgroup.centralizer
      ({proj 4 (ZMod 3) AS35W.dSL} : Set (projectiveSL 4 (ZMod 3))) := by
  rintro _ ⟨g, hg, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  rw [← map_mul, ← map_mul, AS35W.comm_dSL_of_mem_Qt hg]


theorem card_Qa_of_width_two (h : HasWidth (Qa (proj 4 (ZMod 3) AS35W.dSL)) 2) :
    Nat.card (Qa (proj 4 (ZMod 3) AS35W.dSL)) = 32 := by
  rw [HasWidth] at h
  simpa using h


theorem zmod3_pow_four_eq_one {x : ZMod 3} (h : x ^ 4 = 1) : x = 1 ∨ x = -1 := by
  have hsq : ∀ y : ZMod 3, y ^ 2 = 1 → y = 1 ∨ y = -1 := by decide
  have hno : ∀ x : ZMod 3, x ^ 2 ≠ -1 := by decide
  have h2 : (x ^ 2) ^ 2 = 1 := by
    rw [← pow_mul, show (2 * 2 : ℕ) = 4 by norm_num]
    exact h
  rcases hsq (x ^ 2) h2 with h1 | h1
  · exact hsq x h1
  · exact absurd h1 (hno x)

abbrev CentralizerZ : Subgroup (projectiveSL 4 (ZMod 3)) :=
  Subgroup.centralizer ({proj 4 (ZMod 3) AS35W.dSL} : Set (projectiveSL 4 (ZMod 3)))

theorem scalar_four_mul (c : ZMod 3) (M : Matrix (Fin 4) (Fin 4) (ZMod 3)) :
    scalar (Fin 4) c * M = c • M := by
  rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul M c]

theorem defect_mem_scalars {h' : SpecialLinearGroup (Fin 4) (ZMod 3)}
    (hh : proj 4 (ZMod 3) h' * proj 4 (ZMod 3) AS35W.dSL =
      proj 4 (ZMod 3) AS35W.dSL * proj 4 (ZMod 3) h') :
    h' * AS35W.dSL * h'⁻¹ * AS35W.dSL⁻¹ ∈ scalars 4 (ZMod 3) := by
  rw [← ker_proj, MonoidHom.mem_ker]
  simp only [map_mul, map_inv, map_one]
  rw [hh]
  group

theorem branch_of_comm {h' : SpecialLinearGroup (Fin 4) (ZMod 3)}
    (hh : proj 4 (ZMod 3) h' * proj 4 (ZMod 3) AS35W.dSL =
      proj 4 (ZMod 3) AS35W.dSL * proj 4 (ZMod 3) h') :
    (AS35W.dSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) * (h' : Matrix (Fin 4) (Fin 4) (ZMod 3)) =
        (h' : Matrix (Fin 4) (Fin 4) (ZMod 3)) * AS35W.dSL ∨
      (AS35W.dSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) * (h' : Matrix (Fin 4) (Fin 4) (ZMod 3)) =
        -((h' : Matrix (Fin 4) (Fin 4) (ZMod 3)) * AS35W.dSL) := by
  obtain ⟨c, hc, hA⟩ := mem_scalars.1 (defect_mem_scalars hh)
  have hcv : (c : ZMod 3) ^ 4 = 1 := by simpa using congrArg Units.val hc
  have hcent : ∀ x : SpecialLinearGroup (Fin 4) (ZMod 3),
      scalarElement c hc * x = x * scalarElement c hc :=
    fun x => (Subgroup.mem_center_iff.mp
      (scalars_le_center 4 (ZMod 3) (scalarElement_mem_scalars c hc)) x).symm
  have hE : h' * AS35W.dSL * h'⁻¹ * AS35W.dSL⁻¹ = scalarElement c hc := Subtype.ext hA
  have hD : h' * AS35W.dSL = AS35W.dSL * (scalarElement c hc * h') := by
    calc h' * AS35W.dSL = (h' * AS35W.dSL * h'⁻¹ * AS35W.dSL⁻¹) * AS35W.dSL * h' := by group
      _ = scalarElement c hc * AS35W.dSL * h' := by rw [hE]
      _ = AS35W.dSL * (scalarElement c hc * h') := by rw [hcent AS35W.dSL]; group
  have hmat : (h' : Matrix (Fin 4) (Fin 4) (ZMod 3)) *
        (AS35W.dSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) =
      (c : ZMod 3) • ((AS35W.dSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) *
        (h' : Matrix (Fin 4) (Fin 4) (ZMod 3))) := by
    have h := congrArg (fun x : SpecialLinearGroup (Fin 4) (ZMod 3) =>
      (x : Matrix (Fin 4) (Fin 4) (ZMod 3))) hD
    have e1 : ((h' * AS35W.dSL : SpecialLinearGroup (Fin 4) (ZMod 3)) :
        Matrix (Fin 4) (Fin 4) (ZMod 3)) =
        (h' : Matrix (Fin 4) (Fin 4) (ZMod 3)) *
          (AS35W.dSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) := rfl
    have e2 : ((AS35W.dSL * (scalarElement c hc * h') :
        SpecialLinearGroup (Fin 4) (ZMod 3)) : Matrix (Fin 4) (Fin 4) (ZMod 3)) =
        (c : ZMod 3) • ((AS35W.dSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) *
          (h' : Matrix (Fin 4) (Fin 4) (ZMod 3))) := by
      rw [show ((AS35W.dSL * (scalarElement c hc * h') :
            SpecialLinearGroup (Fin 4) (ZMod 3)) : Matrix (Fin 4) (Fin 4) (ZMod 3)) =
          (AS35W.dSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) *
            (((scalarElement c hc : SpecialLinearGroup (Fin 4) (ZMod 3)) :
              Matrix (Fin 4) (Fin 4) (ZMod 3)) *
            (h' : Matrix (Fin 4) (Fin 4) (ZMod 3))) from rfl]
      rw [show ((scalarElement c hc : SpecialLinearGroup (Fin 4) (ZMod 3)) :
            Matrix (Fin 4) (Fin 4) (ZMod 3)) = scalar (Fin 4) ((c : ZMod 3)) from rfl]
      rw [scalar_four_mul, Matrix.mul_smul]
    exact e1.symm.trans (h.trans e2)
  rcases zmod3_pow_four_eq_one hcv with hc1 | hc1
  · left
    rw [hc1, one_smul] at hmat
    exact hmat.symm
  · right
    rw [hc1] at hmat
    simp only [neg_one_smul] at hmat
    have h := congrArg Neg.neg hmat
    simpa using h.symm

theorem Qt_map_subgroupOf_normal :
    ((AS35W.Qt.map (proj 4 (ZMod 3))).subgroupOf CentralizerZ).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hnP : (n : projectiveSL 4 (ZMod 3)) ∈ AS35W.Qt.map (proj 4 (ZMod 3)) :=
    Subgroup.mem_subgroupOf.mp hn
  have hg' : (g : projectiveSL 4 (ZMod 3)) * proj 4 (ZMod 3) AS35W.dSL =
      proj 4 (ZMod 3) AS35W.dSL * (g : projectiveSL 4 (ZMod 3)) :=
    ((Subgroup.mem_centralizer_iff.mp g.2) _ (Set.mem_singleton _)).symm
  obtain ⟨q, hq, hqn⟩ := hnP
  obtain ⟨h', hh'⟩ := proj_surjective (n := 4) (K := ZMod 3) (g : projectiveSL 4 (ZMod 3))
  have hbranch := branch_of_comm (h' := h') (by rw [hh']; exact hg')
  have hconj : h' * q * h'⁻¹ ∈ AS35W.Qt :=
    AS35W.conj_mem_Qt_of_comm_or_anticomm hbranch hq
  refine Subgroup.mem_subgroupOf.mpr ?_
  have hcoe : ((g * n * g⁻¹ : ↥CentralizerZ) : projectiveSL 4 (ZMod 3)) =
      proj 4 (ZMod 3) (h' * q * h'⁻¹) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, ← hh', ← hqn]
  rw [hcoe]
  exact Subgroup.mem_map_of_mem _ hconj

theorem Qt_map_le_Qa :
    AS35W.Qt.map (proj 4 (ZMod 3)) ≤ Qa (proj 4 (ZMod 3) AS35W.dSL) := by
  have hPC : AS35W.Qt.map (proj 4 (ZMod 3)) ≤ CentralizerZ := Qt_map_le_centralizer
  have hPN : ((AS35W.Qt.map (proj 4 (ZMod 3))).subgroupOf CentralizerZ).Normal :=
    Qt_map_subgroupOf_normal
  have hP2 : IsPGroup 2 ((AS35W.Qt.map (proj 4 (ZMod 3))).subgroupOf CentralizerZ) :=
    isPGroup_two_Qt_map.of_equiv (Subgroup.subgroupOfEquivOfLe hPC).symm
  have hle : (AS35W.Qt.map (proj 4 (ZMod 3))).subgroupOf CentralizerZ ≤
      CFSG.pCore 2 ↥CentralizerZ :=
    le_sSup (s := {K : Subgroup ↥CentralizerZ | K.Normal ∧ IsPGroup 2 K}) ⟨hPN, hP2⟩
  have hle2 : (AS35W.Qt.map (proj 4 (ZMod 3))).subgroupOf CentralizerZ ≤
      CFSG.generalizedFitting ↥CentralizerZ := by
    refine hle.trans (le_trans (CFSG.pCore_le_fitting ↥CentralizerZ 2) ?_)
    rw [CFSG.generalizedFitting.eq_sup]
    exact le_sup_left
  have hmap : AS35W.Qt.map (proj 4 (ZMod 3)) ≤
      (CFSG.generalizedFitting ↥CentralizerZ).map CentralizerZ.subtype := by
    have hm := Subgroup.map_mono (f := CentralizerZ.subtype) hle2
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPC] at hm
  exact hmap

theorem Qa_proj_dSL (h : HasWidth (Qa (proj 4 (ZMod 3) AS35W.dSL)) 2) :
    Qa (proj 4 (ZMod 3) AS35W.dSL) = AS35W.Qt.map (proj 4 (ZMod 3)) := by
  refine (Subgroup.eq_of_le_of_card_ge Qt_map_le_Qa ?_).symm
  rw [card_Qa_of_width_two h, card_Qt_map]

open scoped commutatorElement

@[expose] def q8Sub : Subgroup (SpecialLinearGroup (Fin 2) (ZMod 3)) where
  carrier := {A | (A : Matrix (Fin 2) (Fin 2) (ZMod 3)) ∈ q8List}
  one_mem' := by
    show ((1 : SpecialLinearGroup (Fin 2) (ZMod 3)) :
      Matrix (Fin 2) (Fin 2) (ZMod 3)) ∈ q8List
    rw [Matrix.SpecialLinearGroup.coe_one]
    simp [q8List]
  mul_mem' := by
    intro A B hA hB
    exact q8List_mul A.1 hA B.1 hB
  inv_mem' := by
    intro A hA
    rw [q8_inv hA]
    exact q8List_mul (A.1 * A.1) (q8List_mul A.1 hA A.1 hA) A.1 hA

@[expose] def q8SL (a : {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List}) : q8Sub :=
  ⟨⟨a.1, by
    rw [Matrix.det_fin_two]
    exact (q8List_prop a.1 a.2).1⟩, a.2⟩

@[expose] def q8Mul (a c : {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List}) :
    {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List} :=
  ⟨a.1 * c.1, q8List_mul a.1 a.2 c.1 c.2⟩

@[expose] def oneQ : {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List} := ⟨1, by simp [q8List]⟩

@[expose] def negOne8 : q8Sub := q8SL negOne2

theorem q8SL_mul (a c : {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List}) :
    q8SL (q8Mul a c) = q8SL a * q8SL c := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

theorem q8SL_one : q8SL oneQ = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

theorem q8SL_negOne : q8SL negOne2 = negOne8 := rfl

theorem q8SL_injective : Function.Injective q8SL := by
  intro a b h
  apply Subtype.ext
  exact congrArg (fun x : q8Sub => (x : Matrix (Fin 2) (Fin 2) (ZMod 3))) h

theorem q8SL_eq_one_iff (a : {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List}) :
    q8SL a = 1 ↔ a = oneQ := by
  rw [← q8SL_one]
  exact q8SL_injective.eq_iff

theorem q8SL_inv (a : {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List}) :
    (q8SL a)⁻¹ = q8SL a * q8SL a * q8SL a := by
  apply Subtype.ext
  exact q8_inv (a := (q8SL a : SpecialLinearGroup (Fin 2) (ZMod 3))) a.2

theorem finSumFinEquiv_symm_zero :
    (finSumFinEquiv (m := 2) (n := 2)).symm (0 : Fin 4) = Sum.inl 0 := by
  decide

theorem finSumFinEquiv_symm_one :
    (finSumFinEquiv (m := 2) (n := 2)).symm (1 : Fin 4) = Sum.inl 1 := by
  decide

theorem finSumFinEquiv_symm_two :
    (finSumFinEquiv (m := 2) (n := 2)).symm (2 : Fin 4) = Sum.inr 0 := by
  decide

theorem finSumFinEquiv_symm_three :
    (finSumFinEquiv (m := 2) (n := 2)).symm (3 : Fin 4) = Sum.inr 1 := by
  decide

theorem blkDiag_eq_fromBlocks (a b : Matrix (Fin 2) (Fin 2) (ZMod 3)) :
    blkDiag a b = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks a 0 0 b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blkDiag, Matrix.reindex_apply, Matrix.fromBlocks,
      finSumFinEquiv_symm_zero, finSumFinEquiv_symm_one,
      finSumFinEquiv_symm_two, finSumFinEquiv_symm_three]

theorem det_blkDiag (a b : Matrix (Fin 2) (Fin 2) (ZMod 3)) :
    (blkDiag a b).det = a.det * b.det := by
  rw [blkDiag_eq_fromBlocks, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

@[expose] def blkSL (A B : SpecialLinearGroup (Fin 2) (ZMod 3)) :
    SpecialLinearGroup (Fin 4) (ZMod 3) :=
  ⟨blkDiag A.1 B.1, by rw [det_blkDiag, A.2, B.2, mul_one]⟩

theorem blkSL_mul (A B C D : SpecialLinearGroup (Fin 2) (ZMod 3)) :
    blkSL A B * blkSL C D = blkSL (A * C) (B * D) := by
  apply Subtype.ext
  exact blkDiag_mul A.1 B.1 C.1 D.1

theorem blkSL_one : blkSL 1 1 = (1 : SpecialLinearGroup (Fin 4) (ZMod 3)) := by
  apply Subtype.ext
  exact blkDiag_one

theorem blkSL_inv (A B : SpecialLinearGroup (Fin 2) (ZMod 3)) :
    (blkSL A B)⁻¹ = blkSL A⁻¹ B⁻¹ := by
  exact inv_eq_of_mul_eq_one_right (by
    rw [blkSL_mul, mul_inv_cancel, mul_inv_cancel, blkSL_one])

theorem blkSL_commutator (A B C D : SpecialLinearGroup (Fin 2) (ZMod 3)) :
    ⁅blkSL A B, blkSL C D⁆ = blkSL ⁅A, C⁆ ⁅B, D⁆ := by
  rw [commutatorElement_def, blkSL_mul, blkSL_inv, blkSL_inv, blkSL_mul, blkSL_mul]
  rfl

theorem qtOf_eq_blkSL (a b : {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List}) :
    ((qtOf a b : Qt).1 : SpecialLinearGroup (Fin 4) (ZMod 3)) =
      blkSL (q8SL a) (q8SL b) := by
  apply Subtype.ext
  rfl

set_option maxRecDepth 20000 in
theorem q8_commutator_cube_eq_one_or_negOne :
    ∀ a c : {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List},
      q8SL a * q8SL c * (q8SL a * q8SL a * q8SL a) *
          (q8SL c * q8SL c * q8SL c) = 1 ∨
        q8SL a * q8SL c * (q8SL a * q8SL a * q8SL a) *
          (q8SL c * q8SL c * q8SL c) = negOne8 := by
  decide

theorem q8_commutator_eq_one_or_negOne
    (a c : {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List}) :
    ⁅q8SL a, q8SL c⁆ = 1 ∨ ⁅q8SL a, q8SL c⁆ = negOne8 := by
  rw [commutatorElement_def, q8SL_inv, q8SL_inv]
  exact q8_commutator_cube_eq_one_or_negOne a c

@[expose] def q8Comm (a c : {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List}) :
    {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List} :=
  ⟨((⁅q8SL a, q8SL c⁆ : q8Sub) : Matrix (Fin 2) (Fin 2) (ZMod 3)), by
    rcases q8_commutator_eq_one_or_negOne a c with h | h
    · rw [h]
      exact oneQ.2
    · rw [h]
      exact negOne2.2⟩

theorem q8SL_q8Comm (a c : {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List}) :
    q8SL (q8Comm a c) = ⁅q8SL a, q8SL c⁆ := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

theorem q8Comm_eq_one_or_negOne
    (a c : {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List}) :
    q8Comm a c = oneQ ∨ q8Comm a c = negOne2 := by
  rcases q8_commutator_eq_one_or_negOne a c with h | h
  · left
    apply Subtype.ext
    exact congrArg (fun x : q8Sub =>
      ((x : SpecialLinearGroup (Fin 2) (ZMod 3)) :
        Matrix (Fin 2) (Fin 2) (ZMod 3))) h
  · right
    apply Subtype.ext
    exact congrArg (fun x : q8Sub =>
      ((x : SpecialLinearGroup (Fin 2) (ZMod 3)) :
        Matrix (Fin 2) (Fin 2) (ZMod 3))) h

theorem q8Comm_eq_one_iff_commute
    (a c : {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List}) :
    q8Comm a c = oneQ ↔ q8SL a * q8SL c = q8SL c * q8SL a := by
  rw [← q8SL_eq_one_iff, q8SL_q8Comm, commutatorElement_eq_one_iff_mul_comm]

theorem q8Comm_one_right (a : {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List}) :
    q8Comm a oneQ = oneQ := by
  rw [q8Comm_eq_one_iff_commute, q8SL_one, mul_one, one_mul]

set_option maxRecDepth 20000 in
theorem q8_mul_comm_iff_central :
    ∀ a : {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List},
      (∀ c : {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List},
        q8SL a * q8SL c = q8SL c * q8SL a) ↔ a = oneQ ∨ a = negOne2 := by
  decide

set_option maxRecDepth 20000 in
theorem exists_q8_commutator_cube_eq_negOne :
    ∃ a c : {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List},
      q8SL a * q8SL c * (q8SL a * q8SL a * q8SL a) *
        (q8SL c * q8SL c * q8SL c) = negOne8 := by
  decide

theorem exists_q8Comm_eq_negOne :
    ∃ a c : {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List},
      q8Comm a c = negOne2 := by
  obtain ⟨a, c, h⟩ := exists_q8_commutator_cube_eq_negOne
  refine ⟨a, c, ?_⟩
  have hc : ⁅q8SL a, q8SL c⁆ = negOne8 := by
    rw [commutatorElement_def, q8SL_inv, q8SL_inv]
    exact h
  apply Subtype.ext
  exact congrArg (fun x : q8Sub =>
    ((x : SpecialLinearGroup (Fin 2) (ZMod 3)) :
      Matrix (Fin 2) (Fin 2) (ZMod 3))) hc

@[expose] def s1 : Qt := qtOf negOne2 oneQ

@[expose] def s2 : Qt := qtOf oneQ negOne2

@[expose] def K4 : Subgroup Qt := Subgroup.closure ({z2, s2} : Set Qt)

theorem qtOf_one : qtOf oneQ oneQ = (1 : Qt) := by
  apply Qt_ext
  rw [qtOf_val, coe_one_Qt]
  simpa [oneQ] using blkDiag_one

theorem z2_mul_s2 : z2 * s2 = s1 := by
  decide

theorem z2_mem_K4 : z2 ∈ K4 := Subgroup.subset_closure (by simp)

theorem s2_mem_K4 : s2 ∈ K4 := Subgroup.subset_closure (by simp)

theorem one_mem_K4 : (1 : Qt) ∈ K4 := K4.one_mem

theorem s1_mem_K4 : s1 ∈ K4 := by
  rw [← z2_mul_s2]
  exact K4.mul_mem z2_mem_K4 s2_mem_K4

theorem s2_val : ((s2 : Qt).1 : Matrix (Fin 4) (Fin 4) (ZMod 3)) = AS35W.dSL := by
  rw [s2, qtOf_val]
  obtain ⟨h1, h2, h3, h4⟩ := AS35W.blk_dSL
  rw [← blkDiag_blkA_blkD (M := AS35W.dSL) h2 h3, h1, h4]
  rfl

theorem s2_eq_dSL : (s2 : Qt).1 = AS35W.dSL := Subtype.ext s2_val

theorem dSL_mem_Qt : AS35W.dSL ∈ Qt := s2_eq_dSL ▸ (s2 : Qt).2

theorem qtOf_mul (a b c d : {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List}) :
    qtOf a b * qtOf c d = qtOf (q8Mul a c) (q8Mul b d) := by
  apply Qt_ext
  change ((qtOf a b : Qt).1 : Matrix (Fin 4) (Fin 4) (ZMod 3)) *
      ((qtOf c d : Qt).1 : Matrix (Fin 4) (Fin 4) (ZMod 3)) =
    blkDiag (q8Mul a c).1 (q8Mul b d).1
  rw [qtOf_val, qtOf_val, blkDiag_mul]
  rfl

theorem qtOf_commutator
    (a b c d : {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List}) :
    ⁅qtOf a b, qtOf c d⁆ = qtOf (q8Comm a c) (q8Comm b d) := by
  apply Qt_ext
  have h1 : ((⁅qtOf a b, qtOf c d⁆ : Qt).1 : SpecialLinearGroup (Fin 4) (ZMod 3)) =
      ⁅((qtOf a b : Qt).1 : SpecialLinearGroup (Fin 4) (ZMod 3)),
        ((qtOf c d : Qt).1 : SpecialLinearGroup (Fin 4) (ZMod 3))⁆ :=
    map_commutatorElement (f := Qt.subtype) (g₁ := qtOf a b) (g₂ := qtOf c d)
  have h2 : ⁅((qtOf a b : Qt).1 : SpecialLinearGroup (Fin 4) (ZMod 3)),
        ((qtOf c d : Qt).1 : SpecialLinearGroup (Fin 4) (ZMod 3))⁆ =
      blkSL ⁅((q8SL a : q8Sub) : SpecialLinearGroup (Fin 2) (ZMod 3)),
          ((q8SL c : q8Sub) : SpecialLinearGroup (Fin 2) (ZMod 3))⁆
        ⁅((q8SL b : q8Sub) : SpecialLinearGroup (Fin 2) (ZMod 3)),
          ((q8SL d : q8Sub) : SpecialLinearGroup (Fin 2) (ZMod 3))⁆ := by
    rw [qtOf_eq_blkSL, qtOf_eq_blkSL, blkSL_commutator]
  have h3 : blkSL ⁅((q8SL a : q8Sub) : SpecialLinearGroup (Fin 2) (ZMod 3)),
          ((q8SL c : q8Sub) : SpecialLinearGroup (Fin 2) (ZMod 3))⁆
        ⁅((q8SL b : q8Sub) : SpecialLinearGroup (Fin 2) (ZMod 3)),
          ((q8SL d : q8Sub) : SpecialLinearGroup (Fin 2) (ZMod 3))⁆ =
      ((qtOf (q8Comm a c) (q8Comm b d) : Qt).1 :
        SpecialLinearGroup (Fin 4) (ZMod 3)) := by
    rw [qtOf_eq_blkSL]
    rw [show ((q8SL (q8Comm a c) : q8Sub) : SpecialLinearGroup (Fin 2) (ZMod 3)) =
        ⁅((q8SL a : q8Sub) : SpecialLinearGroup (Fin 2) (ZMod 3)),
          ((q8SL c : q8Sub) : SpecialLinearGroup (Fin 2) (ZMod 3))⁆ from
      congrArg (fun x : q8Sub => (x : SpecialLinearGroup (Fin 2) (ZMod 3)))
        (q8SL_q8Comm a c)]
    rw [show ((q8SL (q8Comm b d) : q8Sub) : SpecialLinearGroup (Fin 2) (ZMod 3)) =
        ⁅((q8SL b : q8Sub) : SpecialLinearGroup (Fin 2) (ZMod 3)),
          ((q8SL d : q8Sub) : SpecialLinearGroup (Fin 2) (ZMod 3))⁆ from
      congrArg (fun x : q8Sub => (x : SpecialLinearGroup (Fin 2) (ZMod 3)))
        (q8SL_q8Comm b d)]
  exact congrArg (fun x : SpecialLinearGroup (Fin 4) (ZMod 3) =>
    (x : Matrix (Fin 4) (Fin 4) (ZMod 3))) (h1.trans (h2.trans h3))

theorem qtOf_inj {a b c d : {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List}}
    (h : qtOf a b = qtOf c d) : a = c ∧ b = d := by
  have h' := congrArg qtToPair h
  rw [qtToPair_qtOf, qtToPair_qtOf] at h'
  exact Prod.ext_iff.mp h'

theorem oneQ_ne_negOne2 : oneQ ≠ negOne2 := by
  intro h
  have h1 := congrArg (fun x : {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List} =>
    (x : Matrix (Fin 2) (Fin 2) (ZMod 3))) h
  exact absurd h1 (by decide)

theorem qtOf_one_or_negOne_mem_K4
    (a b : {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List})
    (ha : a = oneQ ∨ a = negOne2) (hb : b = oneQ ∨ b = negOne2) :
    qtOf a b ∈ K4 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · rw [qtOf_one]
    exact one_mem_K4
  · exact s2_mem_K4
  · change s1 ∈ K4
    exact s1_mem_K4
  · exact z2_mem_K4

theorem commutator_qtOf_mem_K4
    (a b c d : {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List}) :
    ⁅qtOf a b, qtOf c d⁆ ∈ K4 := by
  rw [qtOf_commutator]
  exact qtOf_one_or_negOne_mem_K4 _ _
    (q8Comm_eq_one_or_negOne a c) (q8Comm_eq_one_or_negOne b d)

theorem commutator_top_le_K4 : ⁅(⊤ : Subgroup Qt), (⊤ : Subgroup Qt)⁆ ≤ K4 := by
  rw [Subgroup.commutator_le]
  intro g _ h _
  rw [← qtOf_qtToPair g, ← qtOf_qtToPair h]
  exact commutator_qtOf_mem_K4 _ _ _ _

theorem z2_mem_commutator_top : z2 ∈ ⁅(⊤ : Subgroup Qt), (⊤ : Subgroup Qt)⁆ := by
  obtain ⟨a, c, hac⟩ := exists_q8Comm_eq_negOne
  have h : ⁅qtOf a a, qtOf c c⁆ = z2 := by
    rw [qtOf_commutator, hac]
    rfl
  rw [← h]
  exact Subgroup.commutator_mem_commutator (H₁ := (⊤ : Subgroup Qt)) (H₂ := (⊤ : Subgroup Qt))
    (Subgroup.mem_top (qtOf oneQ a)) (Subgroup.mem_top (qtOf oneQ c))

theorem s2_mem_commutator_top : s2 ∈ ⁅(⊤ : Subgroup Qt), (⊤ : Subgroup Qt)⁆ := by
  obtain ⟨a, c, hac⟩ := exists_q8Comm_eq_negOne
  have h : ⁅qtOf oneQ a, qtOf oneQ c⁆ = s2 := by
    rw [qtOf_commutator, q8Comm_one_right, hac]
    rfl
  rw [← h]
  exact Subgroup.commutator_mem_commutator (H₁ := (⊤ : Subgroup Qt)) (H₂ := (⊤ : Subgroup Qt))
    (Subgroup.mem_top (qtOf oneQ a)) (Subgroup.mem_top (qtOf oneQ c))

theorem K4_le_commutator_top : K4 ≤ ⁅(⊤ : Subgroup Qt), (⊤ : Subgroup Qt)⁆ := by
  rw [K4, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact z2_mem_commutator_top
  · exact s2_mem_commutator_top

theorem commutator_top_eq_K4 : ⁅(⊤ : Subgroup Qt), (⊤ : Subgroup Qt)⁆ = K4 :=
  le_antisymm commutator_top_le_K4 K4_le_commutator_top

theorem mem_zpowers_z2_iff {g : Qt} :
    g ∈ Subgroup.zpowers z2 ↔ g = 1 ∨ g = z2 := by
  rw [mem_zpowers_iff_mem_range_orderOf,
    orderOf_eq_prime z2_sq z2_ne_one]
  simp only [Finset.mem_range, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hk, hkg⟩
    interval_cases k
    · left
      simpa using hkg.symm
    · right
      simpa using hkg.symm
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, by simp⟩
    · exact ⟨1, by norm_num, by simp⟩

theorem proj_Qt_z2 : ((proj 4 (ZMod 3)).comp Qt.subtype) z2 = 1 := proj_z2

theorem proj_Qt_s2 :
    ((proj 4 (ZMod 3)).comp Qt.subtype) s2 = proj 4 (ZMod 3) AS35W.dSL := by
  show proj 4 (ZMod 3) (s2 : Qt).1 = proj 4 (ZMod 3) AS35W.dSL
  rw [s2_eq_dSL]

theorem K4_map_eq_zpowers :
    K4.map ((proj 4 (ZMod 3)).comp Qt.subtype) =
      Subgroup.zpowers (proj 4 (ZMod 3) AS35W.dSL) := by
  apply le_antisymm
  · rw [K4, MonoidHom.map_closure, Subgroup.closure_le]
    rintro x ⟨y, hy, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · rw [proj_Qt_z2]
      exact Subgroup.one_mem _
    · rw [proj_Qt_s2]
      exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le, ← proj_Qt_s2]
    exact Subgroup.mem_map_of_mem _ s2_mem_K4

theorem mem_K4_of_center_lift {q : Qt} {y : ↥(Qt.map (proj 4 (ZMod 3)))}
    (hy : y ∈ Subgroup.center (Qt.map (proj 4 (ZMod 3))))
    (hqy : (y : projectiveSL 4 (ZMod 3)) =
      proj 4 (ZMod 3) (q : SpecialLinearGroup (Fin 4) (ZMod 3))) :
    q ∈ K4 := by
  let a := (qtToPair q).1
  let b := (qtToPair q).2
  have hq_ab : qtOf a b = q := qtOf_qtToPair q
  have hcentral := Subgroup.mem_center_iff.mp hy
  have hcomm_left : ∀ c : {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List},
      q8Comm a c = oneQ := by
    intro c
    let yc : Qt := qtOf c oneQ
    have hmem_yc : proj 4 (ZMod 3) (yc : SpecialLinearGroup (Fin 4) (ZMod 3)) ∈
        Qt.map (proj 4 (ZMod 3)) :=
      Subgroup.mem_map_of_mem (proj 4 (ZMod 3)) yc.2
    have hcent := congrArg (fun w : ↥(Qt.map (proj 4 (ZMod 3))) =>
      (w : projectiveSL 4 (ZMod 3)))
      (hcentral ⟨proj 4 (ZMod 3) (yc : SpecialLinearGroup (Fin 4) (ZMod 3)), hmem_yc⟩)
    have hcent' : proj 4 (ZMod 3) (q : SpecialLinearGroup (Fin 4) (ZMod 3)) *
        proj 4 (ZMod 3) (yc : SpecialLinearGroup (Fin 4) (ZMod 3)) =
        proj 4 (ZMod 3) (yc : SpecialLinearGroup (Fin 4) (ZMod 3)) *
          proj 4 (ZMod 3) (q : SpecialLinearGroup (Fin 4) (ZMod 3)) := by
      simpa [hqy] using hcent.symm
    have hcomm_psl : ⁅proj 4 (ZMod 3) (q : SpecialLinearGroup (Fin 4) (ZMod 3)),
        proj 4 (ZMod 3) (yc : SpecialLinearGroup (Fin 4) (ZMod 3))⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr hcent'
    have hker : ⁅q, yc⁆ ∈ ((proj 4 (ZMod 3)).comp Qt.subtype).ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement]
      simpa [MonoidHom.comp_apply] using hcomm_psl
    have hmem_z2 : ⁅q, yc⁆ ∈ Subgroup.zpowers z2 := by
      rwa [ker_proj_Qt_eq] at hker
    have hformula : ⁅q, yc⁆ = qtOf (q8Comm a c) oneQ := by
      rw [← hq_ab, show yc = qtOf c oneQ from rfl, qtOf_commutator, q8Comm_one_right]
    have h1or2 : qtOf (q8Comm a c) oneQ = 1 ∨ qtOf (q8Comm a c) oneQ = z2 := by
      rw [← hformula]
      exact mem_zpowers_z2_iff.mp hmem_z2
    have hne : qtOf (q8Comm a c) oneQ ≠ z2 := by
      intro hh
      have hb : oneQ = negOne2 :=
        (qtOf_inj (by simpa [z2] using hh)).2
      exact oneQ_ne_negOne2 hb
    have hone : qtOf (q8Comm a c) oneQ = 1 := by
      rcases h1or2 with h | h
      · exact h
      · exact absurd h hne
    have heq : qtOf (q8Comm a c) oneQ = qtOf oneQ oneQ := by
      rw [hone, qtOf_one]
    exact (qtOf_inj heq).1
  have hcomm_right : ∀ d : {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List},
      q8Comm b d = oneQ := by
    intro d
    let yd : Qt := qtOf oneQ d
    have hmem_yd : proj 4 (ZMod 3) (yd : SpecialLinearGroup (Fin 4) (ZMod 3)) ∈
        Qt.map (proj 4 (ZMod 3)) :=
      Subgroup.mem_map_of_mem (proj 4 (ZMod 3)) yd.2
    have hcent := congrArg (fun w : ↥(Qt.map (proj 4 (ZMod 3))) =>
      (w : projectiveSL 4 (ZMod 3)))
      (hcentral ⟨proj 4 (ZMod 3) (yd : SpecialLinearGroup (Fin 4) (ZMod 3)), hmem_yd⟩)
    have hcent' : proj 4 (ZMod 3) (q : SpecialLinearGroup (Fin 4) (ZMod 3)) *
        proj 4 (ZMod 3) (yd : SpecialLinearGroup (Fin 4) (ZMod 3)) =
        proj 4 (ZMod 3) (yd : SpecialLinearGroup (Fin 4) (ZMod 3)) *
          proj 4 (ZMod 3) (q : SpecialLinearGroup (Fin 4) (ZMod 3)) := by
      simpa [hqy] using hcent.symm
    have hcomm_psl : ⁅proj 4 (ZMod 3) (q : SpecialLinearGroup (Fin 4) (ZMod 3)),
        proj 4 (ZMod 3) (yd : SpecialLinearGroup (Fin 4) (ZMod 3))⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr hcent'
    have hker : ⁅q, yd⁆ ∈ ((proj 4 (ZMod 3)).comp Qt.subtype).ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement]
      simpa [MonoidHom.comp_apply] using hcomm_psl
    have hmem_z2 : ⁅q, yd⁆ ∈ Subgroup.zpowers z2 := by
      rwa [ker_proj_Qt_eq] at hker
    have hformula : ⁅q, yd⁆ = qtOf oneQ (q8Comm b d) := by
      rw [← hq_ab, show yd = qtOf oneQ d from rfl, qtOf_commutator, q8Comm_one_right]
    have h1or2 : qtOf oneQ (q8Comm b d) = 1 ∨ qtOf oneQ (q8Comm b d) = z2 := by
      rw [← hformula]
      exact mem_zpowers_z2_iff.mp hmem_z2
    have hne : qtOf oneQ (q8Comm b d) ≠ z2 := by
      intro hh
      have ha : oneQ = negOne2 :=
        (qtOf_inj (by simpa [z2] using hh)).1
      exact oneQ_ne_negOne2 ha
    have hone : qtOf oneQ (q8Comm b d) = 1 := by
      rcases h1or2 with h | h
      · exact h
      · exact absurd h hne
    have heq : qtOf oneQ (q8Comm b d) = qtOf oneQ oneQ := by
      rw [hone, qtOf_one]
    exact (qtOf_inj heq).2
  have ha : a = oneQ ∨ a = negOne2 :=
    (q8_mul_comm_iff_central a).mp fun c =>
      (q8Comm_eq_one_iff_commute a c).mp (hcomm_left c)
  have hb : b = oneQ ∨ b = negOne2 :=
    (q8_mul_comm_iff_central b).mp fun d =>
      (q8Comm_eq_one_iff_commute b d).mp (hcomm_right d)
  rw [← hq_ab]
  exact qtOf_one_or_negOne_mem_K4 a b ha hb

theorem center_map_le_zpowers :
    (Subgroup.center (Qt.map (proj 4 (ZMod 3)))).map
        (Qt.map (proj 4 (ZMod 3))).subtype ≤
      Subgroup.zpowers (proj 4 (ZMod 3) AS35W.dSL) := by
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨q, hq, hqy⟩ := y.2
  let qq : Qt := ⟨q, hq⟩
  have hqK4 : qq ∈ K4 := mem_K4_of_center_lift (q := qq) (y := y) hy hqy.symm
  have hmem : (y : projectiveSL 4 (ZMod 3)) ∈
      K4.map ((proj 4 (ZMod 3)).comp Qt.subtype) := by
    rw [← hqy]
    exact Subgroup.mem_map_of_mem _ hqK4
  rwa [K4_map_eq_zpowers] at hmem

theorem proj_dSL_mem_center :
    (⟨proj 4 (ZMod 3) AS35W.dSL,
      Subgroup.mem_map_of_mem (proj 4 (ZMod 3)) dSL_mem_Qt⟩ :
      ↥(Qt.map (proj 4 (ZMod 3)))) ∈
      Subgroup.center (Qt.map (proj 4 (ZMod 3))) := by
  rw [Subgroup.mem_center_iff]
  intro z
  apply Subtype.ext
  show (z : projectiveSL 4 (ZMod 3)) * proj 4 (ZMod 3) AS35W.dSL =
    proj 4 (ZMod 3) AS35W.dSL * (z : projectiveSL 4 (ZMod 3))
  obtain ⟨q, hq, hqz⟩ := z.2
  rw [← hqz]
  rw [← map_mul, ← map_mul, AS35W.comm_dSL_of_mem_Qt hq]

theorem zpowers_proj_dSL_le_center_map :
    Subgroup.zpowers (proj 4 (ZMod 3) AS35W.dSL) ≤
      (Subgroup.center (Qt.map (proj 4 (ZMod 3)))).map
        (Qt.map (proj 4 (ZMod 3))).subtype := by
  rw [Subgroup.zpowers_le]
  exact Subgroup.mem_map_of_mem _ proj_dSL_mem_center

theorem center_map_subtype_eq_zpowers :
    (Subgroup.center (Qt.map (proj 4 (ZMod 3)))).map
        (Qt.map (proj 4 (ZMod 3))).subtype =
      Subgroup.zpowers (proj 4 (ZMod 3) AS35W.dSL) :=
  le_antisymm center_map_le_zpowers zpowers_proj_dSL_le_center_map

theorem commutator_Qt_map_eq_zpowers :
    ⁅Qt.map (proj 4 (ZMod 3)), Qt.map (proj 4 (ZMod 3))⁆ =
      Subgroup.zpowers (proj 4 (ZMod 3) AS35W.dSL) := by
  have hmap := Subgroup.map_commutator (⊤ : Subgroup Qt) (⊤ : Subgroup Qt)
    ((proj 4 (ZMod 3)).comp Qt.subtype)
  have htop : (⊤ : Subgroup Qt).map ((proj 4 (ZMod 3)).comp Qt.subtype) =
      Qt.map (proj 4 (ZMod 3)) := by
    rw [← MonoidHom.range_eq_map, map_eq_range]
  rw [commutator_top_eq_K4, K4_map_eq_zpowers, htop] at hmap
  exact hmap.symm

theorem isExtraspecial2_Qt_map : IsExtraspecial2 (Qt.map (proj 4 (ZMod 3))) := by
  refine ⟨isPGroup_two_Qt_map, ?_, ?_⟩
  · rw [commutator_Qt_map_eq_zpowers, center_map_subtype_eq_zpowers]
  · rw [commutator_Qt_map_eq_zpowers, Nat.card_zpowers, orderOf_proj_dSL]

theorem isExtraspecial2_Qa_proj_dSL
    (h : HasWidth (Qa (proj 4 (ZMod 3) AS35W.dSL)) 2) :
    IsExtraspecial2 (Qa (proj 4 (ZMod 3) AS35W.dSL)) := by
  rw [Qa_proj_dSL h]
  exact isExtraspecial2_Qt_map

@[expose] def Ct : Subgroup (SpecialLinearGroup (Fin 4) (ZMod 3)) :=
  CentralizerZ.comap (proj 4 (ZMod 3))

theorem mem_Ct_iff {h : SpecialLinearGroup (Fin 4) (ZMod 3)} :
    h ∈ Ct ↔ proj 4 (ZMod 3) h ∈ CentralizerZ := Iff.rfl

theorem comm_of_mem_Ct {h : SpecialLinearGroup (Fin 4) (ZMod 3)} (hh : h ∈ Ct) :
    proj 4 (ZMod 3) h * proj 4 (ZMod 3) AS35W.dSL =
      proj 4 (ZMod 3) AS35W.dSL * proj 4 (ZMod 3) h :=
  ((Subgroup.mem_centralizer_iff.mp hh) _ (Set.mem_singleton _)).symm

theorem Qt_le_Ct : Qt ≤ Ct := by
  intro q hq
  rw [mem_Ct_iff, Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  rw [← map_mul, ← map_mul, AS35W.comm_dSL_of_mem_Qt hq]

theorem dSL_eq_blkSL : AS35W.dSL = blkSL 1 negOne8 := by
  rw [← s2_eq_dSL, s2, qtOf_eq_blkSL, q8SL_one, q8SL_negOne, Subgroup.coe_one]

theorem blkSL_fst_mul_dSL (C : SpecialLinearGroup (Fin 2) (ZMod 3)) :
    blkSL C 1 * AS35W.dSL = AS35W.dSL * blkSL C 1 := by
  rw [dSL_eq_blkSL]
  simp only [blkSL_mul, mul_one, one_mul]

theorem blkSL_fst_mem_Ct (C : SpecialLinearGroup (Fin 2) (ZMod 3)) : blkSL C 1 ∈ Ct := by
  rw [mem_Ct_iff, Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  rw [← map_mul, ← map_mul, blkSL_fst_mul_dSL]

theorem coe_negOne8 : ((negOne8 : q8Sub) : Matrix (Fin 2) (Fin 2) (ZMod 3)) = -1 := rfl

theorem negOne8_comm (C : SpecialLinearGroup (Fin 2) (ZMod 3)) :
    negOne8 * C = C * negOne8 := by
  apply Subtype.ext
  show ((negOne8 : q8Sub) : Matrix (Fin 2) (Fin 2) (ZMod 3)) * (C : Matrix (Fin 2) (Fin 2)
      (ZMod 3)) = (C : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
        ((negOne8 : q8Sub) : Matrix (Fin 2) (Fin 2) (ZMod 3))
  rw [coe_negOne8, AS35W.negOne_mul, AS35W.mul_negOne]

theorem blkSL_snd_mul_dSL (C : SpecialLinearGroup (Fin 2) (ZMod 3)) :
    blkSL 1 C * AS35W.dSL = AS35W.dSL * blkSL 1 C := by
  rw [dSL_eq_blkSL]
  simp only [blkSL_mul, mul_one, negOne8_comm]

theorem blkSL_snd_mem_Ct (C : SpecialLinearGroup (Fin 2) (ZMod 3)) : blkSL 1 C ∈ Ct := by
  rw [mem_Ct_iff, Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  rw [← map_mul, ← map_mul, blkSL_snd_mul_dSL]

@[expose] def swap4 : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

theorem det_swap4 : swap4.det = 1 := by decide

theorem swap4_self : swap4 * swap4 = 1 := by decide

theorem swap4_mul_dSL :
    swap4 * (AS35W.dSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) =
      -((AS35W.dSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) * swap4) := by decide

@[expose] def W : SpecialLinearGroup (Fin 4) (ZMod 3) := ⟨swap4, det_swap4⟩

theorem coe_W : (W : Matrix (Fin 4) (Fin 4) (ZMod 3)) = swap4 := rfl

@[expose] def negOneSL : SpecialLinearGroup (Fin 4) (ZMod 3) :=
  scalarElement (-1 : (ZMod 3)ˣ) (by decide)

theorem coe_negOneSL : (negOneSL : Matrix (Fin 4) (Fin 4) (ZMod 3)) = -1 := by
  rw [negOneSL, coe_scalarElement, show ((-1 : (ZMod 3)ˣ) : ZMod 3) = -1 from rfl,
    scalar_four_neg_one]

theorem proj_negOneSL : proj 4 (ZMod 3) negOneSL = 1 := by
  rw [proj_eq_one_iff]
  exact scalarElement_mem_scalars (-1) (by decide)

theorem coe_mul_sl4 (A B : SpecialLinearGroup (Fin 4) (ZMod 3)) :
    ((A * B : SpecialLinearGroup (Fin 4) (ZMod 3)) : Matrix (Fin 4) (Fin 4) (ZMod 3)) =
      (A : Matrix (Fin 4) (Fin 4) (ZMod 3)) * (B : Matrix (Fin 4) (Fin 4) (ZMod 3)) := rfl

theorem negOne_four_mul (N : Matrix (Fin 4) (Fin 4) (ZMod 3)) :
    (-1 : Matrix (Fin 4) (Fin 4) (ZMod 3)) * N = -N := by
  rw [show (-1 : Matrix (Fin 4) (Fin 4) (ZMod 3)) =
    -(1 : Matrix (Fin 4) (Fin 4) (ZMod 3)) from rfl, Matrix.neg_mul, Matrix.one_mul]

theorem W_mul_dSL : W * AS35W.dSL = negOneSL * (AS35W.dSL * W) := by
  apply SL_ext
  rw [coe_mul_sl4, coe_mul_sl4, coe_mul_sl4, coe_W, coe_negOneSL, swap4_mul_dSL,
    negOne_four_mul]

theorem proj_W_mul_dSL : proj 4 (ZMod 3) W * proj 4 (ZMod 3) AS35W.dSL =
    proj 4 (ZMod 3) AS35W.dSL * proj 4 (ZMod 3) W := by
  calc proj 4 (ZMod 3) W * proj 4 (ZMod 3) AS35W.dSL
      = proj 4 (ZMod 3) (W * AS35W.dSL) := (map_mul (proj 4 (ZMod 3)) _ _).symm
    _ = proj 4 (ZMod 3) (negOneSL * (AS35W.dSL * W)) := by rw [W_mul_dSL]
    _ = proj 4 (ZMod 3) negOneSL * proj 4 (ZMod 3) (AS35W.dSL * W) :=
        map_mul (proj 4 (ZMod 3)) _ _
    _ = proj 4 (ZMod 3) (AS35W.dSL * W) := by rw [proj_negOneSL, one_mul]
    _ = proj 4 (ZMod 3) AS35W.dSL * proj 4 (ZMod 3) W := map_mul (proj 4 (ZMod 3)) _ _

theorem W_mem_Ct : W ∈ Ct := by
  rw [mem_Ct_iff, Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact proj_W_mul_dSL.symm

theorem conj_mem_Qt_of_mem_Ct {g : SpecialLinearGroup (Fin 4) (ZMod 3)} (hg : g ∈ Ct)
    {m : SpecialLinearGroup (Fin 4) (ZMod 3)} (hm : m ∈ Qt) : g * m * g⁻¹ ∈ Qt :=
  AS35W.conj_mem_Qt_of_comm_or_anticomm (branch_of_comm (comm_of_mem_Ct hg)) hm

@[expose] def conjOn (g : Ct) (m : Qt) : Qt :=
  ⟨(g : SpecialLinearGroup (Fin 4) (ZMod 3)) * (m : SpecialLinearGroup (Fin 4) (ZMod 3)) *
    (g : SpecialLinearGroup (Fin 4) (ZMod 3))⁻¹, conj_mem_Qt_of_mem_Ct g.2 m.2⟩

theorem qtOf_eq_of_val {a b : {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List}} {x : Qt}
    (h : ((x : Qt).1 : Matrix (Fin 4) (Fin 4) (ZMod 3)) = blkDiag a.1 b.1) : x = qtOf a b := by
  apply Qt_ext
  rw [h, qtOf_val]

theorem coe_q8SL (a : {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List}) :
    ((q8SL a : q8Sub) : Matrix (Fin 2) (Fin 2) (ZMod 3)) = a.1 := rfl

theorem blkSL_conj_fst (C : SpecialLinearGroup (Fin 2) (ZMod 3))
    (a b : {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List})
    (c : {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List})
    (h : (C : Matrix (Fin 2) (Fin 2) (ZMod 3)) * a.1 *
      ((C⁻¹ : SpecialLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) = c.1) :
    (blkSL C 1 : SpecialLinearGroup (Fin 4) (ZMod 3)) * (qtOf a b : Qt).1 * (blkSL C 1)⁻¹ =
      (qtOf c b : Qt).1 := by
  have hq8 : (C * q8SL a * C⁻¹ : SpecialLinearGroup (Fin 2) (ZMod 3)) = q8SL c := by
    apply Subtype.ext
    show (C : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
      ((q8SL a : q8Sub) : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
      ((C⁻¹ : SpecialLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) = c.1
    rw [coe_q8SL]
    exact h
  rw [blkSL_inv, inv_one, qtOf_eq_blkSL, qtOf_eq_blkSL, blkSL_mul, blkSL_mul]
  simp only [mul_one, one_mul]
  rw [hq8]

theorem conjOn_blkSL_fst_eq (C : SpecialLinearGroup (Fin 2) (ZMod 3))
    (a b c : {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List})
    (h : (C : Matrix (Fin 2) (Fin 2) (ZMod 3)) * a.1 *
      ((C⁻¹ : SpecialLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) = c.1) :
    conjOn ⟨blkSL C 1, blkSL_fst_mem_Ct C⟩ (qtOf a b) = qtOf c b := by
  apply Qt_ext
  exact congrArg (fun x : SpecialLinearGroup (Fin 4) (ZMod 3) =>
    (x : Matrix (Fin 4) (Fin 4) (ZMod 3))) (blkSL_conj_fst C a b c h)

theorem blkSL_conj_snd (C : SpecialLinearGroup (Fin 2) (ZMod 3))
    (a b : {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List})
    (c : {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List})
    (h : (C : Matrix (Fin 2) (Fin 2) (ZMod 3)) * b.1 *
      ((C⁻¹ : SpecialLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) = c.1) :
    (blkSL 1 C : SpecialLinearGroup (Fin 4) (ZMod 3)) * (qtOf a b : Qt).1 * (blkSL 1 C)⁻¹ =
      (qtOf a c : Qt).1 := by
  have hq8 : (C * q8SL b * C⁻¹ : SpecialLinearGroup (Fin 2) (ZMod 3)) = q8SL c := by
    apply Subtype.ext
    show (C : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
      ((q8SL b : q8Sub) : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
      ((C⁻¹ : SpecialLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) = c.1
    rw [coe_q8SL]
    exact h
  rw [blkSL_inv, inv_one, qtOf_eq_blkSL, qtOf_eq_blkSL, blkSL_mul, blkSL_mul]
  simp only [mul_one, one_mul]
  rw [hq8]

theorem conjOn_blkSL_snd_eq (C : SpecialLinearGroup (Fin 2) (ZMod 3))
    (a b c : {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List})
    (h : (C : Matrix (Fin 2) (Fin 2) (ZMod 3)) * b.1 *
      ((C⁻¹ : SpecialLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) = c.1) :
    conjOn ⟨blkSL 1 C, blkSL_snd_mem_Ct C⟩ (qtOf a b) = qtOf a c := by
  apply Qt_ext
  exact congrArg (fun x : SpecialLinearGroup (Fin 4) (ZMod 3) =>
    (x : Matrix (Fin 4) (Fin 4) (ZMod 3))) (blkSL_conj_snd C a b c h)

theorem swap4_blkDiag (a b : Matrix (Fin 2) (Fin 2) (ZMod 3)) :
    swap4 * blkDiag a b * swap4 = blkDiag b a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swap4, blkDiag, Matrix.mul_apply, Fin.sum_univ_four]

theorem W_sq : W * W = (1 : SpecialLinearGroup (Fin 4) (ZMod 3)) := by decide

theorem W_inv : W⁻¹ = W := inv_eq_of_mul_eq_one_right W_sq

theorem coe_inv_W :
    (((W⁻¹ : SpecialLinearGroup (Fin 4) (ZMod 3))) : Matrix (Fin 4) (Fin 4) (ZMod 3)) = swap4 := by
  rw [W_inv]
  exact coe_W

theorem W_conj (a b : {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List}) :
    (W : SpecialLinearGroup (Fin 4) (ZMod 3)) * (qtOf a b : Qt).1 *
      (W : SpecialLinearGroup (Fin 4) (ZMod 3))⁻¹ = (qtOf b a : Qt).1 := by
  apply SL_ext
  rw [coe_mul_sl4, coe_mul_sl4, coe_W, qtOf_val, coe_inv_W]
  exact swap4_blkDiag a.1 b.1

theorem conjOn_W_eq (a b : {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List}) :
    conjOn ⟨W, W_mem_Ct⟩ (qtOf a b) = qtOf b a := by
  apply Qt_ext
  exact congrArg (fun x : SpecialLinearGroup (Fin 4) (ZMod 3) =>
    (x : Matrix (Fin 4) (Fin 4) (ZMod 3))) (W_conj a b)

@[expose] def MOf (N : Subgroup (projectiveSL 4 (ZMod 3))) : Subgroup Qt :=
  N.comap ((proj 4 (ZMod 3)).comp Qt.subtype)

theorem map_MOf_eq (h : HasWidth (Qa (proj 4 (ZMod 3) AS35W.dSL)) 2)
    {N : Subgroup (projectiveSL 4 (ZMod 3))} (hN : N ≤ Qa (proj 4 (ZMod 3) AS35W.dSL)) :
    (MOf N).map ((proj 4 (ZMod 3)).comp Qt.subtype) = N := by
  refine Subgroup.map_comap_eq_self ?_
  rw [map_eq_range, ← Qa_proj_dSL h]
  exact hN

theorem K4_le_MOf {N : Subgroup (projectiveSL 4 (ZMod 3))}
    (hzN : Subgroup.zpowers (proj 4 (ZMod 3) AS35W.dSL) ≤ N) : K4 ≤ MOf N := by
  intro k hk
  change ((proj 4 (ZMod 3)).comp Qt.subtype) k ∈ N
  refine hzN ?_
  rw [← K4_map_eq_zpowers]
  exact Subgroup.mem_map_of_mem _ hk

theorem conjOn_mem_MOf {N : Subgroup (projectiveSL 4 (ZMod 3))}
    (hNC : CentralizerZ ≤ Subgroup.normalizer (N : Set (projectiveSL 4 (ZMod 3))))
    (g : Ct) {m : Qt} (hm : m ∈ MOf N) : conjOn g m ∈ MOf N := by
  change ((proj 4 (ZMod 3)).comp Qt.subtype) m ∈ N at hm
  change ((proj 4 (ZMod 3)).comp Qt.subtype) (conjOn g m) ∈ N
  have hval : ((proj 4 (ZMod 3)).comp Qt.subtype) (conjOn g m) =
      proj 4 (ZMod 3) (g : SpecialLinearGroup (Fin 4) (ZMod 3)) *
        ((proj 4 (ZMod 3)).comp Qt.subtype) m *
        (proj 4 (ZMod 3) (g : SpecialLinearGroup (Fin 4) (ZMod 3)))⁻¹ := by
    show proj 4 (ZMod 3) ((conjOn g m : Qt) : SpecialLinearGroup (Fin 4) (ZMod 3)) = _
    rw [show ((conjOn g m : Qt) : SpecialLinearGroup (Fin 4) (ZMod 3)) =
      (g : SpecialLinearGroup (Fin 4) (ZMod 3)) * (m : SpecialLinearGroup (Fin 4) (ZMod 3)) *
        (g : SpecialLinearGroup (Fin 4) (ZMod 3))⁻¹ from rfl]
    rw [map_mul, map_mul, map_inv]
    rfl
  rw [hval]
  exact (Subgroup.le_normalizer_iff.mp hNC) _ (show proj 4 (ZMod 3) (g :
    SpecialLinearGroup (Fin 4) (ZMod 3)) ∈ CentralizerZ from g.2) _ hm


abbrev Q8 := {a : Matrix (Fin 2) (Fin 2) (ZMod 3) // a ∈ q8List}

@[expose] def i2 : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![0, 1; -1, 0]

@[expose] def j2 : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![1, 1; 1, -1]

@[expose] def k2 : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![1, -1; -1, -1]

@[expose] def c1 : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![1, 1; 0, 1]

@[expose] def c2 : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![1, 0; 1, 1]

@[expose] def c1' : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![1, -1; 0, 1]

@[expose] def c2' : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![1, 0; -1, 1]

@[expose] def q8i : Q8 := ⟨i2, by decide⟩

@[expose] def q8j : Q8 := ⟨j2, by decide⟩

@[expose] def q8k : Q8 := ⟨k2, by decide⟩

@[expose] def q8negi : Q8 := ⟨-i2, by decide⟩

@[expose] def q8negj : Q8 := ⟨-j2, by decide⟩

@[expose] def q8negk : Q8 := ⟨-k2, by decide⟩

@[expose] def c1SL : SpecialLinearGroup (Fin 2) (ZMod 3) := ⟨c1, by decide⟩

@[expose] def c2SL : SpecialLinearGroup (Fin 2) (ZMod 3) := ⟨c2, by decide⟩

theorem coe_c1SL : (c1SL : Matrix (Fin 2) (Fin 2) (ZMod 3)) = c1 := rfl

theorem coe_c2SL : (c2SL : Matrix (Fin 2) (Fin 2) (ZMod 3)) = c2 := rfl

theorem c1SL_inv_eq : c1SL⁻¹ = (⟨c1', by decide⟩ : SpecialLinearGroup (Fin 2) (ZMod 3)) :=
  inv_eq_of_mul_eq_one_right (by decide)

theorem c2SL_inv_eq : c2SL⁻¹ = (⟨c2', by decide⟩ : SpecialLinearGroup (Fin 2) (ZMod 3)) :=
  inv_eq_of_mul_eq_one_right (by decide)

theorem inv_c1SL :
    ((c1SL⁻¹ : SpecialLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) = c1' := by
  rw [c1SL_inv_eq]

theorem inv_c2SL :
    ((c2SL⁻¹ : SpecialLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) = c2' := by
  rw [c2SL_inv_eq]

theorem conj_orbit_I : ∀ a : Matrix (Fin 2) (Fin 2) (ZMod 3), a ∈ q8List →
    a ≠ (1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) → a ≠ -1 →
    (a = i2 ∨ a = -i2 ∨ c1 * a * c1' = i2 ∨ c1 * a * c1' = -i2 ∨
      c2 * a * c2' = i2 ∨ c2 * a * c2' = -i2) := by decide

theorem conj_orbit_J : ∀ a : Matrix (Fin 2) (Fin 2) (ZMod 3), a ∈ q8List →
    a ≠ (1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) → a ≠ -1 →
    (a = j2 ∨ a = -j2 ∨ c1 * a * c1' = j2 ∨ c1 * a * c1' = -j2 ∨
      c2 * a * c2' = j2 ∨ c2 * a * c2' = -j2) := by decide

theorem s1_sq : s1 * s1 = (1 : Qt) := by decide

theorem s2_sq : s2 * s2 = (1 : Qt) := by decide

theorem q8Mul_oneQ_left (c : Q8) : q8Mul oneQ c = c := by
  apply Subtype.ext
  show (1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) * c.1 = c.1
  rw [one_mul]

theorem q8Mul_oneQ_right (c : Q8) : q8Mul c oneQ = c := by
  apply Subtype.ext
  show c.1 * (1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) = c.1
  rw [mul_one]

theorem q8Mul_negOne_self : q8Mul negOne2 negOne2 = oneQ := by decide

theorem q8k_mul : q8Mul q8i q8j = q8k := by decide

theorem q8_sq : ∀ a : Q8, q8Mul a a = oneQ ∨ q8Mul a a = negOne2 := by decide

theorem q8_cases : ∀ c : Q8, c = oneQ ∨ c = negOne2 ∨ c = q8i ∨ c = q8negi ∨
    c = q8j ∨ c = q8negj ∨ c = q8k ∨ c = q8negk := by decide

theorem qtOf_mul_split (a b : Q8) : qtOf a b = qtOf a oneQ * qtOf oneQ b := by
  rw [qtOf_mul, q8Mul_oneQ_right, q8Mul_oneQ_left]

theorem q8negi_eq : q8negi = q8Mul negOne2 q8i := by
  apply Subtype.ext
  show (-i2 : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
    ((negOne2 : Q8) : Matrix (Fin 2) (Fin 2) (ZMod 3)) * i2
  rw [show ((negOne2 : Q8) : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
    (-1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) from rfl, AS35W.negOne_mul]

theorem q8negj_eq : q8negj = q8Mul negOne2 q8j := by
  apply Subtype.ext
  show (-j2 : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
    ((negOne2 : Q8) : Matrix (Fin 2) (Fin 2) (ZMod 3)) * j2
  rw [show ((negOne2 : Q8) : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
    (-1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) from rfl, AS35W.negOne_mul]

theorem q8negk_eq : q8negk = q8Mul negOne2 q8k := by
  apply Subtype.ext
  show (-k2 : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
    ((negOne2 : Q8) : Matrix (Fin 2) (Fin 2) (ZMod 3)) * k2
  rw [show ((negOne2 : Q8) : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
    (-1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) from rfl, AS35W.negOne_mul]

theorem qtOf_mul_negOne (c b : Q8) :
    qtOf (q8Mul negOne2 c) b = s1 * qtOf c b := by
  rw [s1, qtOf_mul, q8Mul_oneQ_left]

theorem mem_qtOf_mul_negOne_iff {M : Subgroup Qt} (hK4 : K4 ≤ M) (c b : Q8) :
    qtOf (q8Mul negOne2 c) b ∈ M ↔ qtOf c b ∈ M := by
  constructor
  · intro h
    rw [qtOf_mul_negOne c b] at h
    have h2 : qtOf c b = s1 * (s1 * qtOf c b) := by
      rw [← mul_assoc, s1_sq, one_mul]
    rw [h2]
    exact M.mul_mem (hK4 s1_mem_K4) h
  · intro h
    rw [qtOf_mul_negOne c b]
    exact M.mul_mem (hK4 s1_mem_K4) h

theorem q8Mul_negOne_comm (c : Q8) : q8Mul negOne2 c = q8Mul c negOne2 := by
  apply Subtype.ext
  show ((negOne2 : Q8) : Matrix (Fin 2) (Fin 2) (ZMod 3)) * c.1 =
    c.1 * ((negOne2 : Q8) : Matrix (Fin 2) (Fin 2) (ZMod 3))
  rw [show ((negOne2 : Q8) : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
    (-1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) from rfl, AS35W.negOne_mul, AS35W.mul_negOne]

theorem qtOf_mul_negOne_snd (a c : Q8) :
    qtOf a (q8Mul negOne2 c) = qtOf a c * s2 := by
  rw [s2, qtOf_mul, q8Mul_oneQ_right, q8Mul_negOne_comm]

theorem mem_qtOf_mul_negOne_snd_iff {M : Subgroup Qt} (hK4 : K4 ≤ M) (a c : Q8) :
    qtOf a (q8Mul negOne2 c) ∈ M ↔ qtOf a c ∈ M := by
  constructor
  · intro h
    rw [qtOf_mul_negOne_snd a c] at h
    have h2 : qtOf a c = qtOf a c * s2 * s2 := by
      rw [mul_assoc, s2_sq, mul_one]
    rw [h2]
    exact M.mul_mem h (hK4 s2_mem_K4)
  · intro h
    rw [qtOf_mul_negOne_snd a c]
    exact M.mul_mem h (hK4 s2_mem_K4)

theorem qtOf_snd_negOne (c : Q8) : qtOf c oneQ = qtOf c negOne2 * s2 := by
  rw [s2, qtOf_mul, q8Mul_oneQ_right, q8Mul_negOne_self]

theorem mem_qtOf_oneQ_of_sign {M : Subgroup Qt} (hK4 : K4 ≤ M) {c b : Q8}
    (hb : b = oneQ ∨ b = negOne2) (h : qtOf c b ∈ M) : qtOf c oneQ ∈ M := by
  rcases hb with rfl | rfl
  · exact h
  · rw [qtOf_snd_negOne c]
    exact M.mul_mem h (hK4 s2_mem_K4)

theorem mem_qtOf_conj_fst_c1 {M : Subgroup Qt}
    (hinv : ∀ (g : Ct) (m : Qt), m ∈ M → conjOn g m ∈ M) {a b c : Q8}
    (h : c1 * (a : Matrix (Fin 2) (Fin 2) (ZMod 3)) * c1' = c.1) (hm : qtOf a b ∈ M) :
    qtOf c b ∈ M := by
  have hh : (c1SL : Matrix (Fin 2) (Fin 2) (ZMod 3)) * (a : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
      ((c1SL⁻¹ : SpecialLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
        c.1 := by
    rw [coe_c1SL, inv_c1SL]
    exact h
  rw [← conjOn_blkSL_fst_eq c1SL a b c hh]
  exact hinv _ _ hm

theorem mem_qtOf_conj_fst_c2 {M : Subgroup Qt}
    (hinv : ∀ (g : Ct) (m : Qt), m ∈ M → conjOn g m ∈ M) {a b c : Q8}
    (h : c2 * (a : Matrix (Fin 2) (Fin 2) (ZMod 3)) * c2' = c.1) (hm : qtOf a b ∈ M) :
    qtOf c b ∈ M := by
  have hh : (c2SL : Matrix (Fin 2) (Fin 2) (ZMod 3)) * (a : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
      ((c2SL⁻¹ : SpecialLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
        c.1 := by
    rw [coe_c2SL, inv_c2SL]
    exact h
  rw [← conjOn_blkSL_fst_eq c2SL a b c hh]
  exact hinv _ _ hm

theorem mem_qtOf_conj_snd_c1 {M : Subgroup Qt}
    (hinv : ∀ (g : Ct) (m : Qt), m ∈ M → conjOn g m ∈ M) {a b c : Q8}
    (h : c1 * (b : Matrix (Fin 2) (Fin 2) (ZMod 3)) * c1' = c.1) (hm : qtOf a b ∈ M) :
    qtOf a c ∈ M := by
  have hh : (c1SL : Matrix (Fin 2) (Fin 2) (ZMod 3)) * (b : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
      ((c1SL⁻¹ : SpecialLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
        c.1 := by
    rw [coe_c1SL, inv_c1SL]
    exact h
  rw [← conjOn_blkSL_snd_eq c1SL a b c hh]
  exact hinv _ _ hm

theorem mem_qtOf_conj_snd_c2 {M : Subgroup Qt}
    (hinv : ∀ (g : Ct) (m : Qt), m ∈ M → conjOn g m ∈ M) {a b c : Q8}
    (h : c2 * (b : Matrix (Fin 2) (Fin 2) (ZMod 3)) * c2' = c.1) (hm : qtOf a b ∈ M) :
    qtOf a c ∈ M := by
  have hh : (c2SL : Matrix (Fin 2) (Fin 2) (ZMod 3)) * (b : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
      ((c2SL⁻¹ : SpecialLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
        c.1 := by
    rw [coe_c2SL, inv_c2SL]
    exact h
  rw [← conjOn_blkSL_snd_eq c2SL a b c hh]
  exact hinv _ _ hm

theorem mem_qtOf_q8i_of_noncentral {M : Subgroup Qt} (hK4 : K4 ≤ M)
    (hinv : ∀ (g : Ct) (m : Qt), m ∈ M → conjOn g m ∈ M) {a b : Q8}
    (hm : qtOf a b ∈ M) (ha : a ≠ oneQ) (ha' : a ≠ negOne2) : qtOf q8i b ∈ M := by
  have h1 : (a : Matrix (Fin 2) (Fin 2) (ZMod 3)) ≠ 1 := fun h => ha (Subtype.ext h)
  have h2 : (a : Matrix (Fin 2) (Fin 2) (ZMod 3)) ≠ -1 := fun h => ha' (Subtype.ext h)
  have hmem : qtOf q8i b ∈ M ∨ qtOf q8negi b ∈ M := by
    rcases conj_orbit_I a.1 a.2 h1 h2 with h | h | h | h | h | h
    · left
      rw [← show a = q8i from Subtype.ext h]
      exact hm
    · right
      rw [← show a = q8negi from Subtype.ext h]
      exact hm
    · exact Or.inl (mem_qtOf_conj_fst_c1 hinv h hm)
    · exact Or.inr (mem_qtOf_conj_fst_c1 hinv h hm)
    · exact Or.inl (mem_qtOf_conj_fst_c2 hinv h hm)
    · exact Or.inr (mem_qtOf_conj_fst_c2 hinv h hm)
  rcases hmem with h | h
  · exact h
  · rw [q8negi_eq] at h
    exact (mem_qtOf_mul_negOne_iff hK4 q8i b).mp h

theorem mem_qtOf_q8j_of_noncentral {M : Subgroup Qt} (hK4 : K4 ≤ M)
    (hinv : ∀ (g : Ct) (m : Qt), m ∈ M → conjOn g m ∈ M) {a b : Q8}
    (hm : qtOf a b ∈ M) (ha : a ≠ oneQ) (ha' : a ≠ negOne2) : qtOf q8j b ∈ M := by
  have h1 : (a : Matrix (Fin 2) (Fin 2) (ZMod 3)) ≠ 1 := fun h => ha (Subtype.ext h)
  have h2 : (a : Matrix (Fin 2) (Fin 2) (ZMod 3)) ≠ -1 := fun h => ha' (Subtype.ext h)
  have hmem : qtOf q8j b ∈ M ∨ qtOf q8negj b ∈ M := by
    rcases conj_orbit_J a.1 a.2 h1 h2 with h | h | h | h | h | h
    · left
      rw [← show a = q8j from Subtype.ext h]
      exact hm
    · right
      rw [← show a = q8negj from Subtype.ext h]
      exact hm
    · exact Or.inl (mem_qtOf_conj_fst_c1 hinv h hm)
    · exact Or.inr (mem_qtOf_conj_fst_c1 hinv h hm)
    · exact Or.inl (mem_qtOf_conj_fst_c2 hinv h hm)
    · exact Or.inr (mem_qtOf_conj_fst_c2 hinv h hm)
  rcases hmem with h | h
  · exact h
  · rw [q8negj_eq] at h
    exact (mem_qtOf_mul_negOne_iff hK4 q8j b).mp h

theorem mem_qtOf_snd_q8i_of_noncentral {M : Subgroup Qt} (hK4 : K4 ≤ M)
    (hinv : ∀ (g : Ct) (m : Qt), m ∈ M → conjOn g m ∈ M) {a b : Q8}
    (hm : qtOf a b ∈ M) (hb : b ≠ oneQ) (hb' : b ≠ negOne2) : qtOf a q8i ∈ M := by
  have h1 : (b : Matrix (Fin 2) (Fin 2) (ZMod 3)) ≠ 1 := fun h => hb (Subtype.ext h)
  have h2 : (b : Matrix (Fin 2) (Fin 2) (ZMod 3)) ≠ -1 := fun h => hb' (Subtype.ext h)
  have hmem : qtOf a q8i ∈ M ∨ qtOf a q8negi ∈ M := by
    rcases conj_orbit_I b.1 b.2 h1 h2 with h | h | h | h | h | h
    · left
      rw [← show b = q8i from Subtype.ext h]
      exact hm
    · right
      rw [← show b = q8negi from Subtype.ext h]
      exact hm
    · exact Or.inl (mem_qtOf_conj_snd_c1 hinv h hm)
    · exact Or.inr (mem_qtOf_conj_snd_c1 hinv h hm)
    · exact Or.inl (mem_qtOf_conj_snd_c2 hinv h hm)
    · exact Or.inr (mem_qtOf_conj_snd_c2 hinv h hm)
  rcases hmem with h | h
  · exact h
  · rw [q8negi_eq] at h
    exact (mem_qtOf_mul_negOne_snd_iff hK4 a q8i).mp h

theorem mem_qtOf_snd_q8j_of_noncentral {M : Subgroup Qt} (hK4 : K4 ≤ M)
    (hinv : ∀ (g : Ct) (m : Qt), m ∈ M → conjOn g m ∈ M) {a b : Q8}
    (hm : qtOf a b ∈ M) (hb : b ≠ oneQ) (hb' : b ≠ negOne2) : qtOf a q8j ∈ M := by
  have h1 : (b : Matrix (Fin 2) (Fin 2) (ZMod 3)) ≠ 1 := fun h => hb (Subtype.ext h)
  have h2 : (b : Matrix (Fin 2) (Fin 2) (ZMod 3)) ≠ -1 := fun h => hb' (Subtype.ext h)
  have hmem : qtOf a q8j ∈ M ∨ qtOf a q8negj ∈ M := by
    rcases conj_orbit_J b.1 b.2 h1 h2 with h | h | h | h | h | h
    · left
      rw [← show b = q8j from Subtype.ext h]
      exact hm
    · right
      rw [← show b = q8negj from Subtype.ext h]
      exact hm
    · exact Or.inl (mem_qtOf_conj_snd_c1 hinv h hm)
    · exact Or.inr (mem_qtOf_conj_snd_c1 hinv h hm)
    · exact Or.inl (mem_qtOf_conj_snd_c2 hinv h hm)
    · exact Or.inr (mem_qtOf_conj_snd_c2 hinv h hm)
  rcases hmem with h | h
  · exact h
  · rw [q8negj_eq] at h
    exact (mem_qtOf_mul_negOne_snd_iff hK4 a q8j).mp h

theorem all_fst_mem {M : Subgroup Qt} (hK4 : K4 ≤ M)
    (hI : qtOf q8i oneQ ∈ M) (hJ : qtOf q8j oneQ ∈ M) :
    ∀ c : Q8, qtOf c oneQ ∈ M := by
  intro c
  have hK : qtOf q8k oneQ ∈ M := by
    rw [show qtOf q8k oneQ = qtOf q8i oneQ * qtOf q8j oneQ from by
      rw [qtOf_mul, q8k_mul, q8Mul_oneQ_right]]
    exact M.mul_mem hI hJ
  rcases q8_cases c with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [qtOf_one]
    exact M.one_mem
  · exact hK4 s1_mem_K4
  · exact hI
  · rw [q8negi_eq]
    exact (mem_qtOf_mul_negOne_iff hK4 q8i oneQ).mpr hI
  · exact hJ
  · rw [q8negj_eq]
    exact (mem_qtOf_mul_negOne_iff hK4 q8j oneQ).mpr hJ
  · exact hK
  · rw [q8negk_eq]
    exact (mem_qtOf_mul_negOne_iff hK4 q8k oneQ).mpr hK

theorem eq_top_of_fst_noncentral {M : Subgroup Qt} (hK4 : K4 ≤ M)
    (hinv : ∀ (g : Ct) (m : Qt), m ∈ M → conjOn g m ∈ M) {a b : Q8}
    (hm : qtOf a b ∈ M) (ha : a ≠ oneQ) (ha' : a ≠ negOne2)
    (hb : b = oneQ ∨ b = negOne2) : M = ⊤ := by
  have hI : qtOf q8i b ∈ M := mem_qtOf_q8i_of_noncentral hK4 hinv hm ha ha'
  have hJ : qtOf q8j b ∈ M := mem_qtOf_q8j_of_noncentral hK4 hinv hm ha ha'
  have hI1 : qtOf q8i oneQ ∈ M := mem_qtOf_oneQ_of_sign hK4 hb hI
  have hJ1 : qtOf q8j oneQ ∈ M := mem_qtOf_oneQ_of_sign hK4 hb hJ
  have hfst : ∀ c : Q8, qtOf c oneQ ∈ M := all_fst_mem hK4 hI1 hJ1
  have hsnd : ∀ c : Q8, qtOf oneQ c ∈ M := by
    intro c
    rw [← conjOn_W_eq c oneQ]
    exact hinv ⟨W, W_mem_Ct⟩ _ (hfst c)
  rw [Subgroup.eq_top_iff']
  intro x
  rw [← qtOf_qtToPair x, qtOf_mul_split]
  exact M.mul_mem (hfst _) (hsnd _)

theorem eq_top_of_both_noncentral {M : Subgroup Qt} (hK4 : K4 ≤ M)
    (hinv : ∀ (g : Ct) (m : Qt), m ∈ M → conjOn g m ∈ M) {a b : Q8}
    (hm : qtOf a b ∈ M) (hb : b ≠ oneQ) (hb' : b ≠ negOne2) : M = ⊤ := by
  have h1 : qtOf a q8i ∈ M := mem_qtOf_snd_q8i_of_noncentral hK4 hinv hm hb hb'
  have h2 : qtOf a q8j ∈ M := mem_qtOf_snd_q8j_of_noncentral hK4 hinv hm hb hb'
  have h3 : qtOf (q8Mul a a) q8k ∈ M := by
    rw [← q8k_mul, ← qtOf_mul]
    exact M.mul_mem h1 h2
  have h4 : qtOf oneQ q8k ∈ M := by
    rcases q8_sq a with hs | hs
    · rwa [hs] at h3
    · rw [hs, ← q8Mul_oneQ_right negOne2] at h3
      exact (mem_qtOf_mul_negOne_iff hK4 oneQ q8k).mp h3
  have h5 : qtOf q8k oneQ ∈ M := by
    rw [← conjOn_W_eq oneQ q8k]
    exact hinv ⟨W, W_mem_Ct⟩ _ h4
  exact eq_top_of_fst_noncentral hK4 hinv h5 (by decide) (by decide) (Or.inl rfl)

theorem eq_K4_or_top {M : Subgroup Qt} (hK4 : K4 ≤ M)
    (hinv : ∀ (g : Ct) (m : Qt), m ∈ M → conjOn g m ∈ M) : M = K4 ∨ M = ⊤ := by
  by_cases hle : M ≤ K4
  · exact Or.inl (le_antisymm hle hK4)
  · right
    have hlt : ∃ x, x ∈ M ∧ x ∉ K4 := by
      by_contra h
      apply hle
      intro x hx
      by_contra hxK
      exact h ⟨x, hx, hxK⟩
    obtain ⟨x, hxM, hxK⟩ := hlt
    set a := (qtToPair x).1 with ha
    set b := (qtToPair x).2 with hb
    have hx : qtOf a b = x := qtOf_qtToPair x
    have hm : qtOf a b ∈ M := by
      rw [hx]
      exact hxM
    by_cases hca : a = oneQ ∨ a = negOne2
    · by_cases hcb : b = oneQ ∨ b = negOne2
      · exact absurd (by rw [← hx]; exact qtOf_one_or_negOne_mem_K4 a b hca hcb) hxK
      · have hswap : qtOf b a ∈ M := by
          rw [← conjOn_W_eq a b]
          exact hinv ⟨W, W_mem_Ct⟩ _ hm
        exact eq_top_of_fst_noncentral hK4 hinv hswap
          (fun h => hcb (Or.inl h)) (fun h => hcb (Or.inr h)) hca
    · by_cases hcb : b = oneQ ∨ b = negOne2
      · exact eq_top_of_fst_noncentral hK4 hinv hm
          (fun h => hca (Or.inl h)) (fun h => hca (Or.inr h)) hcb
      · exact eq_top_of_both_noncentral hK4 hinv hm
          (fun h => hcb (Or.inl h)) (fun h => hcb (Or.inr h))

theorem caseI_proj_dSL (h : HasWidth (Qa (proj 4 (ZMod 3) AS35W.dSL)) 2) :
    ∀ N : Subgroup (projectiveSL 4 (ZMod 3)),
      Subgroup.zpowers (proj 4 (ZMod 3) AS35W.dSL) ≤ N →
      N ≤ Qa (proj 4 (ZMod 3) AS35W.dSL) →
      Subgroup.centralizer ({proj 4 (ZMod 3) AS35W.dSL} : Set (projectiveSL 4 (ZMod 3))) ≤
        Subgroup.normalizer (N : Set (projectiveSL 4 (ZMod 3))) →
      N = Subgroup.zpowers (proj 4 (ZMod 3) AS35W.dSL) ∨
        N = Qa (proj 4 (ZMod 3) AS35W.dSL) := by
  intro N hzN hNQ hNC
  have hM : MOf N = K4 ∨ MOf N = ⊤ :=
    eq_K4_or_top (K4_le_MOf hzN) (fun g m hm => conjOn_mem_MOf hNC g hm)
  rcases hM with hM | hM
  · left
    rw [← map_MOf_eq h hNQ, hM, K4_map_eq_zpowers]
  · right
    rw [← map_MOf_eq h hNQ, hM, ← MonoidHom.range_eq_map, map_eq_range, ← Qa_proj_dSL h]

noncomputable def projectiveSLFourMulEquiv :
    projectiveSL 4 (ZMod 3) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 3) :=
  QuotientGroup.congr (scalars 4 (ZMod 3))
    (Subgroup.center (SpecialLinearGroup (Fin 4) (ZMod 3))) (MulEquiv.refl _) (by
      show (scalars 4 (ZMod 3)).map (MulEquiv.refl (SpecialLinearGroup (Fin 4) (ZMod 3))).toMonoidHom
        = Subgroup.center (SpecialLinearGroup (Fin 4) (ZMod 3))
      rw [show (MulEquiv.refl (SpecialLinearGroup (Fin 4) (ZMod 3))).toMonoidHom
        = MonoidHom.id _ from rfl, Subgroup.map_id]
      exact scalars_eq_center 4 (ZMod 3))

end CFSG.RankThree.GF2n.Tim79a
