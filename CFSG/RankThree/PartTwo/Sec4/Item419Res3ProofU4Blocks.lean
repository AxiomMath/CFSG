module

public import CFSG.RankThree.PartTwo.Sec4.Item419Res3ProofComp
public import CFSG.RankThree.PartTwo.KFacts.KS222U4OddBlock
import CFSG.CharacterTheory.Burnside
import CFSG.RankThree.PartOne.TCX.Plane
import CFSG.RankThree.PartOne.KF.R7Levi

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item419Res3

open Matrix CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement
open CFSG.RankThree.PartOne.KFU (diagU diagU_val apply_eq_zero_of_commute_diagU)
open CFSG.RankThree.PartTwo.Sec21.U4OddLines (blk2 blk2_one blk2_mul blk2_injective det_blk2
  blk2_gram blkGL2 coe_blkGL2 blkSU2 blkSU2_le blkSU2Equiv nonempty_blkSU2_mulEquiv mem_blkSU2_of
  dvecD0 phiD0 ker_phiD0 blkSU2_le_centralizer)

variable {K : Type} [Field K] {f : ℕ}

@[expose] def blk2L (Y : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, Y 0 0, Y 0 1; 0, 0, Y 1 0, Y 1 1]

theorem blk2L_one : blk2L (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk2L]

theorem blk2L_mul (X Y : Matrix (Fin 2) (Fin 2) K) : blk2L (X * Y) = blk2L X * blk2L Y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk2L, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four]

theorem blk2L_injective {X Y : Matrix (Fin 2) (Fin 2) K} (h : blk2L X = blk2L Y) : X = Y := by
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [blk2L] using congrFun (congrFun h 2) 2
  · simpa [blk2L] using congrFun (congrFun h 2) 3
  · simpa [blk2L] using congrFun (congrFun h 3) 2
  · simpa [blk2L] using congrFun (congrFun h 3) 3

theorem det_blk2L (Y : Matrix (Fin 2) (Fin 2) K) : (blk2L Y).det = Y.det := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, blk2L, Fin.succAbove]

theorem blk2L_gram (h : UnitaryFieldData 2 f K) (X Y : Matrix (Fin 2) (Fin 2) K) :
    ((blk2L X).map h.bar)ᵀ * blk2L Y = blk2L ((X.map h.bar)ᵀ * Y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk2L, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four, Matrix.transpose_apply]

@[expose] noncomputable def blkGL2L : GL (Fin 2) K →* GL (Fin 4) K where
  toFun X :=
    { val := blk2L (X : Matrix (Fin 2) (Fin 2) K)
      inv := blk2L ((X⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      val_inv := by
        rw [← blk2L_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, blk2L_one]
      inv_val := by
        rw [← blk2L_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, blk2L_one] }
  map_one' := Units.ext (by simp [blk2L_one])
  map_mul' X Y := Units.ext (by simp [blk2L_mul])

theorem coe_blkGL2L (Y : GL (Fin 2) K) :
    ((blkGL2L Y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      blk2L (Y : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem blkGL2L_injective : Function.Injective (blkGL2L (K := K)) := by
  intro X Y h
  apply Units.ext
  apply blk2L_injective
  have := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K)) h
  simpa only [coe_blkGL2L] using this

@[expose] noncomputable def blkSU2L (f : ℕ) (K : Type) [Field K] : Subgroup (GL (Fin 4) K) :=
  (unitarySU 2 f K 2).map blkGL2L

theorem blkSU2L_le (h : UnitaryFieldData 2 f K) : blkSU2L f K ≤ unitarySU 2 f K 4 := by
  rintro _ ⟨X, hX, rfl⟩
  obtain ⟨hdet, hgram⟩ := (mem_unitarySU_iff h).1 hX
  refine (mem_unitarySU_iff h).2 ⟨?_, ?_⟩
  · rw [coe_blkGL2L, det_blk2L]
    exact hdet
  · rw [coe_blkGL2L, blk2L_gram, hgram, blk2L_one]

noncomputable def blkSU2LEquiv (f : ℕ) (K : Type) [Field K] :
    unitarySU 2 f K 2 ≃* blkSU2L f K :=
  Subgroup.equivMapOfInjective _ _ blkGL2L_injective

theorem nonempty_blkSU2L_mulEquiv (h : UnitaryFieldData 2 f K) :
    Nonempty (blkSU2L f K ≃* SpecialLinearGroup (Fin 2) h.fixedField) := by
  obtain ⟨φ⟩ := nonempty_blkSU2_mulEquiv h
  exact ⟨(blkSU2LEquiv f K).symm.trans ((blkSU2Equiv f K).trans φ)⟩

theorem mem_blkSU2L_of (h : UnitaryFieldData 2 f K) {g : GL (Fin 4) K}
    (hgU : g ∈ unitarySU 2 f K 4) (h01 : (g : Matrix (Fin 4) (Fin 4) K) 0 1 = 0)
    (h02 : (g : Matrix (Fin 4) (Fin 4) K) 0 2 = 0) (h03 : (g : Matrix (Fin 4) (Fin 4) K) 0 3 = 0)
    (h10 : (g : Matrix (Fin 4) (Fin 4) K) 1 0 = 0) (h12 : (g : Matrix (Fin 4) (Fin 4) K) 1 2 = 0)
    (h13 : (g : Matrix (Fin 4) (Fin 4) K) 1 3 = 0) (h20 : (g : Matrix (Fin 4) (Fin 4) K) 2 0 = 0)
    (h21 : (g : Matrix (Fin 4) (Fin 4) K) 2 1 = 0) (h30 : (g : Matrix (Fin 4) (Fin 4) K) 3 0 = 0)
    (h31 : (g : Matrix (Fin 4) (Fin 4) K) 3 1 = 0) (h00 : (g : Matrix (Fin 4) (Fin 4) K) 0 0 = 1)
    (h11 : (g : Matrix (Fin 4) (Fin 4) K) 1 1 = 1) : g ∈ blkSU2L f K := by
  set Y : Matrix (Fin 2) (Fin 2) K :=
    !![(g : Matrix (Fin 4) (Fin 4) K) 2 2, (g : Matrix (Fin 4) (Fin 4) K) 2 3;
      (g : Matrix (Fin 4) (Fin 4) K) 3 2, (g : Matrix (Fin 4) (Fin 4) K) 3 3] with hY
  have hgY : (g : Matrix (Fin 4) (Fin 4) K) = blk2L Y := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blk2L, hY, h01, h02, h03, h10, h12, h13, h20, h21, h30, h31, h00, h11]
  obtain ⟨hdet, hgram⟩ := (mem_unitarySU_iff h).1 hgU
  have hdetY : Y.det = 1 := by
    rw [← det_blk2L, ← hgY]
    exact hdet
  have hgramY : (Y.map h.bar)ᵀ * Y = 1 := by
    apply blk2L_injective
    rw [← blk2L_gram h Y Y, ← hgY, blk2L_one]
    exact hgram
  have hYY : Y * (Y.map h.bar)ᵀ = 1 := mul_eq_one_comm.mp hgramY
  let YU : GL (Fin 2) K := ⟨Y, (Y.map h.bar)ᵀ, hYY, hgramY⟩
  have hYU : YU ∈ unitarySU 2 f K 2 := (mem_unitarySU_iff h).2 ⟨hdetY, hgramY⟩
  exact ⟨YU, hYU, Units.ext hgY.symm⟩

@[expose] def dvecC (ω : Kˣ) : Fin 4 → Kˣ := ![ω, ω, ω⁻¹, ω⁻¹]

abbrev centC (f : ℕ) (K : Type) [Field K] (ω : Kˣ) : Subgroup (GL (Fin 4) K) :=
  unitarySU 2 f K 4 ⊓ Subgroup.centralizer {diagU (dvecC ω)}

theorem centC_pattern {ω : Kˣ} (hω : ω ≠ ω⁻¹) {g : GL (Fin 4) K} (hg : g ∈ centC f K ω) :
    (g : Matrix (Fin 4) (Fin 4) K) 0 2 = 0 ∧ (g : Matrix (Fin 4) (Fin 4) K) 0 3 = 0 ∧
      (g : Matrix (Fin 4) (Fin 4) K) 1 2 = 0 ∧ (g : Matrix (Fin 4) (Fin 4) K) 1 3 = 0 ∧
      (g : Matrix (Fin 4) (Fin 4) K) 2 0 = 0 ∧ (g : Matrix (Fin 4) (Fin 4) K) 2 1 = 0 ∧
      (g : Matrix (Fin 4) (Fin 4) K) 3 0 = 0 ∧ (g : Matrix (Fin 4) (Fin 4) K) 3 1 = 0 := by
  have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hg.2
  have hω' : ω⁻¹ ≠ ω := Ne.symm hω
  exact ⟨apply_eq_zero_of_commute_diagU hcomm (i := 0) (j := 2) (by simpa [dvecC] using hω),
    apply_eq_zero_of_commute_diagU hcomm (i := 0) (j := 3) (by simpa [dvecC] using hω),
    apply_eq_zero_of_commute_diagU hcomm (i := 1) (j := 2) (by simpa [dvecC] using hω),
    apply_eq_zero_of_commute_diagU hcomm (i := 1) (j := 3) (by simpa [dvecC] using hω),
    apply_eq_zero_of_commute_diagU hcomm (i := 2) (j := 0) (by simpa [dvecC] using hω'),
    apply_eq_zero_of_commute_diagU hcomm (i := 2) (j := 1) (by simpa [dvecC] using hω'),
    apply_eq_zero_of_commute_diagU hcomm (i := 3) (j := 0) (by simpa [dvecC] using hω'),
    apply_eq_zero_of_commute_diagU hcomm (i := 3) (j := 1) (by simpa [dvecC] using hω')⟩

@[expose] noncomputable def blockUp {ω : Kˣ} (hω : ω ≠ ω⁻¹) :
    ↥(centC f K ω) →* Matrix (Fin 2) (Fin 2) K where
  toFun g := !![((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 0,
    ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 1;
    ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 1 0,
    ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 1 1]
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' g g' := by
    obtain ⟨h02, h03, h12, h13, -, -, -, -⟩ := centC_pattern hω g.2
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two, h02, h03, h12, h13]

@[expose] noncomputable def blockLow {ω : Kˣ} (hω : ω ≠ ω⁻¹) :
    ↥(centC f K ω) →* Matrix (Fin 2) (Fin 2) K where
  toFun g := !![((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 2 2,
    ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 2 3;
    ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 3 2,
    ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 3 3]
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' g g' := by
    obtain ⟨-, -, -, -, h20, h21, h30, h31⟩ := centC_pattern hω g.2
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two, h20, h21, h30, h31]

theorem blkSU2_le_centC (h : UnitaryFieldData 2 f K) (ω : Kˣ) : blkSU2 f K ≤ centC f K ω := by
  refine le_inf (blkSU2_le h) ?_
  rintro _ ⟨X, -, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_blkGL2, diagU_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk2, dvecC, Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

theorem blkSU2L_le_centC (h : UnitaryFieldData 2 f K) (ω : Kˣ) : blkSU2L f K ≤ centC f K ω := by
  refine le_inf (blkSU2L_le h) ?_
  rintro _ ⟨X, -, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_blkGL2L, diagU_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk2L, dvecC, Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

theorem ker_blockLow (h : UnitaryFieldData 2 f K) {ω : Kˣ} (hω : ω ≠ ω⁻¹) :
    (blockLow (f := f) hω).ker = (blkSU2 f K).subgroupOf (centC f K ω) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  obtain ⟨h02, h03, h12, h13, h20, h21, h30, h31⟩ := centC_pattern hω g.2
  constructor
  · intro hg1
    have e := fun i j => congrFun (congrFun hg1 i) j
    have h22 := e 0 0
    have h23 := e 0 1
    have h32 := e 1 0
    have h33 := e 1 1
    simp [blockLow] at h22 h23 h32 h33
    exact mem_blkSU2_of h g.2.1 h02 h03 h12 h13 h20 h21 h23 h30 h31 h32 h22 h33
  · rintro ⟨X, -, hX⟩
    have hg : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        blk2 (X : Matrix (Fin 2) (Fin 2) K) := by
      rw [← hX]
      rfl
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blockLow, hg, blk2]

theorem ker_blockUp (h : UnitaryFieldData 2 f K) {ω : Kˣ} (hω : ω ≠ ω⁻¹) :
    (blockUp (f := f) hω).ker = (blkSU2L f K).subgroupOf (centC f K ω) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  obtain ⟨h02, h03, h12, h13, h20, h21, h30, h31⟩ := centC_pattern hω g.2
  constructor
  · intro hg1
    have e := fun i j => congrFun (congrFun hg1 i) j
    have h00 := e 0 0
    have h01 := e 0 1
    have h10 := e 1 0
    have h11 := e 1 1
    simp [blockUp] at h00 h01 h10 h11
    exact mem_blkSU2L_of h g.2.1 h01 h02 h03 h10 h12 h13 h20 h21 h30 h31 h00 h11
  · rintro ⟨X, -, hX⟩
    have hg : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        blk2L (X : Matrix (Fin 2) (Fin 2) K) := by
      rw [← hX]
      rfl
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blockUp, hg, blk2L]

theorem mem_sup_of_det_blockUp (h : UnitaryFieldData 2 f K) {ω : Kˣ} (hω : ω ≠ ω⁻¹)
    (g : ↥(centC f K ω)) (hdet : (blockUp hω g).det = 1) :
    (g : GL (Fin 4) K) ∈ blkSU2 f K ⊔ blkSU2L f K := by
  obtain ⟨h02, h03, h12, h13, h20, h21, h30, h31⟩ := centC_pattern hω g.2
  set m := ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hm
  set A : Matrix (Fin 2) (Fin 2) K := !![m 0 0, m 0 1; m 1 0, m 1 1] with hA
  set B : Matrix (Fin 2) (Fin 2) K := !![m 2 2, m 2 3; m 3 2, m 3 3] with hB
  have hAup : blockUp hω g = A := rfl
  have hsplit : m = blk2 A * blk2L B := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blk2, blk2L, hA, hB, Matrix.mul_apply, Fin.sum_univ_four, h02, h03, h12, h13, h20,
        h21, h30, h31]
  obtain ⟨hdetm, hgram⟩ := (mem_unitarySU_iff h).1 g.2.1
  have hdetA : A.det = 1 := by rw [← hAup]; exact hdet
  have hdetB : B.det = 1 := by
    have := hdetm
    rw [← hm, hsplit, Matrix.det_mul, det_blk2, det_blk2L, hdetA, one_mul] at this
    exact this
  have hgram' : ((m.map h.bar)ᵀ * m) = 1 := hgram
  have hgA : (A.map h.bar)ᵀ * A = 1 := by
    have e := fun i j => congrFun (congrFun hgram' i) j
    ext i j
    fin_cases i <;> fin_cases j
    · have := e 0 0
      simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply, h20, h30] at this
      simpa [hA, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] using this
    · have := e 0 1
      simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply, h20, h30, h21, h31]
        at this
      simpa [hA, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] using this
    · have := e 1 0
      simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply, h20, h30, h21, h31]
        at this
      simpa [hA, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] using this
    · have := e 1 1
      simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply, h21, h31] at this
      simpa [hA, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] using this
  have hgB : (B.map h.bar)ᵀ * B = 1 := by
    have e := fun i j => congrFun (congrFun hgram' i) j
    ext i j
    fin_cases i <;> fin_cases j
    · have := e 2 2
      simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply, h02, h12] at this
      simpa [hB, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] using this
    · have := e 2 3
      simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply, h02, h12, h03, h13]
        at this
      simpa [hB, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] using this
    · have := e 3 2
      simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply, h02, h12, h03, h13]
        at this
      simpa [hB, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] using this
    · have := e 3 3
      simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply, h03, h13] at this
      simpa [hB, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] using this
  let AU : GL (Fin 2) K := ⟨A, (A.map h.bar)ᵀ, mul_eq_one_comm.mp hgA, hgA⟩
  let BU : GL (Fin 2) K := ⟨B, (B.map h.bar)ᵀ, mul_eq_one_comm.mp hgB, hgB⟩
  have hAU : AU ∈ unitarySU 2 f K 2 := (mem_unitarySU_iff h).2 ⟨hdetA, hgA⟩
  have hBU : BU ∈ unitarySU 2 f K 2 := (mem_unitarySU_iff h).2 ⟨hdetB, hgB⟩
  have hg : (g : GL (Fin 4) K) = blkGL2 AU * blkGL2L BU := by
    apply Units.ext
    rw [Units.val_mul, coe_blkGL2, coe_blkGL2L]
    exact hsplit
  rw [hg]
  exact Subgroup.mul_mem_sup ⟨AU, hAU, rfl⟩ ⟨BU, hBU, rfl⟩

theorem commutator_centC_le (h : UnitaryFieldData 2 f K) {ω : Kˣ} (hω : ω ≠ ω⁻¹) :
    ⁅centC f K ω, centC f K ω⁆ ≤ blkSU2 f K ⊔ blkSU2L f K := by
  rw [Subgroup.commutator_le]
  intro g hg k hk
  let χ : ↥(centC f K ω) →* Kˣ := ((Matrix.detMonoidHom).comp (blockUp hω)).toHomUnits
  have h1 : χ ⁅(⟨g, hg⟩ : centC f K ω), ⟨k, hk⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have h1' : (blockUp hω ⁅(⟨g, hg⟩ : centC f K ω), ⟨k, hk⟩⁆).det = 1 :=
    congrArg Units.val h1
  have h2 := mem_sup_of_det_blockUp h hω _ h1'
  exact h2

theorem isSolvable_SL2_of_card_two {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    Group.IsSolvable (SpecialLinearGroup (Fin 2) F) := by
  have : Fintype (SpecialLinearGroup (Fin 2) F) := Fintype.ofFinite _
  refine CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 1)
    (b := 1) Nat.prime_two Nat.prime_three (by norm_num) ?_
  rw [← Nat.card_eq_fintype_card, CFSG.RankThree.PartOne.TCX.card_SL2', hF]
  norm_num

theorem sl2_block_facts (h : UnitaryFieldData 2 f K) {N : Subgroup (GL (Fin 4) K)}
    (hN : Nonempty (N ≃* SpecialLinearGroup (Fin 2) h.fixedField)) :
    (2 ≤ f → IsQuasisimple N ∧ Nat.card N = 2 ^ f * ((2 ^ f) ^ 2 - 1)) ∧
      (f = 1 → Group.IsSolvable N) := by
  obtain ⟨φ⟩ := hN
  have := h.finite
  have hcard : Nat.card h.fixedField = 2 ^ f := h.card_fixedField
  refine ⟨fun hf => ⟨?_, ?_⟩, fun hf => ?_⟩
  · have h4 : 4 ≤ Nat.card h.fixedField := by
      rw [hcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    have hq := CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le (k := h.fixedField)
      (m := 2) le_rfl h4
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv φ.symm hq
  · rw [Nat.card_congr φ.toEquiv, CFSG.RankThree.PartOne.TCX.card_SL2', hcard]
  · subst hf
    have := isSolvable_SL2_of_card_two (F := h.fixedField) (by rw [hcard]; norm_num)
    exact Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective

theorem component_of_typeC (h : UnitaryFieldData 2 f K) {ω : Kˣ} (hω : ω ≠ ω⁻¹)
    {J : Subgroup (GL (Fin 4) K)} (hJC : J ≤ centC f K ω)
    (hJ : IsComponent (J.subgroupOf (centC f K ω))) :
    Nat.card J = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
  have := h.finite
  have hperf := commutator_eq_of_isComponent_subgroupOf hJ hJC
  have hJN : J ≤ blkSU2 f K ⊔ blkSU2L f K :=
    hperf ▸ (Subgroup.commutator_mono hJC hJC).trans (commutator_centC_le h hω)
  have hJN' : J.subgroupOf (centC f K ω) ≤
      (blkSU2 f K).subgroupOf (centC f K ω) ⊔ (blkSU2L f K).subgroupOf (centC f K ω) := by
    rw [← Subgroup.subgroupOf_sup (blkSU2_le_centC h ω) (blkSU2L_le_centC h ω)]
    exact fun x hx => hJN hx
  have hn₁ : ((blkSU2 f K).subgroupOf (centC f K ω)).Normal := by
    rw [← ker_blockLow h hω]
    exact MonoidHom.normal_ker _
  have hn₂ : ((blkSU2L f K).subgroupOf (centC f K ω)).Normal := by
    rw [← ker_blockUp h hω]
    exact MonoidHom.normal_ker _
  have hf := h.one_le
  have h₁ := sl2_block_facts h (nonempty_blkSU2_mulEquiv h)
  have h₂ := sl2_block_facts h (nonempty_blkSU2L_mulEquiv h)
  rcases le_or_le_of_isComponent_le_sup hJ hJN' hn₁ hn₂ with hle | hle
  · have hle' : J ≤ blkSU2 f K := fun x hx => hle (show (⟨x, hJC hx⟩ : centC f K ω) ∈ _ from hx)
    rcases (show f = 1 ∨ 2 ≤ f by omega) with h1 | h2
    · exact (false_of_isComponent_subgroupOf_le hJ (blkSU2_le_centC h ω) hle'
        (h₁.2 h1)).elim
    · rw [eq_of_isComponent_subgroupOf_le hJ hJC (blkSU2_le_centC h ω) hle' (h₁.1 h2).1]
      exact (h₁.1 h2).2
  · have hle' : J ≤ blkSU2L f K := fun x hx => hle (show (⟨x, hJC hx⟩ : centC f K ω) ∈ _ from hx)
    rcases (show f = 1 ∨ 2 ≤ f by omega) with h1 | h2
    · exact (false_of_isComponent_subgroupOf_le hJ (blkSU2L_le_centC h ω) hle'
        (h₂.2 h1)).elim
    · rw [eq_of_isComponent_subgroupOf_le hJ hJC (blkSU2L_le_centC h ω) hle' (h₂.1 h2).1]
      exact (h₂.1 h2).2

theorem component_of_typeB (h : UnitaryFieldData 2 f K) {ω : Kˣ} (h1 : ω ≠ 1) (h2 : ω ≠ ω⁻¹)
    {J : Subgroup (GL (Fin 4) K)}
    (hJC : J ≤ unitarySU 2 f K 4 ⊓ Subgroup.centralizer {diagU (dvecD0 ω)})
    (hJ : IsComponent (J.subgroupOf
      (unitarySU 2 f K 4 ⊓ Subgroup.centralizer {diagU (dvecD0 ω)}))) :
    Nat.card J = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
  have := h.finite
  set C := unitarySU 2 f K 4 ⊓ Subgroup.centralizer {diagU (dvecD0 ω)} with hC
  have hperf := commutator_eq_of_isComponent_subgroupOf hJ hJC
  have hcomm : ⁅C, C⁆ ≤ blkSU2 f K := by
    rw [Subgroup.commutator_le]
    intro g hg k hk
    have hmem : (⟨g, hg⟩ * ⟨k, hk⟩ * ⟨g, hg⟩⁻¹ * ⟨k, hk⟩⁻¹ : C) ∈ (phiD0 h h1 h2).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm
        (phiD0 h h1 h2 ⟨g, hg⟩) (phiD0 h h1 h2 ⟨k, hk⟩)]
      group
    rw [ker_phiD0 h h1 h2, Subgroup.mem_subgroupOf] at hmem
    rw [commutatorElement_def]
    exact hmem
  have hJN : J ≤ blkSU2 f K := hperf ▸ (Subgroup.commutator_mono hJC hJC).trans hcomm
  have hf := h.one_le
  have h₁ := sl2_block_facts h (nonempty_blkSU2_mulEquiv h)
  rcases (show f = 1 ∨ 2 ≤ f by omega) with hf1 | hf2
  · exact (false_of_isComponent_subgroupOf_le hJ (blkSU2_le_centralizer h ω) hJN
      (h₁.2 hf1)).elim
  · rw [eq_of_isComponent_subgroupOf_le hJ hJC (blkSU2_le_centralizer h ω) hJN (h₁.1 hf2).1]
    exact (h₁.1 hf2).2

end CFSG.RankThree.PartTwo.Sec4.Item419Res3
