module

public import CFSG.RankThree.PartOne.KF.U4Model
public import CFSG.RankThree.PartOne.KF.UnitaryTorus
public import CFSG.RankThree.PartOne.KF.LayerCover
import CFSG.RankThree.PartOne.KF.R7Levi

public section

namespace CFSG.RankThree.PartTwo.Sec21.U4OddLines

open Matrix CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.KFU (diagU diagU_val apply_eq_zero_of_commute_diagU)

variable {K : Type} [Field K] {f : ℕ}

@[expose] def blk2 (X : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 4) (Fin 4) K :=
  !![X 0 0, X 0 1, 0, 0; X 1 0, X 1 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

theorem blk2_one : blk2 (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk2]

theorem blk2_mul (X Y : Matrix (Fin 2) (Fin 2) K) : blk2 (X * Y) = blk2 X * blk2 Y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk2, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four]

theorem blk2_injective {X Y : Matrix (Fin 2) (Fin 2) K} (h : blk2 X = blk2 Y) : X = Y := by
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [blk2] using congrFun (congrFun h 0) 0
  · simpa [blk2] using congrFun (congrFun h 0) 1
  · simpa [blk2] using congrFun (congrFun h 1) 0
  · simpa [blk2] using congrFun (congrFun h 1) 1

theorem det_blk2 (X : Matrix (Fin 2) (Fin 2) K) : (blk2 X).det = X.det := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, blk2, Fin.succAbove]

theorem blk2_gram (h : UnitaryFieldData 2 f K) (X Y : Matrix (Fin 2) (Fin 2) K) :
    ((blk2 X).map h.bar)ᵀ * blk2 Y = blk2 ((X.map h.bar)ᵀ * Y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk2, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four, Matrix.transpose_apply]

@[expose] noncomputable def blkGL2 : GL (Fin 2) K →* GL (Fin 4) K where
  toFun X :=
    { val := blk2 (X : Matrix (Fin 2) (Fin 2) K)
      inv := blk2 ((X⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      val_inv := by
        rw [← blk2_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, blk2_one]
      inv_val := by
        rw [← blk2_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, blk2_one] }
  map_one' := Units.ext (by simp [blk2_one])
  map_mul' X Y := Units.ext (by simp [blk2_mul])

theorem coe_blkGL2 (X : GL (Fin 2) K) :
    ((blkGL2 X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      blk2 (X : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem blkGL2_injective : Function.Injective (blkGL2 (K := K)) := by
  intro X Y h
  apply Units.ext
  apply blk2_injective
  have := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K)) h
  simpa only [coe_blkGL2] using this

@[expose] noncomputable def blkSU2 (f : ℕ) (K : Type) [Field K] : Subgroup (GL (Fin 4) K) :=
  (unitarySU 2 f K 2).map blkGL2

theorem blkSU2_le (h : UnitaryFieldData 2 f K) : blkSU2 f K ≤ unitarySU 2 f K 4 := by
  rintro _ ⟨X, hX, rfl⟩
  obtain ⟨hdet, hgram⟩ := (mem_unitarySU_iff h).1 hX
  refine (mem_unitarySU_iff h).2 ⟨?_, ?_⟩
  · rw [coe_blkGL2, det_blk2]
    exact hdet
  · rw [coe_blkGL2, blk2_gram, hgram, blk2_one]

noncomputable def blkSU2Equiv (f : ℕ) (K : Type) [Field K] :
    unitarySU 2 f K 2 ≃* blkSU2 f K :=
  Subgroup.equivMapOfInjective _ _ blkGL2_injective

theorem nonempty_blkSU2_mulEquiv (h : UnitaryFieldData 2 f K) :
    Nonempty (blkSU2 f K ≃* SpecialLinearGroup (Fin 2) h.fixedField) := by
  obtain ⟨φ⟩ := CFSG.RankThree.PartOne.KFU.nonempty_gramSU_two_mulEquiv_SL2 h
  exact ⟨(blkSU2Equiv f K).symm.trans
    ((MulEquiv.subgroupCongr (unitarySU_eq_gramSU h 2)).trans φ)⟩

theorem isPerfect_blkSU2 (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f) :
    Group.IsPerfect ↥(blkSU2 f K) := by
  obtain ⟨φ⟩ := nonempty_blkSU2_mulEquiv h
  have hfin := h.finite
  have hcard : Nat.card h.fixedField = 2 ^ f := h.card_fixedField
  have h4 : 4 ≤ Nat.card h.fixedField := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hq := CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le (k := h.fixedField)
    (m := 2) le_rfl h4
  have := hq.1
  exact Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective

@[expose] def dvecD0 (ω : Kˣ) : Fin 4 → Kˣ := ![1, 1, ω, ω⁻¹]

theorem centralizer_D0_facts (h : UnitaryFieldData 2 f K) {ω : Kˣ} (h1 : ω ≠ 1)
    (h2 : ω ≠ ω⁻¹) {g : GL (Fin 4) K}
    (hg : g ∈ unitarySU 2 f K 4 ⊓ Subgroup.centralizer {diagU (dvecD0 ω)}) :
    (g : Matrix (Fin 4) (Fin 4) K) 0 2 = 0 ∧ (g : Matrix (Fin 4) (Fin 4) K) 0 3 = 0 ∧
      (g : Matrix (Fin 4) (Fin 4) K) 1 2 = 0 ∧ (g : Matrix (Fin 4) (Fin 4) K) 1 3 = 0 ∧
      (g : Matrix (Fin 4) (Fin 4) K) 2 0 = 0 ∧ (g : Matrix (Fin 4) (Fin 4) K) 2 1 = 0 ∧
      (g : Matrix (Fin 4) (Fin 4) K) 2 3 = 0 ∧ (g : Matrix (Fin 4) (Fin 4) K) 3 0 = 0 ∧
      (g : Matrix (Fin 4) (Fin 4) K) 3 1 = 0 ∧ (g : Matrix (Fin 4) (Fin 4) K) 3 2 = 0 ∧
      h.bar ((g : Matrix (Fin 4) (Fin 4) K) 2 2) * (g : Matrix (Fin 4) (Fin 4) K) 2 2 = 1 ∧
      h.bar ((g : Matrix (Fin 4) (Fin 4) K) 3 3) * (g : Matrix (Fin 4) (Fin 4) K) 3 3 = 1 := by
  obtain ⟨hgU, hgC⟩ := Subgroup.mem_inf.mp hg
  have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hgC
  have h1' : (1 : Kˣ) ≠ ω := Ne.symm h1
  have h1'' : (1 : Kˣ) ≠ ω⁻¹ := fun h => h1 (inv_eq_one.mp h.symm)
  have e02 := apply_eq_zero_of_commute_diagU hcomm (i := 0) (j := 2) (by simpa [dvecD0] using h1')
  have e03 := apply_eq_zero_of_commute_diagU hcomm (i := 0) (j := 3)
    (by simpa [dvecD0] using h1'')
  have e12 := apply_eq_zero_of_commute_diagU hcomm (i := 1) (j := 2) (by simpa [dvecD0] using h1')
  have e13 := apply_eq_zero_of_commute_diagU hcomm (i := 1) (j := 3)
    (by simpa [dvecD0] using h1'')
  have e20 := apply_eq_zero_of_commute_diagU hcomm (i := 2) (j := 0)
    (by simpa [dvecD0] using h1'.symm)
  have e21 := apply_eq_zero_of_commute_diagU hcomm (i := 2) (j := 1)
    (by simpa [dvecD0] using h1'.symm)
  have e23 := apply_eq_zero_of_commute_diagU hcomm (i := 2) (j := 3) (by simpa [dvecD0] using h2)
  have e30 := apply_eq_zero_of_commute_diagU hcomm (i := 3) (j := 0)
    (by simpa [dvecD0] using h1''.symm)
  have e31 := apply_eq_zero_of_commute_diagU hcomm (i := 3) (j := 1)
    (by simpa [dvecD0] using h1''.symm)
  have e32 := apply_eq_zero_of_commute_diagU hcomm (i := 3) (j := 2)
    (by simpa [dvecD0] using h2.symm)
  have hgram := ((mem_unitarySU_iff h).1 hgU).2
  have g22 := congrFun (congrFun hgram 2) 2
  have g33 := congrFun (congrFun hgram 3) 3
  simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply] at g22 g33
  simp only [e02, e12, e32, e03, e13, e23, map_zero, mul_zero, zero_add, add_zero] at g22 g33
  exact ⟨e02, e03, e12, e13, e20, e21, e23, e30, e31, e32, g22, g33⟩

@[expose] noncomputable def phiD0 (h : UnitaryFieldData 2 f K) {ω : Kˣ} (h1 : ω ≠ 1)
    (h2 : ω ≠ ω⁻¹) :
    ↥(unitarySU 2 f K 4 ⊓ Subgroup.centralizer {diagU (dvecD0 ω)}) →* Kˣ × Kˣ where
  toFun g :=
    (Units.mk0 (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 2 2) (fun h0 => by
        obtain ⟨-, -, -, -, -, -, -, -, -, -, h22, -⟩ := centralizer_D0_facts h h1 h2 g.2
        rw [h0, map_zero, zero_mul] at h22
        exact zero_ne_one h22),
      Units.mk0 (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 3 3) (fun h0 => by
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h33⟩ := centralizer_D0_facts h h1 h2 g.2
        rw [h0, map_zero, zero_mul] at h33
        exact zero_ne_one h33))
  map_one' := by
    apply Prod.ext <;> apply Units.ext <;> simp
  map_mul' g g' := by
    obtain ⟨-, -, -, -, h20, h21, h23, h30, h31, h32, -, -⟩ := centralizer_D0_facts h h1 h2 g.2
    apply Prod.ext <;> apply Units.ext <;>
      simp [Subgroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_four, h20, h21, h23, h30, h31, h32]

theorem phiD0_apply (h : UnitaryFieldData 2 f K) {ω : Kˣ} (h1 : ω ≠ 1) (h2 : ω ≠ ω⁻¹)
    (g : ↥(unitarySU 2 f K 4 ⊓ Subgroup.centralizer {diagU (dvecD0 ω)})) :
    (((phiD0 h h1 h2 g).1 : Kˣ) : K) = ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 2 2 ∧
      (((phiD0 h h1 h2 g).2 : Kˣ) : K) = ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 3 3 :=
  ⟨rfl, rfl⟩

theorem mem_blkSU2_of (h : UnitaryFieldData 2 f K) {g : GL (Fin 4) K}
    (hgU : g ∈ unitarySU 2 f K 4) (h02 : (g : Matrix (Fin 4) (Fin 4) K) 0 2 = 0)
    (h03 : (g : Matrix (Fin 4) (Fin 4) K) 0 3 = 0) (h12 : (g : Matrix (Fin 4) (Fin 4) K) 1 2 = 0)
    (h13 : (g : Matrix (Fin 4) (Fin 4) K) 1 3 = 0) (h20 : (g : Matrix (Fin 4) (Fin 4) K) 2 0 = 0)
    (h21 : (g : Matrix (Fin 4) (Fin 4) K) 2 1 = 0) (h23 : (g : Matrix (Fin 4) (Fin 4) K) 2 3 = 0)
    (h30 : (g : Matrix (Fin 4) (Fin 4) K) 3 0 = 0) (h31 : (g : Matrix (Fin 4) (Fin 4) K) 3 1 = 0)
    (h32 : (g : Matrix (Fin 4) (Fin 4) K) 3 2 = 0) (h22 : (g : Matrix (Fin 4) (Fin 4) K) 2 2 = 1)
    (h33 : (g : Matrix (Fin 4) (Fin 4) K) 3 3 = 1) : g ∈ blkSU2 f K := by
  set X : Matrix (Fin 2) (Fin 2) K :=
    !![(g : Matrix (Fin 4) (Fin 4) K) 0 0, (g : Matrix (Fin 4) (Fin 4) K) 0 1;
      (g : Matrix (Fin 4) (Fin 4) K) 1 0, (g : Matrix (Fin 4) (Fin 4) K) 1 1] with hX
  have hgX : (g : Matrix (Fin 4) (Fin 4) K) = blk2 X := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blk2, hX, h02, h03, h12, h13, h20, h21, h23, h30, h31, h32, h22, h33]
  obtain ⟨hdet, hgram⟩ := (mem_unitarySU_iff h).1 hgU
  have hdetX : X.det = 1 := by
    rw [← det_blk2, ← hgX]
    exact hdet
  have hgramX : (X.map h.bar)ᵀ * X = 1 := by
    apply blk2_injective
    rw [← blk2_gram h X X, ← hgX, blk2_one]
    exact hgram
  have hXX : X * (X.map h.bar)ᵀ = 1 := mul_eq_one_comm.mp hgramX
  let XU : GL (Fin 2) K := ⟨X, (X.map h.bar)ᵀ, hXX, hgramX⟩
  have hXU : XU ∈ unitarySU 2 f K 2 := (mem_unitarySU_iff h).2 ⟨hdetX, hgramX⟩
  exact ⟨XU, hXU, Units.ext hgX.symm⟩

theorem blkSU2_le_centralizer (h : UnitaryFieldData 2 f K) (ω : Kˣ) :
    blkSU2 f K ≤ unitarySU 2 f K 4 ⊓ Subgroup.centralizer {diagU (dvecD0 ω)} := by
  refine le_inf (blkSU2_le h) ?_
  rintro _ ⟨X, -, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_blkGL2, diagU_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk2, dvecD0, Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

theorem ker_phiD0 (h : UnitaryFieldData 2 f K) {ω : Kˣ} (h1 : ω ≠ 1) (h2 : ω ≠ ω⁻¹) :
    (phiD0 h h1 h2).ker = (blkSU2 f K).subgroupOf
      (unitarySU 2 f K 4 ⊓ Subgroup.centralizer {diagU (dvecD0 ω)}) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  obtain ⟨e02, e03, e12, e13, e20, e21, e23, e30, e31, e32, -, -⟩ :=
    centralizer_D0_facts h h1 h2 g.2
  constructor
  · intro hg1
    have h22 : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 2 2 = 1 := by
      have := congrArg (fun x : Kˣ × Kˣ => ((x.1 : Kˣ) : K)) hg1
      simpa [(phiD0_apply h h1 h2 g).1] using this
    have h33 : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 3 3 = 1 := by
      have := congrArg (fun x : Kˣ × Kˣ => ((x.2 : Kˣ) : K)) hg1
      simpa [(phiD0_apply h h1 h2 g).2] using this
    exact mem_blkSU2_of h (Subgroup.mem_inf.mp g.2).1 e02 e03 e12 e13 e20 e21 e23 e30 e31 e32
      h22 h33
  · rintro ⟨X, -, hX⟩
    have hg : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        blk2 (X : Matrix (Fin 2) (Fin 2) K) := by
      rw [← hX]
      rfl
    apply Prod.ext <;> apply Units.ext
    · rw [(phiD0_apply h h1 h2 g).1, hg]
      simp [blk2]
    · rw [(phiD0_apply h h1 h2 g).2, hg]
      simp [blk2]

theorem perfectResidual_centralizer_D0 (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f) {ω : Kˣ}
    (h1 : ω ≠ 1) (h2 : ω ≠ ω⁻¹) :
    inSubgroup perfectResidual (unitarySU 2 f K 4 ⊓ Subgroup.centralizer {diagU (dvecD0 ω)}) =
      blkSU2 f K := by
  have := h.finite
  exact CFSG.RankThree.PartOne.KFU.inSubgroup_perfectResidual_eq_of_ker
    (blkSU2_le_centralizer h ω) (isPerfect_blkSU2 h hf) (phiD0 h h1 h2) (ker_phiD0 h h1 h2)

end CFSG.RankThree.PartTwo.Sec21.U4OddLines
