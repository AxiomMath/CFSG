module

public import CFSG.Quasithin.H13.NQCatJ4Check
public import CFSG.Quasithin.H13.NQCatJ4Rank
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4Local
public import CFSG.Sporadic.J4
import all CFSG.Blueprint.NativeSporadic
import all CFSG.Sporadic.J4.Group

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.NQCat

open CFSG.Quasithin.H13.NQCat.Native CFSG.SectionRank CFSG.SectionRank.Native
  CFSG.SectionRank.LocalWitness CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped commutatorElement Matrix

noncomputable abbrev jmat : Sporadic.J4.J →* Matrix (Fin 112) (Fin 112) (ZMod 2) :=
  (Units.coeHom _).comp (Sporadic.J4.J).subtype

theorem jmat_injective : Function.Injective jmat := fun _ _ e => Subtype.ext (Units.ext e)

@[expose] noncomputable def fixDim (g : Sporadic.J4.J) : ℕ :=
  Module.finrank (ZMod 2) (LinearMap.ker (Matrix.mulVecLin (jmat g - 1)))

noncomputable abbrev j4S : Submonoid (Matrix (Fin 112) (Fin 112) (ZMod 2)) :=
  NativeSporadic.seedMonoid 2 112 1 j4Sylow11Data.seedA j4Sylow11Data.seedB

theorem j4_cubic_facts :
    j4Sylow11Data.prog.all (Op.lt j4Sylow11Data.nregs) = true ∧
    (ops2 112).eq ((ops2 112).pow j4X 11) (ops2 112).one = true ∧
    (ops2 112).eq ((ops2 112).pow j4Y 11) (ops2 112).one = true ∧
    (ops2 112).vne ((ops2 112).vmul ((ops2 112).unit 0) j4Z) ((ops2 112).unit 0) = true ∧
    (ops2 112).eq ((ops2 112).mul j4Z j4X) ((ops2 112).mul j4X j4Z) = true ∧
    (ops2 112).eq ((ops2 112).mul j4Z j4Y) ((ops2 112).mul j4Y j4Z) = true := by
  have h := CFSG.SectionRank.j4_sylow11_check
  unfold Ops.cubicCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hprog⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hXr⟩, hYr⟩, -⟩, hZt⟩,
    hZX⟩, hZY⟩, -⟩, -⟩, -⟩, -⟩ := h
  exact ⟨hprog, hXr, hYr, hZt, hZX, hZY⟩

theorem j4_reg_mem
    {r : ℕ} (hr : r < 31) : rowsMatrix 112 j4R[r]! ∈ j4S :=
  ((spec2 112).regsOf_ok j4_cubic_facts.1 hr).2

theorem rowsMatrix_ops2_mul (X Y : Array ℕ) :
    rowsMatrix 112 ((ops2 112).mul X Y) = rowsMatrix 112 X * rowsMatrix 112 Y :=
  rowsMatrix_mulRows 112 X Y

theorem rowsMatrix_ops2_pow (X : Array ℕ) (n : ℕ) :
    rowsMatrix 112 ((ops2 112).pow X n) = rowsMatrix 112 X ^ n :=
  ((spec2 112).pow_spec (X := X) trivial n).2

theorem rowsMatrix_pow_eq_one_of_check {X : Array ℕ} {n : ℕ}
    (h : (ops2 112).eq ((ops2 112).pow X n) (ops2 112).one = true) : rowsMatrix 112 X ^ n = 1 :=
  (spec2 112).pow_eq_one_of_check trivial h

theorem rowsMatrix_eq_of_check {X Y : Array ℕ} (h : (ops2 112).eq X Y = true) :
    rowsMatrix 112 X = rowsMatrix 112 Y :=
  (spec2 112).toMat_eq trivial trivial h

theorem rowsMatrix_j4X_pow : rowsMatrix 112 j4X ^ 11 = 1 :=
  rowsMatrix_pow_eq_one_of_check j4_cubic_facts.2.1

theorem rowsMatrix_j4Y_pow : rowsMatrix 112 j4Y ^ 11 = 1 :=
  rowsMatrix_pow_eq_one_of_check j4_cubic_facts.2.2.1

theorem rowsMatrix_j4H_pow : rowsMatrix 112 j4H ^ 40 = 1 :=
  rowsMatrix_pow_eq_one_of_check j4H_pow

noncomputable def j4Elt
    {X : Array ℕ} (hX : rowsMatrix 112 X ∈ j4S) {n : ℕ} (hn : n ≠ 0)
    (h : rowsMatrix 112 X ^ n = 1) : Sporadic.J4.J :=
  Sporadic.J4.seedEquiv Sporadic.J4.j4Facts.mat (unitOf j4S hX hn h)

theorem jmat_j4Elt
    {X : Array ℕ} (hX : rowsMatrix 112 X ∈ j4S) {n : ℕ} (hn : n ≠ 0)
    (h : rowsMatrix 112 X ^ n = 1) : jmat (j4Elt hX hn h) = rowsMatrix 112 X :=
  valHom_unitOf j4S hX hn h

@[irreducible] noncomputable def j4x :
    Sporadic.J4.J :=
  j4Elt (j4_reg_mem (r := 22) (by norm_num)) (by norm_num) rowsMatrix_j4X_pow

@[irreducible] noncomputable def j4y :
    Sporadic.J4.J :=
  j4Elt (j4_reg_mem (r := 30) (by norm_num)) (by norm_num) rowsMatrix_j4Y_pow

@[irreducible] noncomputable def j4h :
    Sporadic.J4.J :=
  j4Elt (j4_reg_mem (r := 18) (by norm_num)) (by norm_num) rowsMatrix_j4H_pow

noncomputable abbrev j4z :
    Sporadic.J4.J := ⁅j4x, j4y⁆

theorem jmat_j4x :
    jmat j4x = rowsMatrix 112 j4X := by
  unfold j4x
  exact jmat_j4Elt _ _ _

theorem jmat_j4y :
    jmat j4y = rowsMatrix 112 j4Y := by
  unfold j4y
  exact jmat_j4Elt _ _ _

theorem jmat_j4h :
    jmat j4h = rowsMatrix 112 j4H := by
  unfold j4h
  exact jmat_j4Elt _ _ _

theorem j4x_pow : j4x ^ 11 = 1 :=
  jmat_injective (by rw [map_pow, jmat_j4x, rowsMatrix_j4X_pow, map_one])

theorem j4y_pow : j4y ^ 11 = 1 :=
  jmat_injective (by rw [map_pow, jmat_j4y, rowsMatrix_j4Y_pow, map_one])

theorem inv_eq_pow_of_pow_eq_one {G : Type*} [Group G] {g : G} {n : ℕ} (hn : 0 < n)
    (h : g ^ n = 1) : g⁻¹ = g ^ (n - 1) := by
  rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel hn, h]

theorem jmat_j4z :
    jmat j4z = rowsMatrix 112 j4Z := by
  rw [j4z, commutatorElement_def, inv_eq_pow_of_pow_eq_one (by norm_num) j4x_pow,
    inv_eq_pow_of_pow_eq_one (by norm_num) j4y_pow, map_mul, map_mul, map_mul, map_pow, map_pow,
    jmat_j4x, jmat_j4y, j4Z, Ops.commM, rowsMatrix_ops2_mul, rowsMatrix_ops2_mul,
    rowsMatrix_ops2_mul, rowsMatrix_ops2_pow, rowsMatrix_ops2_pow]

theorem j4z_comm_x :
    Commute j4z j4x := by
  refine jmat_injective ?_
  rw [map_mul, map_mul, jmat_j4z, jmat_j4x, ← rowsMatrix_ops2_mul, ← rowsMatrix_ops2_mul]
  exact rowsMatrix_eq_of_check j4_cubic_facts.2.2.2.2.1

theorem j4z_comm_y :
    Commute j4z j4y := by
  refine jmat_injective ?_
  rw [map_mul, map_mul, jmat_j4z, jmat_j4y, ← rowsMatrix_ops2_mul, ← rowsMatrix_ops2_mul]
  exact rowsMatrix_eq_of_check j4_cubic_facts.2.2.2.2.2

theorem j4z_ne_one : j4z ≠ 1 := by
  intro h1
  apply (spec2 112).toVec_ne j4_cubic_facts.2.2.2.1
  rw [(spec2 112).toVec_vmul ((spec2 112).unit_wf _) trivial]
  change _ ᵥ* rowsMatrix 112 j4Z = _
  rw [← jmat_j4z, h1, map_one, Matrix.vecMul_one]

theorem jmat_word (i j k : ℕ) :
    jmat (j4x ^ i * j4y ^ j * j4z ^ k) = rowsMatrix 112 (j4Word i j k) := by
  rw [map_mul, map_mul, map_pow, map_pow, map_pow, jmat_j4x, jmat_j4y, jmat_j4z, j4Word,
    rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_powRows, rowsMatrix_powRows,
    rowsMatrix_powRows]

theorem powTable_getD (M : Array ℕ) {i : ℕ} (hi : i < 11) :
    (powTable M).getD i #[] = powRows 112 M i := by
  rw [powTable, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
    List.getElem_range]

theorem fixDimOK_noncentral
    {i j k : ℕ} (hi : i < 11) (hj : j < 11) (hk : k < 11)
    (hij : ¬ (i = 0 ∧ j = 0)) : fixDimOK 112 (j4Word i j k) 12 = true := by
  have h := j4_fix_noncentral
  unfold j4FixNoncentralOK at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq] at h
  rcases h i hi j hj with h1 | h1
  · exact absurd h1 hij
  · have h2 := h1 k hk
    rwa [powTable_getD _ hi, powTable_getD _ hj, powTable_getD _ hk] at h2

theorem fixDimOK_central {k : ℕ} (hk : k < 11) (hk0 : k ≠ 0) :
    fixDimOK 112 (powRows 112 j4Z k) 2 = true := by
  have h := j4_fix_central
  unfold j4FixCentralOK at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at h
  rcases h k hk with h1 | h1
  · exact absurd h1 hk0
  · rwa [powTable_getD _ hk] at h1

theorem j4xy_pow
    {i j : ℕ} (hi : i < 11) (hj : j < 11) : (j4x ^ i * j4y ^ j) ^ 11 = 1 := by
  have h := j4_pow_xy
  unfold j4PowXYOK at h
  simp only [List.all_eq_true, List.mem_range] at h
  have h1 := rowsMatrix_pow_eq_one_of_check (h i hi j hj)
  rw [powTable_getD _ hi, powTable_getD _ hj, rowsMatrix_mulRows, rowsMatrix_powRows,
    rowsMatrix_powRows] at h1
  refine jmat_injective ?_
  rw [map_pow, map_mul, map_pow, map_pow, jmat_j4x, jmat_j4y, h1, map_one]

theorem fixDim_word
    {i j k : ℕ} {d : ℕ} (h : fixDimOK 112 (j4Word i j k) d = true) :
    fixDim (j4x ^ i * j4y ^ j * j4z ^ k) = d := by
  rw [fixDim, jmat_word]
  exact finrank_ker_of_fixDimOK h

theorem fixDim_z_pow
    {k : ℕ} (hk : k < 11) (hk0 : k ≠ 0) : fixDim (j4z ^ k) = 2 := by
  rw [fixDim, map_pow, jmat_j4z, ← rowsMatrix_powRows]
  exact finrank_ker_of_fixDimOK (fixDimOK_central hk hk0)

theorem rowsMatrix_conj_of_check {X Y W : Array ℕ} (h : (ops2 112).conjOK X Y W = true) :
    rowsMatrix 112 X * rowsMatrix 112 Y = rowsMatrix 112 W * rowsMatrix 112 X :=
  (spec2 112).toMat_of_conjOK trivial trivial trivial h

theorem j4h_conj_x
    : j4h * j4x * j4h⁻¹ = j4x ^ 0 * j4y ^ 7 * j4z ^ 1 := by
  rw [mul_inv_eq_iff_eq_mul]
  refine jmat_injective ?_
  rw [map_mul, map_mul, jmat_word, jmat_j4h, jmat_j4x]
  exact rowsMatrix_conj_of_check j4H_conjX

theorem j4h_conj_y
    : j4h * j4y * j4h⁻¹ = j4x ^ 6 * j4y ^ 9 * j4z ^ 6 := by
  rw [mul_inv_eq_iff_eq_mul]
  refine jmat_injective ?_
  rw [map_mul, map_mul, jmat_word, jmat_j4h, jmat_j4y]
  exact rowsMatrix_conj_of_check j4H_conjY

end CFSG.Quasithin.H13.NQCat
