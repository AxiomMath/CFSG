module

public import CFSG.Quasithin.H13.NQCatJ4Check
public import CFSG.Quasithin.H13.NQCatJ4Rank
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4Local
public import CFSG.Sporadic.J4
import CFSG.Quasithin.H13.NQCatJ4Transport
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

theorem fixDim_conj (h g : Sporadic.J4.J) : fixDim (h * g * h⁻¹) = fixDim g := by
  have hu : jmat h * jmat h⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have e : jmat (h * g * h⁻¹) - 1 = jmat h * (jmat g - 1) * jmat h⁻¹ := by
    rw [map_mul, map_mul, mul_sub, sub_mul, mul_one, hu]
  have hP : IsUnit (jmat h).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 ((Group.isUnit h).map jmat)
  have hQ : IsUnit (jmat h⁻¹).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 ((Group.isUnit h⁻¹).map jmat)
  have hr : (jmat (h * g * h⁻¹) - 1).rank = (jmat g - 1).rank := by
    rw [e, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hQ,
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hP]
  have key : ∀ B : Matrix (Fin 112) (Fin 112) (ZMod 2),
      Module.finrank (ZMod 2) (LinearMap.ker B.mulVecLin) = 112 - B.rank := by
    intro B
    have h := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
    rw [Module.finrank_fin_fun] at h
    unfold Matrix.rank
    omega
  unfold fixDim
  rw [key, key, hr]

theorem fixDim_pow_eq (g : Sporadic.J4.J) (m m' : ℕ) (h : (g ^ m) ^ m' = g) :
    fixDim (g ^ m) = fixDim g := by
  have hle : ∀ (u : Sporadic.J4.J) (n : ℕ), LinearMap.ker (Matrix.mulVecLin (jmat u - 1)) ≤
      LinearMap.ker (Matrix.mulVecLin (jmat (u ^ n) - 1)) := by
    intro u n v hv
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec,
      sub_eq_zero] at hv ⊢
    rw [map_pow]
    induction n with
    | zero => rw [pow_zero, Matrix.one_mulVec]
    | succ n ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hv, ih]
  have heq : LinearMap.ker (Matrix.mulVecLin (jmat (g ^ m) - 1)) =
      LinearMap.ker (Matrix.mulVecLin (jmat g - 1)) := by
    refine le_antisymm ?_ (hle g m)
    have h' := hle (g ^ m) m'
    rwa [h] at h'
  unfold fixDim
  rw [heq]

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

theorem fixDimOK_reps :
    fixDimOK 112 (j4Word 0 1 0) 12 = true ∧ ∀ b < 11, fixDimOK 112 (j4Word 1 b 0) 12 = true := by
  have h := j4_fix_reps
  unfold j4FixRepsOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  exact h

theorem j4z_pow : j4z ^ 11 = 1 := by
  rw [commutator_pow_eq j4z_comm_x, j4x_pow, commutatorElement_one_left]

theorem j4xy_pow
    {i j : ℕ} (hi : i < 11) (hj : j < 11) : (j4x ^ i * j4y ^ j) ^ 11 = 1 :=
  Transport.pow_x_pow_y_pow_eleven j4z_comm_x j4z_comm_y j4z_pow j4x_pow j4y_pow i j

theorem fixDim_word
    {i j k : ℕ} {d : ℕ} (h : fixDimOK 112 (j4Word i j k) d = true) :
    fixDim (j4x ^ i * j4y ^ j * j4z ^ k) = d := by
  rw [fixDim, jmat_word]
  exact finrank_ker_of_fixDimOK h

theorem fixDim_z_pow
    {k : ℕ} (hk : k < 11) (hk0 : k ≠ 0) : fixDim (j4z ^ k) = 2 := by
  obtain ⟨m', hm'⟩ := Transport.pow_pow_inv_eq j4z_pow hk hk0
  rw [fixDim_pow_eq _ k m' hm', fixDim, jmat_j4z]
  exact finrank_ker_of_fixDimOK j4_fix_central

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
