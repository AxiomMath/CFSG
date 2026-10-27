module

public import CFSG.Sporadic.J3.Facts
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Certificates.SchreierStabilizerGenerators
public import CFSG.Sporadic.J3.F2Spec

public section

namespace CFSG.Sporadic.J3

open Native CFSG.Sporadic.Th
open CFSG.Sporadic.Th.Native (ap)
open scoped Matrix

variable (D : Data)

noncomputable abbrev mA : Matrix (Fin 80) (Fin 80) (ZMod 2) :=
  CFSG.Blueprint.NativeSporadic.decode 2 80 1 D.seedA

noncomputable abbrev mB : Matrix (Fin 80) (Fin 80) (ZMod 2) :=
  CFSG.Blueprint.NativeSporadic.decode 2 80 1 D.seedB

theorem rowsMatrix_rowsA : rowsMatrix 80 D.rowsA = mA D := rowsMatrix_rowsOfPayload 80 D.seedA

theorem rowsMatrix_rowsB : rowsMatrix 80 D.rowsB = mB D := rowsMatrix_rowsOfPayload 80 D.seedB

@[expose] noncomputable def gA : GL (Fin 80) (ZMod 2) :=
  @dite _ ((mA D).det ≠ 0) (Classical.propDecidable _)
    (fun h => Matrix.GeneralLinearGroup.mkOfDetNeZero (mA D) h) fun _ => 1

@[expose] noncomputable def gB : GL (Fin 80) (ZMod 2) :=
  @dite _ ((mB D).det ≠ 0) (Classical.propDecidable _)
    (fun h => Matrix.GeneralLinearGroup.mkOfDetNeZero (mB D) h) fun _ => 1

noncomputable abbrev J : Subgroup (GL (Fin 80) (ZMod 2)) := Subgroup.closure {gA D, gB D}

@[expose] noncomputable def a : J D := ⟨gA D, Subgroup.subset_closure (Set.mem_insert _ _)⟩

@[expose] noncomputable def b : J D :=
  ⟨gB D, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

theorem coe_a : ((a D : J D) : GL (Fin 80) (ZMod 2)) = gA D := Subtype.coe_mk _ _

theorem coe_b : ((b D : J D) : GL (Fin 80) (ZMod 2)) = gB D := Subtype.coe_mk _ _

theorem closure_ab : Subgroup.closure ({a D, b D} : Set (J D)) = ⊤ := by
  have h := CFSG.Certificates.schreier_subtype_generators_generate
    ({gA D, gB D} : Set (GL (Fin 80) (ZMod 2)))
  convert h using 2
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage, Subgroup.coe_subtype]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl (coe_a D)
    · exact Or.inr (coe_b D)
  · rintro (h | h)
    · left; exact Subtype.ext (h.trans (coe_a D).symm)
    · right; exact Subtype.ext (h.trans (coe_b D).symm)

abbrev Vec : Type := Fin 80 → ZMod 2

theorem smul_vec (g : J D) (v : Vec) :
    g • v = ((g : GL (Fin 80) (ZMod 2)) : Matrix (Fin 80) (Fin 80) (ZMod 2)) *ᵥ v := rfl

noncomputable abbrev P (i : ℕ) : Vec := toVecD 80 D.pts[i]!

@[expose] def OrbitFacts : Prop :=
  orbitOK 80 D.n D.colsA D.colsB D.pts D.tA D.tB = true ∧ powRows 80 D.rowsA 2 = idRows 80 ∧
    powRows 80 D.rowsB 3 = idRows 80

variable {D} in
theorem Facts.orbitFacts {c : ℕ} (hF : Facts D c) : OrbitFacts D := ⟨hF.orbit, hF.powA, hF.powB⟩

section Seeds

variable {D}

theorem mA_sq (h : powRows 80 D.rowsA 2 = idRows 80) : mA D ^ 2 = 1 := by
  have := congrArg (rowsMatrix 80) h
  rwa [rowsMatrix_powRows, rowsMatrix_idRows, rowsMatrix_rowsA] at this

theorem mB_cube (h : powRows 80 D.rowsB 3 = idRows 80) : mB D ^ 3 = 1 := by
  have := congrArg (rowsMatrix 80) h
  rwa [rowsMatrix_powRows, rowsMatrix_idRows, rowsMatrix_rowsB] at this

theorem det_ne_zero_of_pow {M : Matrix (Fin 80) (Fin 80) (ZMod 2)} {e : ℕ} (he : 0 < e)
    (h : M ^ e = 1) : M.det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det h
  rw [Matrix.det_pow, h0, zero_pow (Nat.pos_iff_ne_zero.mp he), Matrix.det_one] at this
  exact zero_ne_one this

theorem det_mA_ne_zero (h : powRows 80 D.rowsA 2 = idRows 80) : (mA D).det ≠ 0 :=
  det_ne_zero_of_pow (by norm_num) (mA_sq h)

theorem det_mB_ne_zero (h : powRows 80 D.rowsB 3 = idRows 80) : (mB D).det ≠ 0 :=
  det_ne_zero_of_pow (by norm_num) (mB_cube h)

theorem gA_eq (h : powRows 80 D.rowsA 2 = idRows 80) :
    gA D = Matrix.GeneralLinearGroup.mkOfDetNeZero (mA D) (det_mA_ne_zero h) := by
  unfold gA; rw [dite_eq_left (det_mA_ne_zero h)]

theorem gB_eq (h : powRows 80 D.rowsB 3 = idRows 80) :
    gB D = Matrix.GeneralLinearGroup.mkOfDetNeZero (mB D) (det_mB_ne_zero h) := by
  unfold gB; rw [dite_eq_left (det_mB_ne_zero h)]

theorem a_val (h : powRows 80 D.rowsA 2 = idRows 80) :
    (((a D : J D) : GL (Fin 80) (ZMod 2)) : Matrix (Fin 80) (Fin 80) (ZMod 2)) = mA D := by
  rw [coe_a, gA_eq h]; rfl

theorem b_val (h : powRows 80 D.rowsB 3 = idRows 80) :
    (((b D : J D) : GL (Fin 80) (ZMod 2)) : Matrix (Fin 80) (Fin 80) (ZMod 2)) = mB D := by
  rw [coe_b, gB_eq h]; rfl

noncomputable def seedEquiv (hA : powRows 80 D.rowsA 2 = idRows 80)
    (hB : powRows 80 D.rowsB 3 = idRows 80) :
    (CFSG.Blueprint.NativeSporadic.seedMonoid 2 80 1 D.seedA D.seedB)ˣ ≃* J D :=
  (Blueprint.NativeSporadic.matrixSeedEquiv 2 80 (by norm_num) (mA D) (mB D) (det_mA_ne_zero hA)
    (det_mB_ne_zero hB)).trans (MulEquiv.subgroupCongr (by
      show _ = Subgroup.closure {gA D, gB D}
      rw [gA_eq hA, gB_eq hB]))

end Seeds

section Orbit

variable {D}

theorem orbit_parts (h : orbitOK 80 D.n D.colsA D.colsB D.pts D.tA D.tB = true) :
    D.pts.size = D.n ∧
      (∀ i < D.n, D.pts[i]! < 2 ^ 80 ∧ ap D.tA i < D.n ∧
        D.pts[ap D.tA i]! = vecMulN 80 D.colsA D.pts[i]! ∧ ap D.tB i < D.n ∧
        D.pts[ap D.tB i]! = vecMulN 80 D.colsB D.pts[i]!) ∧
      ∀ i, i + 1 < D.n → D.pts[i]! < D.pts[i + 1]! := by
  unfold orbitOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, fun i hi => ?_, fun i hi => ?_⟩
  · have := (allIn_eq_true.1 h2) i (Nat.zero_le _) hi
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    obtain ⟨⟨⟨⟨h5, h6⟩, h7⟩, h8⟩, h9⟩ := this
    exact ⟨h5, h6, h7, h8, h9⟩
  · have := (allIn_eq_true.1 h3) i (Nat.zero_le _) (by omega)
    simpa using this

theorem pts_lt_of_lt (h : orbitOK 80 D.n D.colsA D.colsB D.pts D.tA D.tB = true) {i j : ℕ}
    (hij : i < j) (hj : j < D.n) : D.pts[i]! < D.pts[j]! := by
  induction j with
  | zero => omega
  | succ j ih =>
    have hstep := (orbit_parts h).2.2 j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with hlt | rfl
    · exact lt_trans (ih hlt (by omega)) hstep
    · exact hstep

theorem P_injective (h : orbitOK 80 D.n D.colsA D.colsB D.pts D.tA D.tB = true) :
    ∀ i < D.n, ∀ j < D.n, P D i = P D j → i = j := by
  intro i hi j hj hij
  have e := toVecD_injective ((orbit_parts h).2.1 i hi).1 ((orbit_parts h).2.1 j hj).1 hij
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact absurd e (ne_of_lt (pts_lt_of_lt h hlt hj))
  · exact heq
  · exact absurd e (ne_of_gt (pts_lt_of_lt h hgt hi))

theorem a_smul_P (hO : OrbitFacts D) :
    ∀ i < D.n, ap D.tA i < D.n ∧ a D • P D i = P D (ap D.tA i) := by
  intro i hi
  obtain ⟨-, hlt, he, -, -⟩ := (orbit_parts hO.1).2.1 i hi
  refine ⟨hlt, ?_⟩
  rw [smul_vec, a_val hO.2.1, ← rowsMatrix_rowsA, rowsMatrix_mulVec, P, he]
  rfl

theorem b_smul_P (hO : OrbitFacts D) :
    ∀ i < D.n, ap D.tB i < D.n ∧ b D • P D i = P D (ap D.tB i) := by
  intro i hi
  obtain ⟨-, -, -, hlt, he⟩ := (orbit_parts hO.1).2.1 i hi
  refine ⟨hlt, ?_⟩
  rw [smul_vec, b_val hO.2.2, ← rowsMatrix_rowsB, rowsMatrix_mulVec, P, he]
  rfl

end Orbit

noncomputable abbrev ptSet : Set Vec := P D '' Set.Iio D.n

theorem inv_smul_mem_of_finite {G Y : Type*} [Group G] [MulAction G Y] {g : G} {S : Set Y}
    (hS : S.Finite) (h : ∀ y ∈ S, g • y ∈ S) : ∀ y ∈ S, g⁻¹ • y ∈ S := by
  have hsub : (fun y => g • y) '' S ⊆ S := by
    rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  have himg : (fun y => g • y) '' S = S := by
    apply Set.eq_of_subset_of_ncard_le hsub _ hS
    rw [Set.ncard_image_of_injective _ (MulAction.injective g)]
  intro y hy
  rw [← himg] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  simpa using hz

theorem smul_mem_of_closure' {G Y : Type*} [Group G] [MulAction G Y] {x y : G}
    (hgen : Subgroup.closure ({x, y} : Set G) = ⊤) {S : Set Y} (hS : S.Finite)
    (hx : ∀ v ∈ S, x • v ∈ S) (hy : ∀ v ∈ S, y • v ∈ S) (g : G) : ∀ v ∈ S, g • v ∈ S := by
  have hg : g ∈ Subgroup.closure ({x, y} : Set G) := by rw [hgen]; exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem z hz =>
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  | one => intro v hv; simpa using hv
  | mul z w _ _ hz hw =>
    intro v hv
    rw [mul_smul]
    exact hz _ (hw v hv)
  | inv z _ hz => exact inv_smul_mem_of_finite hS hz

theorem smul_mem_ptSet (hO : OrbitFacts D) (g : J D) : ∀ v ∈ ptSet D, g • v ∈ ptSet D := by
  refine smul_mem_of_closure' (closure_ab D) ((Set.finite_Iio D.n).image _) ?_ ?_ g
  · rintro _ ⟨i, hi, rfl⟩
    exact ⟨_, (a_smul_P hO i hi).1, (a_smul_P hO i hi).2.symm⟩
  · rintro _ ⟨i, hi, rfl⟩
    exact ⟨_, (b_smul_P hO i hi).1, (b_smul_P hO i hi).2.symm⟩

@[expose] noncomputable def ptSub (hO : OrbitFacts D) : SubMulAction (J D) Vec where
  carrier := ptSet D
  smul_mem' g _ hv := smul_mem_ptSet D hO g _ hv

@[expose] noncomputable def ptEquiv (hO : OrbitFacts D) : Fin D.n ≃ ptSub D hO :=
  Equiv.ofBijective (fun i => ⟨P D i, ⟨i, i.isLt, rfl⟩⟩)
    ⟨fun i j h => Fin.ext (P_injective hO.1 i i.isLt j j.isLt (congrArg Subtype.val h)), by
      rintro ⟨v, ⟨i, hi, rfl⟩⟩
      exact ⟨⟨i, hi⟩, rfl⟩⟩

theorem ptEquiv_apply (hO : OrbitFacts D) (i : Fin D.n) : (ptEquiv D hO i : Vec) = P D i := rfl

noncomputable instance idxAction : MulAction (J D) (Fin D.n) where
  smul g i := by
    classical
    exact if h : OrbitFacts D then (ptEquiv D h).symm (g • ptEquiv D h i) else i
  one_smul i := by
    classical
    show (if h : OrbitFacts D then (ptEquiv D h).symm ((1 : J D) • ptEquiv D h i) else i) = i
    split
    · rw [one_smul, Equiv.symm_apply_apply]
    · rfl
  mul_smul g h i := by
    classical
    show (if hF : OrbitFacts D then (ptEquiv D hF).symm ((g * h) • ptEquiv D hF i) else i) =
      (if hF : OrbitFacts D then (ptEquiv D hF).symm (g • ptEquiv D hF
        (if hF : OrbitFacts D then (ptEquiv D hF).symm (h • ptEquiv D hF i) else i)) else
        (if hF : OrbitFacts D then (ptEquiv D hF).symm (h • ptEquiv D hF i) else i))
    split
    · rw [Equiv.apply_symm_apply, mul_smul]
    · rfl

noncomputable abbrev basisRows : Array ℕ := D.basis.map fun i => D.pts[i]!

section Action

variable {D} (hO : OrbitFacts D)
include hO

theorem ptEquiv_smul (g : J D) (i : Fin D.n) :
    ptEquiv D hO (g • i) = g • ptEquiv D hO i := by
  have : (g • i : Fin D.n) = (ptEquiv D hO).symm (g • ptEquiv D hO i) := by
    classical
    show (if h : OrbitFacts D then (ptEquiv D h).symm (g • ptEquiv D h i) else i) = _
    rw [dite_eq_left hO]
  rw [this, Equiv.apply_symm_apply]

theorem P_smul (g : J D) (i : Fin D.n) : P D (g • i).val = g • P D i.val := by
  have := congrArg Subtype.val (ptEquiv_smul hO g i)
  rwa [ptEquiv_apply, SubMulAction.val_smul, ptEquiv_apply] at this

theorem idx_eq_iff {g : J D} {i j : ℕ} (hi : i < D.n) (hj : j < D.n) :
    idx D.n g i = j ↔ g • P D i = P D j := by
  rw [idx_of_lt g hi]
  constructor
  · intro h
    rw [← P_smul hO g ⟨i, hi⟩, h]
  · intro h
    apply P_injective hO.1 _ (g • (⟨i, hi⟩ : Fin D.n)).isLt _ hj
    rw [P_smul hO g ⟨i, hi⟩]
    exact h

theorem rep_a : Rep D.n D.tA (a D) := by
  intro i hi
  symm
  exact (idx_eq_iff hO hi (a_smul_P hO i hi).1).2 (a_smul_P hO i hi).2

theorem rep_b : Rep D.n D.tB (b D) := by
  intro i hi
  symm
  exact (idx_eq_iff hO hi (b_smul_P hO i hi).1).2 (b_smul_P hO i hi).2

end Action

section Faithful

variable {D} {c : ℕ} (hF : Facts D c)
include hF

theorem basis_rowsMatrix (t k : Fin 80) :
    rowsMatrix 80 (basisRows D) t k = P D D.basis[t.val]! k := by
  have ht : t.val < D.basis.size := by rw [hF.basis_size]; exact t.isLt
  rw [rowsMatrix_apply, Array.getElem?_map, Array.getElem?_eq_getElem ht, Option.map_some,
    Option.getD_some, getElem!_pos D.basis t.val ht]

theorem eq_one_of_fix_basis (g : J D)
    (hg : ∀ t < D.basis.size, idx D.n g D.basis[t]! = D.basis[t]!) : g = 1 := by
  have hO := hF.orbitFacts
  have hfix : ∀ t : Fin 80,
      ((g : GL (Fin 80) (ZMod 2)) : Matrix (Fin 80) (Fin 80) (ZMod 2)) *ᵥ P D D.basis[t.val]! =
        P D D.basis[t.val]! := by
    intro t
    have ht : t.val < D.basis.size := by rw [hF.basis_size]; exact t.isLt
    have hlt := hF.basis_lt t.val ht
    have := (idx_eq_iff hO hlt hlt).1 (hg t.val ht)
    rwa [smul_vec] at this
  have hMC : ((g : GL (Fin 80) (ZMod 2)) : Matrix (Fin 80) (Fin 80) (ZMod 2)) *
      (rowsMatrix 80 (basisRows D))ᵀ = (rowsMatrix 80 (basisRows D))ᵀ := by
    ext j t
    have := congrFun (hfix t) j
    rw [Matrix.mul_apply, Matrix.transpose_apply, basis_rowsMatrix hF]
    simp only [Matrix.transpose_apply, basis_rowsMatrix hF]
    rw [← this]
    rfl
  have hinv : rowsMatrix 80 D.basisInv * rowsMatrix 80 (basisRows D) = 1 := by
    have := congrArg (rowsMatrix 80) hF.basis_inv
    rwa [rowsMatrix_mulRows, rowsMatrix_idRows] at this
  have hinvT : (rowsMatrix 80 (basisRows D))ᵀ * (rowsMatrix 80 D.basisInv)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hinv, Matrix.transpose_one]
  have hM1 : ((g : GL (Fin 80) (ZMod 2)) : Matrix (Fin 80) (Fin 80) (ZMod 2)) = 1 := by
    calc ((g : GL (Fin 80) (ZMod 2)) : Matrix (Fin 80) (Fin 80) (ZMod 2))
        = ((g : GL (Fin 80) (ZMod 2)) : Matrix (Fin 80) (Fin 80) (ZMod 2)) *
          ((rowsMatrix 80 (basisRows D))ᵀ * (rowsMatrix 80 D.basisInv)ᵀ) := by
          rw [hinvT, Matrix.mul_one]
      _ = (((g : GL (Fin 80) (ZMod 2)) : Matrix (Fin 80) (Fin 80) (ZMod 2)) *
          (rowsMatrix 80 (basisRows D))ᵀ) * (rowsMatrix 80 D.basisInv)ᵀ := by
          rw [Matrix.mul_assoc]
      _ = 1 := by rw [hMC, hinvT]
  apply Subtype.ext
  apply Units.ext
  exact hM1

theorem faithful : FaithfulSMul (J D) (Fin D.n) := by
  refine ⟨fun {g h} hgh => ?_⟩
  have : h⁻¹ * g = 1 := by
    apply eq_one_of_fix_basis hF
    intro t ht
    have hlt := hF.basis_lt t ht
    rw [idx_of_lt _ hlt, mul_smul, hgh, inv_smul_smul]
  rw [inv_mul_eq_one] at this
  exact this.symm

end Faithful

end CFSG.Sporadic.J3
