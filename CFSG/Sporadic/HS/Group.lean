module

public import CFSG.Sporadic.HS.CertSpec
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Certificates.SchreierStabilizerGenerators
public import CFSG.Sporadic.Th.OrbitSpec
public import CFSG.Sporadic.HS.SmallF2Spec

public section

namespace CFSG.Sporadic.SmallF2

open Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Matrix
open scoped Matrix

variable (D : VecData)

noncomputable abbrev mA : Matrix (Fin D.d) (Fin D.d) (ZMod 2) :=
  CFSG.Blueprint.NativeSporadic.decode 2 D.d 1 D.seedA

noncomputable abbrev mB : Matrix (Fin D.d) (Fin D.d) (ZMod 2) :=
  CFSG.Blueprint.NativeSporadic.decode 2 D.d 1 D.seedB

theorem rowsMatrix_rowsA : rowsMatrix D.d D.rowsA = mA D := rowsMatrix_rowsOfPayload D.d D.seedA

theorem rowsMatrix_rowsB : rowsMatrix D.d D.rowsB = mB D := rowsMatrix_rowsOfPayload D.d D.seedB

@[expose] noncomputable def gA : GL (Fin D.d) (ZMod 2) :=
  if h : (mA D).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (mA D) h else 1

@[expose] noncomputable def gB : GL (Fin D.d) (ZMod 2) :=
  if h : (mB D).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (mB D) h else 1

noncomputable abbrev J : Subgroup (GL (Fin D.d) (ZMod 2)) := Subgroup.closure {gA D, gB D}

@[expose] noncomputable def a : J D := ⟨gA D, Subgroup.subset_closure (Set.mem_insert _ _)⟩

@[expose] noncomputable def b : J D :=
  ⟨gB D, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

theorem closure_ab : Subgroup.closure ({a D, b D} : Set (J D)) = ⊤ := by
  have h := CFSG.Certificates.schreier_subtype_generators_generate
    ({gA D, gB D} : Set (GL (Fin D.d) (ZMod 2)))
  convert h using 2
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage, Subgroup.coe_subtype]
  constructor
  · rintro (rfl | rfl) <;> simp [a, b]
  · rintro (h | h)
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h

abbrev Vec : Type := Fin D.d → ZMod 2

theorem smul_vec (g : J D) (v : Vec D) :
    g • v = ((g : GL (Fin D.d) (ZMod 2)) : Matrix (Fin D.d) (Fin D.d) (ZMod 2)) *ᵥ v := rfl

noncomputable abbrev P (i : ℕ) : Vec D := toVecD D.d (O D).pts[i]!

section Base

variable {D} (hB : BaseFacts D)
include hB

theorem mA_pow : mA D ^ D.expA = 1 := by
  have := congrArg (rowsMatrix D.d) hB.powA
  rwa [rowsMatrix_powRows, rowsMatrix_idRows, rowsMatrix_rowsA] at this

theorem mB_pow : mB D ^ D.expB = 1 := by
  have := congrArg (rowsMatrix D.d) hB.powB
  rwa [rowsMatrix_powRows, rowsMatrix_idRows, rowsMatrix_rowsB] at this

theorem det_mA_ne_zero : (mA D).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (mA_pow hB)
  rw [Matrix.det_pow, h, zero_pow (Nat.pos_iff_ne_zero.mp hB.expA_pos), Matrix.det_one] at this
  exact zero_ne_one this

theorem det_mB_ne_zero : (mB D).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (mB_pow hB)
  rw [Matrix.det_pow, h, zero_pow (Nat.pos_iff_ne_zero.mp hB.expB_pos), Matrix.det_one] at this
  exact zero_ne_one this

theorem gA_eq : gA D = Matrix.GeneralLinearGroup.mkOfDetNeZero (mA D) (det_mA_ne_zero hB) := by
  unfold gA; rw [dite_eq_left (det_mA_ne_zero hB)]

theorem gB_eq : gB D = Matrix.GeneralLinearGroup.mkOfDetNeZero (mB D) (det_mB_ne_zero hB) := by
  unfold gB; rw [dite_eq_left (det_mB_ne_zero hB)]

theorem a_val : (((a D : J D) : GL (Fin D.d) (ZMod 2)) : Matrix (Fin D.d) (Fin D.d) (ZMod 2)) =
    mA D := by
  show ((gA D : GL (Fin D.d) (ZMod 2)) : Matrix (Fin D.d) (Fin D.d) (ZMod 2)) = mA D
  rw [gA_eq hB]; rfl

theorem b_val : (((b D : J D) : GL (Fin D.d) (ZMod 2)) : Matrix (Fin D.d) (Fin D.d) (ZMod 2)) =
    mB D := by
  show ((gB D : GL (Fin D.d) (ZMod 2)) : Matrix (Fin D.d) (Fin D.d) (ZMod 2)) = mB D
  rw [gB_eq hB]; rfl

noncomputable def seedEquiv :
    (CFSG.Blueprint.NativeSporadic.seedMonoid 2 D.d 1 D.seedA D.seedB)ˣ ≃* J D :=
  (Blueprint.NativeSporadic.matrixSeedEquiv 2 D.d hB.d_pos (mA D) (mB D) (det_mA_ne_zero hB)
    (det_mB_ne_zero hB)).trans (MulEquiv.subgroupCongr (by
      show _ = Subgroup.closure {gA D, gB D}
      rw [gA_eq hB, gB_eq hB]))

theorem orbit_parts : (O D).pts.size = D.n ∧ (O D).alpha.size = D.n ∧ (O D).beta.size = D.n ∧
    ∀ i < D.n, (O D).pts[i]! < 2 ^ D.d ∧ ((posTable D.d (O D).pts)[(O D).pts[i]!]!).toNat = i ∧
      ap (O D).alpha i < D.n ∧ (O D).pts[ap (O D).alpha i]! = vecMulN D.d D.colsA (O D).pts[i]! ∧
      ap (O D).beta i < D.n ∧ (O D).pts[ap (O D).beta i]! = vecMulN D.d D.colsB (O D).pts[i]! := by
  have h := hB.orbit
  unfold vOrbitOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, fun i hi => ?_⟩
  have := (allIn_eq_true.1 h4) i (Nat.zero_le _) hi
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
  obtain ⟨⟨⟨⟨⟨h5, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := this
  exact ⟨h5, h6, h7, h8, h9, h10⟩

theorem P_injective : ∀ i < D.n, ∀ j < D.n, P D i = P D j → i = j := by
  intro i hi j hj h
  have hi' := (orbit_parts hB).2.2.2 i hi
  have hj' := (orbit_parts hB).2.2.2 j hj
  have e := toVecD_injective hi'.1 hj'.1 h
  rw [← hi'.2.1, ← hj'.2.1, e]

theorem a_smul_P : ∀ i < D.n, ap (O D).alpha i < D.n ∧ a D • P D i = P D (ap (O D).alpha i) := by
  intro i hi
  obtain ⟨-, -, hlt, he, -, -⟩ := (orbit_parts hB).2.2.2 i hi
  refine ⟨hlt, ?_⟩
  rw [smul_vec, a_val hB, ← rowsMatrix_rowsA, rowsMatrix_mulVec, P, he]
  rfl

theorem b_smul_P : ∀ i < D.n, ap (O D).beta i < D.n ∧ b D • P D i = P D (ap (O D).beta i) := by
  intro i hi
  obtain ⟨-, -, -, -, hlt, he⟩ := (orbit_parts hB).2.2.2 i hi
  refine ⟨hlt, ?_⟩
  rw [smul_vec, b_val hB, ← rowsMatrix_rowsB, rowsMatrix_mulVec, P, he]
  rfl

end Base

noncomputable abbrev ptSet : Set (Vec D) := P D '' Set.Iio D.n

theorem smul_mem_ptSet (hB : BaseFacts D) (g : J D) : ∀ v ∈ ptSet D, g • v ∈ ptSet D := by
  refine smul_mem_of_closure (closure_ab D) ((Set.finite_Iio D.n).image _) ?_ ?_ g
  · rintro _ ⟨i, hi, rfl⟩
    exact ⟨_, (a_smul_P hB i hi).1, (a_smul_P hB i hi).2.symm⟩
  · rintro _ ⟨i, hi, rfl⟩
    exact ⟨_, (b_smul_P hB i hi).1, (b_smul_P hB i hi).2.symm⟩

@[expose] noncomputable def ptSub (hB : BaseFacts D) : SubMulAction (J D) (Vec D) where
  carrier := ptSet D
  smul_mem' g _ hv := smul_mem_ptSet D hB g _ hv

@[expose] noncomputable def ptEquiv (hB : BaseFacts D) : Fin D.n ≃ ptSub D hB :=
  Equiv.ofBijective (fun i => ⟨P D i, ⟨i, i.isLt, rfl⟩⟩)
    ⟨fun i j h => Fin.ext (P_injective hB i i.isLt j j.isLt (congrArg Subtype.val h)), by
      rintro ⟨v, ⟨i, hi, rfl⟩⟩
      exact ⟨⟨i, hi⟩, rfl⟩⟩

theorem ptEquiv_apply (hB : BaseFacts D) (i : Fin D.n) : (ptEquiv D hB i : Vec D) = P D i := rfl

noncomputable instance idxAction : MulAction (J D) (Fin D.n) where
  smul g i := by
    classical
    exact if h : BaseFacts D then (ptEquiv D h).symm (g • ptEquiv D h i) else i
  one_smul i := by
    classical
    show (if h : BaseFacts D then (ptEquiv D h).symm ((1 : J D) • ptEquiv D h i) else i) = i
    split
    · rw [one_smul, Equiv.symm_apply_apply]
    · rfl
  mul_smul g h i := by
    classical
    show (if hF : BaseFacts D then (ptEquiv D hF).symm ((g * h) • ptEquiv D hF i) else i) =
      (if hF : BaseFacts D then (ptEquiv D hF).symm (g • ptEquiv D hF
        (if hF : BaseFacts D then (ptEquiv D hF).symm (h • ptEquiv D hF i) else i)) else
        (if hF : BaseFacts D then (ptEquiv D hF).symm (h • ptEquiv D hF i) else i))
    split
    · rw [Equiv.apply_symm_apply, mul_smul]
    · rfl

noncomputable abbrev basisRows : Array ℕ := D.basis.map fun i => (O D).pts[i]!

section Action

variable {D} (hB : BaseFacts D)
include hB

theorem ptEquiv_smul (g : J D) (i : Fin D.n) :
    ptEquiv D hB (g • i) = g • ptEquiv D hB i := by
  have : (g • i : Fin D.n) = (ptEquiv D hB).symm (g • ptEquiv D hB i) := by
    classical
    show (if h : BaseFacts D then (ptEquiv D h).symm (g • ptEquiv D h i) else i) = _
    rw [dite_eq_left hB]
  rw [this, Equiv.apply_symm_apply]

theorem P_smul (g : J D) (i : Fin D.n) : P D (g • i).val = g • P D i.val := by
  have := congrArg Subtype.val (ptEquiv_smul hB g i)
  rwa [ptEquiv_apply, SubMulAction.val_smul, ptEquiv_apply] at this

theorem idx_eq_iff {g : J D} {i j : ℕ} (hi : i < D.n) (hj : j < D.n) :
    idx D.n g i = j ↔ g • P D i = P D j := by
  rw [idx_of_lt g hi]
  constructor
  · intro h
    rw [← P_smul hB g ⟨i, hi⟩, h]
  · intro h
    apply P_injective hB _ (g • (⟨i, hi⟩ : Fin D.n)).isLt _ hj
    rw [P_smul hB g ⟨i, hi⟩]
    exact h

theorem rep_a : Rep D.n (O D).alpha (a D) := by
  intro i hi
  symm
  exact (idx_eq_iff hB hi (a_smul_P hB i hi).1).2 (a_smul_P hB i hi).2

theorem rep_b : Rep D.n (O D).beta (b D) := by
  intro i hi
  symm
  exact (idx_eq_iff hB hi (b_smul_P hB i hi).1).2 (b_smul_P hB i hi).2

theorem basis_rowsMatrix (t k : Fin D.d) :
    rowsMatrix D.d (basisRows D) t k = P D D.basis[t.val]! k := by
  have ht : t.val < D.basis.size := by rw [hB.basis_size]; exact t.isLt
  rw [rowsMatrix_apply, Array.getElem?_map, Array.getElem?_eq_getElem ht, Option.map_some,
    Option.getD_some, getElem!_pos D.basis t.val ht]

theorem eq_one_of_fix_basis (g : J D)
    (hg : ∀ t < D.basis.size, idx D.n g D.basis[t]! = D.basis[t]!) : g = 1 := by
  have hfix : ∀ t : Fin D.d,
      ((g : GL (Fin D.d) (ZMod 2)) : Matrix (Fin D.d) (Fin D.d) (ZMod 2)) *ᵥ P D D.basis[t.val]! =
        P D D.basis[t.val]! := by
    intro t
    have ht : t.val < D.basis.size := by rw [hB.basis_size]; exact t.isLt
    have hlt := hB.basis_lt t.val ht
    have := (idx_eq_iff hB hlt hlt).1 (hg t.val ht)
    rwa [smul_vec] at this
  have hMC : ((g : GL (Fin D.d) (ZMod 2)) : Matrix (Fin D.d) (Fin D.d) (ZMod 2)) *
      (rowsMatrix D.d (basisRows D))ᵀ = (rowsMatrix D.d (basisRows D))ᵀ := by
    ext j t
    have := congrFun (hfix t) j
    rw [Matrix.mul_apply, Matrix.transpose_apply, basis_rowsMatrix hB]
    simp only [Matrix.transpose_apply, basis_rowsMatrix hB]
    rw [← this]
    rfl
  have hinv : rowsMatrix D.d D.basisInv * rowsMatrix D.d (basisRows D) = 1 := by
    have := congrArg (rowsMatrix D.d) hB.basis_inv
    rwa [rowsMatrix_mulRows, rowsMatrix_idRows] at this
  have hinvT : (rowsMatrix D.d (basisRows D))ᵀ * (rowsMatrix D.d D.basisInv)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hinv, Matrix.transpose_one]
  have hM1 : ((g : GL (Fin D.d) (ZMod 2)) : Matrix (Fin D.d) (Fin D.d) (ZMod 2)) = 1 := by
    calc ((g : GL (Fin D.d) (ZMod 2)) : Matrix (Fin D.d) (Fin D.d) (ZMod 2))
        = ((g : GL (Fin D.d) (ZMod 2)) : Matrix (Fin D.d) (Fin D.d) (ZMod 2)) *
          ((rowsMatrix D.d (basisRows D))ᵀ * (rowsMatrix D.d D.basisInv)ᵀ) := by
          rw [hinvT, Matrix.mul_one]
      _ = (((g : GL (Fin D.d) (ZMod 2)) : Matrix (Fin D.d) (Fin D.d) (ZMod 2)) *
          (rowsMatrix D.d (basisRows D))ᵀ) * (rowsMatrix D.d D.basisInv)ᵀ := by
          rw [Matrix.mul_assoc]
      _ = 1 := by rw [hMC, hinvT]
  apply Subtype.ext
  apply Units.ext
  exact hM1

theorem faithful : FaithfulSMul (J D) (Fin D.n) := by
  refine ⟨fun {g h} hgh => ?_⟩
  have : h⁻¹ * g = 1 := by
    apply eq_one_of_fix_basis hB
    intro t ht
    have hlt := hB.basis_lt t ht
    rw [idx_of_lt _ hlt, mul_smul, hgh, inv_smul_smul]
  rw [inv_mul_eq_one] at this
  exact this.symm

end Action

end CFSG.Sporadic.SmallF2
