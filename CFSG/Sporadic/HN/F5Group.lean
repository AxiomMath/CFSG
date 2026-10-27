module

public import CFSG.Sporadic.HN.F5OrbitSpec
public import Certificates.Data.CFSGNative.HN.F5Cert
public import CFSG.Sporadic.He.FpSpec
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Certificates.SchreierStabilizerGenerators
public import CFSG.Sporadic.Th.OrbitSpec
public import CFSG.Sporadic.HN.F5PackedSpec

public section

namespace CFSG.Sporadic.F5

open Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.He.Native Matrix
open scoped Matrix

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

variable (D : F5Data)

noncomputable abbrev mA : Matrix (Fin D.d) (Fin D.d) (ZMod 5) :=
  CFSG.Blueprint.NativeSporadic.decode 5 D.d 1 D.seedA

noncomputable abbrev mB : Matrix (Fin D.d) (Fin D.d) (ZMod 5) :=
  CFSG.Blueprint.NativeSporadic.decode 5 D.d 1 D.seedB

theorem toMat_rowsA : toMat 5 D.d D.rowsA = mA D := toMat_rowsOf 5 D.d D.seedA

theorem toMat_rowsB : toMat 5 D.d D.rowsB = mB D := toMat_rowsOf 5 D.d D.seedB

theorem toMatR_eq_toMat (d : ℕ) (M : Array (Array ℕ)) : toMatR d d M = toMat 5 d M := rfl

@[expose] noncomputable def gA : GL (Fin D.d) (ZMod 5) :=
  if h : (mA D).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (mA D) h else 1

@[expose] noncomputable def gB : GL (Fin D.d) (ZMod 5) :=
  if h : (mB D).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (mB D) h else 1

noncomputable abbrev J : Subgroup (GL (Fin D.d) (ZMod 5)) := Subgroup.closure {gA D, gB D}

@[expose] noncomputable def a : J D := ⟨gA D, Subgroup.subset_closure (Set.mem_insert _ _)⟩

@[expose] noncomputable def b : J D :=
  ⟨gB D, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

theorem closure_ab : Subgroup.closure ({a D, b D} : Set (J D)) = ⊤ := by
  have h := CFSG.Certificates.schreier_subtype_generators_generate
    ({gA D, gB D} : Set (GL (Fin D.d) (ZMod 5)))
  convert h using 2
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage, Subgroup.coe_subtype]
  constructor
  · rintro (rfl | rfl) <;> simp [a, b]
  · rintro (h | h)
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h

noncomputable abbrev mat (g : J D) : Matrix (Fin D.d) (Fin D.d) (ZMod 5) :=
  ((g : GL (Fin D.d) (ZMod 5)) : Matrix (Fin D.d) (Fin D.d) (ZMod 5))

theorem mat_injective : Function.Injective (mat D) := by
  intro g h e
  exact Subtype.ext (Units.ext e)

abbrev Vec : Type := Fin D.d → ZMod 5

theorem smul_vec (g : J D) (v : Vec D) : g • v = mat D g *ᵥ v := rfl

noncomputable abbrev O : VOrbit := D.orbit ()

noncomputable abbrev P (i : ℕ) : Vec D := toVecB D.d (O D).keys[i]!

structure BaseFacts : Prop where
  d_pos : 0 < D.d
  d_le : D.d ≤ 135
  expA_pos : 0 < D.expA
  expB_pos : 0 < D.expB
  powA : powM 5 D.d D.rowsA D.expA = idM D.d
  powB : powM 5 D.d D.rowsB D.expB = idM D.d
  vf : VecFacts D.d (D.tabA ()) (D.tabB ()) D.v0 (O D)
  keys_size : (O D).keys.size = D.n
  alpha_size : (O D).alpha.size = D.n
  beta_size : (O D).beta.size = D.n
  n_lt : D.n < 2 ^ 30
  invA : invOK D.n (O D).alpha (invT D.n (O D).alpha) = true
  invB : invOK D.n (O D).beta (invT D.n (O D).beta) = true
  Q_size : D.d ≤ D.Q.size
  Q_lt : ∀ t < D.Q.size, D.Q[t]! < D.n
  basis : basisCheck D (O D) = true

section Base

variable {D} (hB : BaseFacts D)
include hB

theorem mA_pow : mA D ^ D.expA = 1 := by
  have := congrArg (toMat 5 D.d) hB.powA
  rwa [toMat_powM, toMat_idM, toMat_rowsA] at this

theorem mB_pow : mB D ^ D.expB = 1 := by
  have := congrArg (toMat 5 D.d) hB.powB
  rwa [toMat_powM, toMat_idM, toMat_rowsB] at this

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

theorem mat_a : mat D (a D) = mA D := by
  show ((gA D : GL (Fin D.d) (ZMod 5)) : Matrix (Fin D.d) (Fin D.d) (ZMod 5)) = mA D
  rw [gA_eq hB]; rfl

theorem mat_b : mat D (b D) = mB D := by
  show ((gB D : GL (Fin D.d) (ZMod 5)) : Matrix (Fin D.d) (Fin D.d) (ZMod 5)) = mB D
  rw [gB_eq hB]; rfl

noncomputable def seedEquiv :
    (CFSG.Blueprint.NativeSporadic.seedMonoid 5 D.d 1 D.seedA D.seedB)ˣ ≃* J D :=
  (Blueprint.NativeSporadic.matrixSeedEquiv 5 D.d hB.d_pos (mA D) (mB D) (det_mA_ne_zero hB)
    (det_mB_ne_zero hB)).trans (MulEquiv.subgroupCongr (by
      show _ = Subgroup.closure {gA D, gB D}
      rw [gA_eq hB, gB_eq hB]))

theorem keys_canon {i : ℕ} (hi : i < D.n) : canonB D.d (O D).keys[i]! = true :=
  hB.vf.canon i (by rw [hB.keys_size]; exact hi)

theorem P_injective : ∀ i < D.n, ∀ j < D.n, P D i = P D j → i = j := by
  intro i hi j hj h
  have e := eq_of_toVecB_eq (keys_canon hB hi) (keys_canon hB hj) h
  exact hB.vf.inj i (by rw [hB.keys_size]; exact hi) j (by rw [hB.keys_size]; exact hj) e

theorem a_smul_P : ∀ i < D.n, ap (O D).alpha i < D.n ∧ a D • P D i = P D (ap (O D).alpha i) := by
  intro i hi
  have hi' : i < (O D).keys.size := by rw [hB.keys_size]; exact hi
  obtain ⟨hlt, he⟩ := hB.vf.alpha i hi'
  refine ⟨by rw [← hB.keys_size]; exact hlt, ?_⟩
  rw [smul_vec, mat_a hB, ← toMat_rowsA, ← toMatR_eq_toMat, P, P, he,
    ← toVecB_mulW (by have := hB.d_le; omega) hB.d_le _ (keys_canon hB hi)]
  rfl

theorem b_smul_P : ∀ i < D.n, ap (O D).beta i < D.n ∧ b D • P D i = P D (ap (O D).beta i) := by
  intro i hi
  have hi' : i < (O D).keys.size := by rw [hB.keys_size]; exact hi
  obtain ⟨hlt, he⟩ := hB.vf.beta i hi'
  refine ⟨by rw [← hB.keys_size]; exact hlt, ?_⟩
  rw [smul_vec, mat_b hB, ← toMat_rowsB, ← toMatR_eq_toMat, P, P, he,
    ← toVecB_mulW (by have := hB.d_le; omega) hB.d_le _ (keys_canon hB hi)]
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

theorem bytesToNats_get (v : ByteArray) (j : ℕ) : (bytesToNats v)[j]! = (v.get! j).toNat := by
  unfold bytesToNats
  by_cases hj : j < v.data.size
  · rw [getElem!_pos _ j (by simpa using hj), Array.getElem_map]
    simp only [ByteArray.get!]
    rw [getElem!_pos v.data j hj]
  · rw [getElem!_neg _ j (by simpa using hj)]
    simp only [ByteArray.get!]
    rw [getElem!_neg v.data j hj]
    rfl

noncomputable abbrev QVecs : Array (Array ℕ) := D.Q.map fun q => bytesToNats (O D).keys[q]!

noncomputable abbrev basisM : Matrix (Fin D.d) (Fin D.d) (ZMod 5) :=
  toMat 5 D.d (colsMat D.d (QVecs D))

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

theorem basisM_apply (i t : Fin D.d) : basisM D i t = P D D.Q[t.val]! i := by
  rw [basisM, toMat_colsMat, toVec_apply]
  have ht : t.val < D.Q.size := lt_of_lt_of_le t.isLt hB.Q_size
  rw [getElem!_pos (QVecs D) t.val (by simp; exact ht), Array.getElem_map, bytesToNats_get,
    getElem!_pos D.Q t.val ht]
  rfl

theorem basisM_mul_inv : basisM D * toMat 5 D.d (invM 5 D.d (colsMat D.d (QVecs D))) = 1 := by
  have h := hB.basis
  unfold basisCheck at h
  have e := toMat_eq_of_beq (p := 5) (d := D.d) h
  rwa [toMat_mulM, toMat_idM] at e

theorem eq_one_of_fix_Q (g : J D) (hg : ∀ t < D.Q.size, idx D.n g D.Q[t]! = D.Q[t]!) : g = 1 := by
  have hfix : ∀ t : Fin D.d, mat D g *ᵥ P D D.Q[t.val]! = P D D.Q[t.val]! := by
    intro t
    have ht : t.val < D.Q.size := lt_of_lt_of_le t.isLt hB.Q_size
    have hlt := hB.Q_lt t.val ht
    have := (idx_eq_iff hB hlt hlt).1 (hg t.val ht)
    rwa [smul_vec] at this
  have hM : mat D g * basisM D = basisM D := by
    ext i t
    have := congrFun (hfix t) i
    rw [Matrix.mulVec, dotProduct] at this
    rw [Matrix.mul_apply, basisM_apply hB, ← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [basisM_apply hB]
  apply mat_injective D
  have h1 : mat D (1 : J D) = 1 := rfl
  rw [h1]
  calc mat D g = mat D g * (basisM D * toMat 5 D.d (invM 5 D.d (colsMat D.d (QVecs D)))) := by
        rw [basisM_mul_inv hB, mul_one]
    _ = (mat D g * basisM D) * toMat 5 D.d (invM 5 D.d (colsMat D.d (QVecs D))) := by
        rw [mul_assoc]
    _ = 1 := by rw [hM, basisM_mul_inv hB]

theorem faithful : FaithfulSMul (J D) (Fin D.n) := by
  refine ⟨fun {g h} hgh => ?_⟩
  have : h⁻¹ * g = 1 := by
    apply eq_one_of_fix_Q hB
    intro t ht
    have hlt := hB.Q_lt t ht
    rw [idx_of_lt _ hlt, mul_smul, hgh, inv_smul_smul]
  rw [inv_mul_eq_one] at this
  exact this.symm

end Action

end CFSG.Sporadic.F5
