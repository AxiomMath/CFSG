module

public import CFSG.Sporadic.Schreier.PairJ3FaithfulCheck
public import CFSG.Sporadic.J3
public import CFSG.Certificates.InvariantQuadraticCentralizerAction
import all CFSG.Blueprint.NativeSporadic

public noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Schreier

open CFSG.Sporadic.Schreier.PairF2 CFSG.Sporadic.Schreier.PairJ3 CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  Matrix

theorem rep_j3Gen
    {k : ℕ} (hk : k < 5) : Rep 6156 j3StrongArrs[k]! (j3Gen k) :=
  rep_j3StrongPerm hk

theorem j3StrongArrs_get_lt
    {k : ℕ} (hk : k < 2) {r : ℕ} (hr : r < 6156) :
    (j3StrongArrs[k]!)[r]! < 6156 := by
  have := rep_j3Gen (by omega : k < 5) ⟨r, hr⟩
  rw [show (j3StrongArrs[k]!)[r]! = (j3StrongArrs[k]!)[((⟨r, hr⟩ : Fin 6156) : ℕ)]! from rfl, this]
  exact Fin.isLt _

theorem tri_get {bytes : ByteArray} {r : ℕ} (hr : r < 6156) :
    (Array.ofFn (n := 6156) fun r : Fin 6156 => triRowsZ 80 (hexAt bytes (810 * r.val) 810))[r]! =
      triRowsZ 80 (hexAt bytes (810 * r) 810) := by
  rw [getElem!_pos _ r (by simpa using hr), Array.getElem_ofFn]

theorem j3FormWord_eq (r : ℕ) : j3FormWord r = hexAt j3FormsHex.toUTF8 (810 * r) 810 := rfl

theorem j3_form_facts
    {r : ℕ} (hr : r < 6156) :
    packRowsZ 80 (triRowsZ 80 (j3FormWord r)) = j3FormWord r ∧
      pullOKZ 80 rowsA1 (j3FormWord r) (j3FormWord (j3StrongArrs[0]!)[r]!) = true ∧
      pullOKZ 80 rowsA2 (j3FormWord r) (j3FormWord (j3StrongArrs[1]!)[r]!) = true := by
  have hc := forms_check
  unfold formsCheckWith at hc
  have h := parLt_spec (by norm_num) hc r hr
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h3⟩, h4⟩ := h
  rw [tri_get hr] at h1 h3 h4
  rw [tri_get (j3StrongArrs_get_lt (k := 0) (by norm_num) hr)] at h3
  rw [tri_get (j3StrongArrs_get_lt (k := 1) (by norm_num) hr)] at h4
  simp only [j3FormWord_eq]
  exact ⟨h1, h3, h4⟩

theorem j3FormWord_inj {r s : ℕ} (hr : r < 6156) (hs : s < 6156)
    (h : j3FormWord r = j3FormWord s) : r = s := by
  have hsort := pairwise_of_strictInc distinct_check
  have hnd : ((List.range 6156).map j3FormWord).Nodup := by
    have := (List.mergeSort_perm ((List.range 6156).map fun r => hexAt j3FormsHex.toUTF8
      (810 * r) 810) (fun a b => decide (a ≤ b))).nodup_iff.1
      (hsort.imp fun hab => Nat.ne_of_lt hab)
    exact this
  exact List.inj_on_of_nodup_map hnd (List.mem_range.2 hr) (List.mem_range.2 hs) h

theorem j3Form_injective
    {r s : ℕ} (hr : r < 6156) (hs : s < 6156) (h : j3Form r = j3Form s) :
    r = s :=
  j3FormWord_inj hr hs (eq_of_quadZ_eq (j3_form_facts hr).1 (j3_form_facts hs).1 h)

abbrev j3A1 : Matrix (Fin 80) (Fin 80) (ZMod 2) :=
  Blueprint.NativeSporadic.decode 2 80 1 Blueprint.NativeSporadic.J3Seed1

abbrev j3A2 : Matrix (Fin 80) (Fin 80) (ZMod 2) :=
  Blueprint.NativeSporadic.decode 2 80 1 Blueprint.NativeSporadic.J3Seed2

private theorem j3Data_seedA :
    CFSG.Sporadic.J3.Native.j3Data.seedA = Blueprint.NativeSporadic.J3Seed1 := rfl

private theorem j3Data_seedB :
    CFSG.Sporadic.J3.Native.j3Data.seedB = Blueprint.NativeSporadic.J3Seed2 := rfl

theorem mA_j3Data : CFSG.Sporadic.J3.mA CFSG.Sporadic.J3.Native.j3Data = j3A1 := by
  show Blueprint.NativeSporadic.decode 2 80 1 CFSG.Sporadic.J3.Native.j3Data.seedA = _
  rw [j3Data_seedA]

theorem mB_j3Data : CFSG.Sporadic.J3.mB CFSG.Sporadic.J3.Native.j3Data = j3A2 := by
  show Blueprint.NativeSporadic.decode 2 80 1 CFSG.Sporadic.J3.Native.j3Data.seedB = _
  rw [j3Data_seedB]

theorem rowsMatrix_rowsA1 : rowsMatrix 80 rowsA1 = j3A1 := by
  rw [← mA_j3Data]
  exact CFSG.Sporadic.J3.rowsMatrix_rowsA _

theorem rowsMatrix_rowsA2 : rowsMatrix 80 rowsA2 = j3A2 := by
  rw [← mB_j3Data]
  exact CFSG.Sporadic.J3.rowsMatrix_rowsB _

theorem det_j3A1 : j3A1.det ≠ 0 := by
  rw [← mA_j3Data]
  exact CFSG.Sporadic.J3.det_mA_ne_zero CFSG.Sporadic.J3.j3Facts.powA

theorem det_j3A2 : j3A2.det ≠ 0 := by
  rw [← mB_j3Data]
  exact CFSG.Sporadic.J3.det_mB_ne_zero CFSG.Sporadic.J3.j3Facts.powB

@[expose] def j3SeedGL (k : ℕ) : GL (Fin 80) (ZMod 2) :=
  if k = 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero j3A1 det_j3A1
  else Matrix.GeneralLinearGroup.mkOfDetNeZero j3A2 det_j3A2

theorem j3SeedGL_val (k : ℕ) :
    ((j3SeedGL k : GL (Fin 80) (ZMod 2)) : Matrix (Fin 80) (Fin 80) (ZMod 2)) =
      if k = 0 then j3A1 else j3A2 := by
  unfold j3SeedGL
  split_ifs <;> rfl

theorem j3SeedGL_mulVec_inv (k : ℕ) (v : J3V) :
    ((j3SeedGL k : Matrix (Fin 80) (Fin 80) (ZMod 2))) *ᵥ
      (((j3SeedGL k)⁻¹ : GL (Fin 80) (ZMod 2)) : Matrix (Fin 80) (Fin 80) (ZMod 2)) *ᵥ v = v := by
  rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

theorem j3Form_seed
    {k : ℕ} (hk : k < 2) (r : Fin 6156) (v : J3V) :
    j3Form r v = j3Form (j3Gen k r) ((if k = 0 then j3A1 else j3A2) *ᵥ v) := by
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · have h := pullOKZ_spec (j3_form_facts r.2).2.1 v
    rw [rowsMatrix_rowsA1, rep_j3Gen (by norm_num : 0 < 5) r] at h
    rw [ite_eq_left rfl]
    exact h
  · have h := pullOKZ_spec (j3_form_facts r.2).2.2 v
    rw [rowsMatrix_rowsA2, rep_j3Gen (by norm_num : 1 < 5) r] at h
    rw [ite_eq_right one_ne_zero]
    exact h

theorem j3Form_seed_inv
    {k : ℕ} (hk : k < 2) (r : Fin 6156) (v : J3V) :
    j3Form r ((((j3SeedGL k)⁻¹ : GL (Fin 80) (ZMod 2)) : Matrix (Fin 80) (Fin 80) (ZMod 2)) *ᵥ
      v) = j3Form (j3Gen k r) v := by
  rw [j3Form_seed hk, ← j3SeedGL_val, j3SeedGL_mulVec_inv]

theorem j3InvForm_seed {k : ℕ} (hk : k < 2) (v : J3V) :
    j3InvForm v = j3InvForm ((if k = 0 then j3A1 else j3A2) *ᵥ v) := by
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · have h := pullOKZ_spec inv_check.1 v
    rw [rowsMatrix_rowsA1] at h
    rw [ite_eq_left rfl]
    exact h
  · have h := pullOKZ_spec inv_check.2.1 v
    rw [rowsMatrix_rowsA2] at h
    rw [ite_eq_right one_ne_zero]
    exact h

theorem j3InvForm_seed_inv
    {k : ℕ} (hk : k < 2) (v : J3V) :
    j3InvForm ((((j3SeedGL k)⁻¹ : GL (Fin 80) (ZMod 2)) : Matrix (Fin 80) (Fin 80) (ZMod 2)) *ᵥ
      v) = j3InvForm v := by
  rw [j3InvForm_seed hk, ← j3SeedGL_val, j3SeedGL_mulVec_inv]

theorem j3B_eq : j3B = rowsMatrix 80 BRows := (rowsMatrix_polarRowsZ _).symm

theorem BInv_mul_j3B : rowsMatrix 80 BInv * j3B = 1 := by
  rw [j3B_eq, ← rowsMatrix_mulRows, inv_check.2.2, rowsMatrix_idRows]

theorem isUnit_j3B : IsUnit j3B :=
  (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_left_inverse BInv_mul_j3B)

theorem j3B_inv :
    j3B⁻¹ = rowsMatrix 80 BInv := Matrix.inv_eq_left_inv BInv_mul_j3B

theorem j3B_mul_inv : j3B * j3B⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 isUnit_j3B)

@[expose] def j3T (r : ℕ) : Matrix (Fin 80) (Fin 80) (ZMod 2) := j3B⁻¹ * polarMatrix (j3Form r)

theorem TRows_size : TRows.size = 4 := by simp [TRows]

theorem TRows_get {r : ℕ} (hr : r < 4) :
    TRows[r]! = mulRows 80 BInv (polarRowsZ 80 (j3FormWord r)) := by
  unfold TRows
  rw [getElem!_pos _ r (by simpa using hr), Array.getElem_ofFn]

theorem rowsMatrix_TRows
    {r : ℕ} (hr : r < 4) : rowsMatrix 80 TRows[r]! = j3T r := by
  rw [TRows_get hr, rowsMatrix_mulRows, rowsMatrix_polarRowsZ, j3T, j3B_inv]
  rfl

theorem j3_commutant (M : Matrix (Fin 80) (Fin 80) (ZMod 2))
    (hM : ∀ r ∈ j3CentralizerIdx, M * j3T r = j3T r * M) : M = 0 ∨ M = 1 := by
  have h := sep_check
  unfold sepCheckWith at h
  refine eq_zero_or_one_of_sepF2OK h (by decide) M fun i hi => ?_
  rw [TRows_size] at hi
  rw [rowsMatrix_TRows hi]
  exact hM i (by simp [j3CentralizerIdx]; omega)

@[expose] def j3CommMap :
    Matrix (Fin 80) (Fin 80) (ZMod 2) →ₗ[ZMod 2] (Fin 4 → Matrix (Fin 80) (Fin 80) (ZMod 2)) where
  toFun M t := M * j3T (j3CentralizerIdx.getD t 0) - j3T (j3CentralizerIdx.getD t 0) * M
  map_add' M N := by
    funext t
    simp only [Pi.add_apply, add_mul, mul_add]
    abel
  map_smul' c M := by
    funext t
    simp only [Pi.smul_apply, RingHom.id_apply, smul_sub, Matrix.smul_mul, Matrix.mul_smul]

theorem mem_ker_j3CommMap (M : Matrix (Fin 80) (Fin 80) (ZMod 2)) :
    M ∈ LinearMap.ker j3CommMap ↔ M = 0 ∨ M = 1 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    refine j3_commutant M fun r hr => ?_
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hr
    have := congrFun h ⟨t, by simpa [j3CentralizerIdx] using ht⟩
    simp only [j3CommMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this
    rw [List.getD_eq_getElem _ _ ht] at this
    exact sub_eq_zero.1 this
  · rintro (rfl | rfl)
    · funext t
      simp [j3CommMap]
    · funext t
      simp [j3CommMap]

theorem ker_j3CommMap_eq_set :
    (LinearMap.ker j3CommMap : Set (Matrix (Fin 80) (Fin 80) (ZMod 2))) = {0, 1} := by
  ext M
  rw [SetLike.mem_coe, mem_ker_j3CommMap]
  simp

theorem ker_j3CommMap :
    LinearMap.ker j3CommMap = Submodule.span (ZMod 2) {1} := by
  ext M
  rw [mem_ker_j3CommMap, Submodule.mem_span_singleton]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨0, zero_smul _ _⟩
    · exact ⟨1, one_smul _ _⟩
  · rintro ⟨c, rfl⟩
    rcases zmod2_eq_zero_or_one c with rfl | rfl
    · left; exact zero_smul _ _
    · right; exact one_smul _ _

theorem finrank_range_j3CommMap :
    Module.finrank (ZMod 2) (LinearMap.range j3CommMap) = 6399 := by
  have h := LinearMap.finrank_range_add_finrank_ker j3CommMap
  rw [ker_j3CommMap, finrank_span_singleton one_ne_zero, Module.finrank_matrix,
    Module.finrank_self, Fintype.card_fin] at h
  omega

abbrev J3GL : Type := LinearMap.GeneralLinearGroup (ZMod 2) J3V

@[expose] def j3SeedLin
    (k : Fin 2) : J3GL := Matrix.GeneralLinearGroup.toLin (j3SeedGL k)

@[expose] def j3G :
    Subgroup J3GL := Subgroup.closure (Set.range j3SeedLin)

@[expose] def j3Bil : LinearMap.BilinForm (ZMod 2) J3V := Matrix.toBilin' j3B

@[expose] def j3S : Set (J3V → ZMod 2) := {q | ∃ r ∈ j3CentralizerIdx, j3Form r = q}

@[expose] def j3TLin (q : J3V → ZMod 2) : Module.End (ZMod 2) J3V :=
  Matrix.toLin' (j3B⁻¹ * polarMatrix q)

theorem j3X_finite : j3X.Finite := by
  have : j3X = j3Form '' {r | r < 6156} := by
    ext q
    simp only [j3X, Set.mem_ofPred_eq, Set.mem_image]
  rw [this]
  exact (Set.finite_lt_nat 6156).image _

theorem j3X_nonempty : j3X.Nonempty := ⟨j3Form 0, 0, by norm_num, rfl⟩

theorem j3_polar (q : J3V → ZMod 2) (hq : q ∈ j3X) (u v : J3V) :
    Matrix.toBilin' (polarMatrix q) u v = q (u + v) + q u + q v := by
  obtain ⟨r, -, rfl⟩ := hq
  rw [Matrix.toBilin'_apply', j3Form, j3Quad, polar_quadZ]

theorem j3SeedLin_apply (k : Fin 2) (v : J3V) :
    (j3SeedLin k : J3V →ₗ[ZMod 2] J3V) v = (j3SeedGL k : Matrix _ _ (ZMod 2)) *ᵥ v :=
  Matrix.GeneralLinearGroup.toLin_apply _ v

theorem j3SeedLin_inv_apply (k : Fin 2) (v : J3V) :
    (((j3SeedLin k)⁻¹ : J3GL) : J3V →ₗ[ZMod 2] J3V) v =
      (((j3SeedGL k)⁻¹ : GL (Fin 80) (ZMod 2)) : Matrix _ _ (ZMod 2)) *ᵥ v := by
  rw [j3SeedLin, ← map_inv]
  exact Matrix.GeneralLinearGroup.toLin_apply _ v

theorem j3Bil_apply (u v : J3V) :
    j3Bil u v = j3InvForm (u + v) + j3InvForm u + j3InvForm v := by
  rw [j3Bil, Matrix.toBilin'_apply', j3B, j3InvForm, j3Quad, polar_quadZ]

theorem j3Bil_seed
    (k : Fin 2) (u v : J3V) :
    j3Bil ((j3SeedLin k : J3V →ₗ[ZMod 2] J3V) u) ((j3SeedLin k : J3V →ₗ[ZMod 2] J3V) v) =
      j3Bil u v := by
  have hk : (k : ℕ) < 2 := k.2
  rw [j3Bil_apply, j3Bil_apply, j3SeedLin_apply, j3SeedLin_apply, ← mulVec_add,
    j3SeedGL_val, ← j3InvForm_seed hk, ← j3InvForm_seed hk, ← j3InvForm_seed hk]

theorem funAct_j3Form
    (k : Fin 2) (r : Fin 6156) :
    funAct (j3SeedLin k) (j3Form r) = j3Form (j3Gen k r) := by
  funext v
  rw [funAct, j3SeedLin_inv_apply, j3Form_seed_inv k.2]

theorem j3Seed_mapsTo
    (k : Fin 2) : ∀ q ∈ j3X, funAct (j3SeedLin k) q ∈ j3X := by
  rintro _ ⟨r, hr, rfl⟩
  refine ⟨j3Gen k ⟨r, hr⟩, (j3Gen k ⟨r, hr⟩).2, ?_⟩
  rw [← funAct_j3Form k ⟨r, hr⟩]

theorem j3S_subset : j3S ⊆ j3X := by
  rintro _ ⟨r, hr, rfl⟩
  refine ⟨r, ?_, rfl⟩
  simp only [j3CentralizerIdx, List.mem_cons, List.not_mem_nil, or_false] at hr
  omega

theorem j3TLin_spec :
    ∀ q ∈ j3S, ∀ u v, j3Bil u (j3TLin q v) = q (u + v) + q u + q v := by
  intro q hq u v
  rw [j3Bil, j3TLin, Matrix.toBilin'_apply', Matrix.toLin'_apply', Matrix.mulVecLin_apply,
    mulVec_mulVec, ← mul_assoc, j3B_mul_inv, one_mul, ← Matrix.toBilin'_apply',
    j3_polar q (j3S_subset hq)]

theorem j3_centralizer :
    {M : Module.End (ZMod 2) J3V | ∀ q ∈ j3S, M * j3TLin q = j3TLin q * M} = {0, 1} := by
  ext M
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    rcases j3_commutant (LinearMap.toMatrix' M) fun r hr => by
      have := congrArg LinearMap.toMatrix' (h (j3Form r) ⟨r, hr, rfl⟩)
      rwa [LinearMap.toMatrix'_mul, LinearMap.toMatrix'_mul, j3TLin,
        LinearMap.toMatrix'_toLin'] at this with h0 | h1
    · left
      rw [← Matrix.toLin'_toMatrix' M, h0, map_zero]
    · right
      rw [← Matrix.toLin'_toMatrix' M, h1, Matrix.toLin'_one]
      rfl
  · rintro (rfl | rfl) q _
    · rw [zero_mul, mul_zero]
    · rw [one_mul, mul_one]

theorem j3Bil_nondegenerate : j3Bil.Nondegenerate :=
  LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.2
    ((Matrix.isUnit_iff_isUnit_det _).1 isUnit_j3B).ne_zero

theorem j3_faithful :
    ∃ ρ : Subgroup.closure (Set.range j3SeedLin) →* Equiv.Perm j3X,
      (∀ g q, ((ρ g q : j3X) : J3V → ZMod 2) = funAct (g : J3GL) q) ∧
      Function.Injective ρ ∧
      ρ.range = Subgroup.closure (Set.range fun i =>
        ρ ⟨j3SeedLin i, Subgroup.subset_closure (Set.mem_range_self i)⟩) :=
  invariant_quadratic_centralizer_faithful_action j3Bil j3Bil_nondegenerate j3X j3X_finite
    j3X_nonempty (fun q hq => ⟨Matrix.toBilin' (polarMatrix q), j3_polar q hq⟩) j3SeedLin
    j3Bil_seed j3Seed_mapsTo j3S j3S_subset j3TLin j3TLin_spec j3_centralizer

@[expose] def j3RhoX :
    j3G →* Equiv.Perm j3X := j3_faithful.choose

theorem j3RhoX_apply
    (g : j3G) (q : j3X) :
    ((j3RhoX g q : j3X) : J3V → ZMod 2) = funAct (g : J3GL) q :=
  j3_faithful.choose_spec.1 g q

theorem j3RhoX_injective :
    Function.Injective j3RhoX := j3_faithful.choose_spec.2.1

theorem j3RhoX_range :
    j3RhoX.range = Subgroup.closure (Set.range fun i =>
    j3RhoX ⟨j3SeedLin i, Subgroup.subset_closure (Set.mem_range_self i)⟩) :=
  j3_faithful.choose_spec.2.2

@[expose] def j3XEquiv :
    Fin 6156 ≃ j3X :=
  Equiv.ofBijective (fun r => ⟨j3Form r, (r : ℕ), r.2, rfl⟩)
    ⟨fun r r' h => by
        have h' := congrArg Subtype.val h
        exact Fin.ext (j3Form_injective r.2 r'.2 h'),
      fun ⟨_, r, hr, hq⟩ => ⟨⟨r, hr⟩, Subtype.ext hq⟩⟩

theorem j3XEquiv_apply
    (r : Fin 6156) : (j3XEquiv r : J3V → ZMod 2) = j3Form r := rfl

@[expose] def j3Rho :
    j3G →* Equiv.Perm (Fin 6156) :=
  j3XEquiv.symm.permCongrHom.toMonoidHom.comp j3RhoX

theorem j3XEquiv_rho
    (g : j3G) (r : Fin 6156) :
    j3XEquiv (j3Rho g r) = j3RhoX g (j3XEquiv r) := by
  change j3XEquiv (j3XEquiv.symm (j3RhoX g (j3XEquiv.symm.symm r))) = _
  rw [Equiv.apply_symm_apply, Equiv.symm_symm]

theorem j3Form_rho
    (g : j3G) (r : Fin 6156) :
    j3Form (j3Rho g r) = funAct (g : J3GL) (j3Form r) := by
  have h := congrArg Subtype.val (j3XEquiv_rho g r)
  rw [j3XEquiv_apply, j3RhoX_apply, j3XEquiv_apply] at h
  exact h

theorem j3Rho_injective :
    Function.Injective j3Rho :=
  j3XEquiv.symm.permCongrHom.injective.comp j3RhoX_injective

theorem j3Rho_seed
    (k : Fin 2) :
    j3Rho ⟨j3SeedLin k, Subgroup.subset_closure ⟨k, rfl⟩⟩ = j3Gen k := by
  refine Equiv.ext fun r => Fin.ext (j3Form_injective (Fin.isLt _) (Fin.isLt _) ?_)
  rw [j3Form_rho]
  exact funAct_j3Form k r

theorem j3P_eq_range : j3P = Subgroup.closure (Set.range fun k : Fin 2 => j3Gen k) := by
  rw [j3P]
  congr 1
  ext g
  simp [Fin.exists_fin_two, eq_comm]

theorem j3Rho_range :
    j3Rho.range = j3P := by
  rw [j3Rho, MonoidHom.range_comp, j3RhoX_range, MonoidHom.map_closure, j3P_eq_range]
  congr 1
  ext σ
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨k, (j3Rho_seed k).symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨_, ⟨k, rfl⟩, j3Rho_seed k⟩

@[expose] def j3ToLin : GL (Fin 80) (ZMod 2) →* J3GL :=
  Matrix.GeneralLinearGroup.toLin.toMonoidHom

theorem j3ToLin_injective : Function.Injective j3ToLin :=
  Matrix.GeneralLinearGroup.toLin.injective

theorem j3SeedLin_eq
    (k : Fin 2) : j3SeedLin k = j3ToLin (j3SeedGL k) := rfl

abbrev j3J : Subgroup (GL (Fin 80) (ZMod 2)) :=
  Subgroup.closure {Matrix.GeneralLinearGroup.mkOfDetNeZero j3A1 det_j3A1,
    Matrix.GeneralLinearGroup.mkOfDetNeZero j3A2 det_j3A2}

theorem j3SeedGL_mem (k : ℕ) : j3SeedGL k ∈ j3J := by
  unfold j3SeedGL
  split_ifs
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem j3ToLin_mem (g : j3J) : j3ToLin g ∈ j3G := by
  obtain ⟨g, hg⟩ := g
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact Subgroup.subset_closure ⟨0, by rw [j3SeedLin_eq]; rfl⟩
    · exact Subgroup.subset_closure ⟨1, by rw [j3SeedLin_eq]; rfl⟩
  | one => rw [map_one]; exact j3G.one_mem
  | mul x y _ _ hx hy => rw [map_mul]; exact j3G.mul_mem hx hy
  | inv x _ hx => rw [map_inv]; exact j3G.inv_mem hx

@[expose] def j3JHom : j3J →* j3G :=
  (j3ToLin.comp j3J.subtype).codRestrict j3G j3ToLin_mem

theorem j3JHom_val (g : j3J) :
    ((j3JHom g : j3G) : J3GL) = j3ToLin (g : GL (Fin 80) (ZMod 2)) := rfl

theorem j3JHom_bijective : Function.Bijective j3JHom := by
  refine ⟨fun g h e => ?_, ?_⟩
  · have e' := congrArg Subtype.val e
    rw [j3JHom_val, j3JHom_val] at e'
    exact Subtype.ext (j3ToLin_injective e')
  rintro ⟨h, hh⟩
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact ⟨⟨j3SeedGL k, j3SeedGL_mem k⟩, Subtype.ext (j3SeedLin_eq k).symm⟩
  | one => exact ⟨1, map_one _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a * b, by rw [map_mul, ha, hb]; rfl⟩
  | inv x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨a⁻¹, by rw [map_inv, ha]; rfl⟩

@[expose] def j3JEquivG :
    j3J ≃* j3G := MulEquiv.ofBijective j3JHom j3JHom_bijective

@[expose] def j3MatEquiv : Blueprint.NativeSporadic.J3 ≃* j3J :=
  Blueprint.NativeSporadic.matrixSeedEquiv 2 80 (by norm_num) j3A1 j3A2 det_j3A1 det_j3A2

theorem j3MatEquiv_val (u : Blueprint.NativeSporadic.J3) :
    (((j3MatEquiv u : j3J) : GL (Fin 80) (ZMod 2)) : Matrix (Fin 80) (Fin 80) (ZMod 2)) =
      u.val.val :=
  Blueprint.NativeSporadic.matrixSeedEquiv_val 2 80 _ j3A1 j3A2 _ _ u

@[expose] def j3EquivG :
    Blueprint.NativeSporadic.J3 ≃* j3G := j3MatEquiv.trans j3JEquivG

@[expose] def j3PermHom :
    Blueprint.NativeSporadic.J3 →* Equiv.Perm (Fin 6156) where
  toFun u := j3Rho (j3EquivG u)
  map_one' := by rw [map_one, map_one]
  map_mul' u w := by rw [map_mul, map_mul]

theorem j3PermHom_apply
    (u : Blueprint.NativeSporadic.J3) :
    j3PermHom u = j3Rho (j3EquivG u) := rfl

theorem j3PermHom_injective :
    Function.Injective j3PermHom :=
  j3Rho_injective.comp j3EquivG.injective

theorem j3PermHom_range :
    j3PermHom.range = j3P := by
  rw [← j3Rho_range]
  ext σ
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨j3EquivG.symm g, by simp [j3PermHom]⟩

@[expose] def j3PermEquiv :
    Blueprint.NativeSporadic.J3 ≃* j3P :=
  (MonoidHom.ofInjective j3PermHom_injective).trans (MulEquiv.subgroupCongr j3PermHom_range)

theorem j3PermEquiv_apply
    (u : Blueprint.NativeSporadic.J3) :
    (j3PermEquiv u : Equiv.Perm (Fin 6156)) = j3PermHom u := rfl

@[expose] def j3SeedA :
    Blueprint.NativeSporadic.J3 := j3MatEquiv.symm ⟨j3SeedGL 0, j3SeedGL_mem 0⟩

@[expose] def j3SeedB :
    Blueprint.NativeSporadic.J3 := j3MatEquiv.symm ⟨j3SeedGL 1, j3SeedGL_mem 1⟩

theorem j3SeedA_val : j3SeedA.val.val = j3A1 := by
  rw [← j3MatEquiv_val, j3SeedA, MulEquiv.apply_symm_apply, j3SeedGL_val]
  rfl

theorem j3SeedB_val : j3SeedB.val.val = j3A2 := by
  rw [← j3MatEquiv_val, j3SeedB, MulEquiv.apply_symm_apply, j3SeedGL_val]
  rfl

theorem j3EquivG_seed (k : ℕ) (hk : k < 2) :
    j3EquivG (j3MatEquiv.symm ⟨j3SeedGL k, j3SeedGL_mem k⟩) =
      ⟨j3SeedLin ⟨k, hk⟩, Subgroup.subset_closure ⟨⟨k, hk⟩, rfl⟩⟩ := by
  apply Subtype.ext
  show ((j3JEquivG (j3MatEquiv (j3MatEquiv.symm ⟨j3SeedGL k, j3SeedGL_mem k⟩)) : j3G) :
    J3GL) = j3SeedLin ⟨k, hk⟩
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem j3PermEquiv_seedA :
    (j3PermEquiv j3SeedA : Equiv.Perm (Fin 6156)) = j3Gen 0 := by
  rw [j3PermEquiv_apply, j3PermHom_apply, j3SeedA, j3EquivG_seed 0 (by norm_num)]
  exact j3Rho_seed 0

theorem j3PermEquiv_seedB :
    (j3PermEquiv j3SeedB : Equiv.Perm (Fin 6156)) = j3Gen 1 := by
  rw [j3PermEquiv_apply, j3PermHom_apply, j3SeedB, j3EquivG_seed 1 (by norm_num)]
  exact j3Rho_seed 1

theorem j3Form_permEquiv
    (u : Blueprint.NativeSporadic.J3) (r : Fin 6156) (v : J3V) :
    j3Form ((j3PermEquiv u : Equiv.Perm (Fin 6156)) r) v =
      j3Form r ((u⁻¹ : Blueprint.NativeSporadic.J3).val.val *ᵥ v) := by
  rw [j3PermEquiv_apply, j3PermHom_apply, j3Form_rho, funAct]
  congr 1

theorem FAM_J3_faithful_permutation_action :
    (∀ r < 6156, ∀ r' < 6156, j3Form r = j3Form r' → r = r') ∧
    (∀ (r : Fin 6156) (v : J3V), j3Form r (j3A1⁻¹ *ᵥ v) = j3Form (j3Gen 0 r) v) ∧
    (∀ (r : Fin 6156) (v : J3V), j3Form r (j3A2⁻¹ *ᵥ v) = j3Form (j3Gen 1 r) v) ∧
    (∀ v : J3V, j3InvForm (j3A1⁻¹ *ᵥ v) = j3InvForm v) ∧
    (∀ v : J3V, j3InvForm (j3A2⁻¹ *ᵥ v) = j3InvForm v) ∧
    IsUnit j3B ∧
    (∀ r, j3T r = j3B⁻¹ * polarMatrix (j3Form r)) ∧
    (LinearMap.ker j3CommMap : Set (Matrix (Fin 80) (Fin 80) (ZMod 2))) = {0, 1} ∧
    Module.finrank (ZMod 2) (LinearMap.range j3CommMap) = 6399 ∧
    (∀ (u : Blueprint.NativeSporadic.J3) (r : Fin 6156) (v : J3V),
      j3Form ((j3PermEquiv u : Equiv.Perm (Fin 6156)) r) v =
        j3Form r ((u⁻¹ : Blueprint.NativeSporadic.J3).val.val *ᵥ v)) ∧
    j3SeedA.val.val = j3A1 ∧ j3SeedB.val.val = j3A2 ∧
    (j3PermEquiv j3SeedA : Equiv.Perm (Fin 6156)) = j3Gen 0 ∧
    (j3PermEquiv j3SeedB : Equiv.Perm (Fin 6156)) = j3Gen 1 := by
  have hA : (((j3SeedGL 0)⁻¹ : GL (Fin 80) (ZMod 2)) : Matrix (Fin 80) (Fin 80) (ZMod 2)) =
      j3A1⁻¹ := by
    rw [Matrix.coe_units_inv, j3SeedGL_val, ite_eq_left rfl]
  have hB : (((j3SeedGL 1)⁻¹ : GL (Fin 80) (ZMod 2)) : Matrix (Fin 80) (Fin 80) (ZMod 2)) =
      j3A2⁻¹ := by
    rw [Matrix.coe_units_inv, j3SeedGL_val, ite_eq_right one_ne_zero]
  refine ⟨fun r hr r' hr' h => j3Form_injective hr hr' h, fun r v => ?_, fun r v => ?_,
    fun v => ?_, fun v => ?_, isUnit_j3B, fun _ => rfl, ker_j3CommMap_eq_set,
    finrank_range_j3CommMap, j3Form_permEquiv, j3SeedA_val, j3SeedB_val, j3PermEquiv_seedA,
    j3PermEquiv_seedB⟩
  · rw [← hA]
    exact j3Form_seed_inv (by norm_num) r v
  · rw [← hB]
    exact j3Form_seed_inv (by norm_num) r v
  · rw [← hA]
    exact j3InvForm_seed_inv (by norm_num) v
  · rw [← hB]
    exact j3InvForm_seed_inv (by norm_num) v

end CFSG.Sporadic.Schreier
