
module

public import CFSG.Monster.B.Fischer.Fi22FaithfulBase

public import CFSG.Monster.B.Fischer.Fi22FaithfulCheck
public import CFSG.Certificates.InvariantQuadratic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Fischer

open CFSG.F3.Native CFSG.Monster.B.Fischer.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  Matrix CFSG.Certificates CFSG.Sporadic.Fi22

attribute [local irreducible] fi22Quad

theorem fi22Form_ne
    {a b : ℕ} (ha : a < 3510) (hb : b < a) : fi22Form a ≠ fi22Form b := by
  have h1 := parLt_spec (by norm_num) fi22Faithful_check.1 a ha
  obtain ⟨i, hi, h2⟩ := nat_any_iff.1 (allLt_spec h1 hb)
  obtain ⟨j, hj, h3⟩ := nat_any_iff.1 h2
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h3
  exact fi22Quad_ne (fun k => fi22FormCoeff_lt a k) (fun k => fi22FormCoeff_lt b k)
    (i := ⟨i, hi⟩) (j := ⟨j, hj⟩) h3.1 h3.2

theorem fi22Form_injective
    {r r' : ℕ} (hr : r < 3510) (hr' : r' < 3510)
    (h : fi22Form r = fi22Form r') : r = r' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact fi22Form_ne hr' hlt h.symm
  · exact fi22Form_ne hr hlt h

theorem fi22Form_seed_aux
    {k : ℕ} (hk : k < 2) {A : Array V} (hA : RowsWF A)
    (h : actionOK fi22FormsBytes (fi22ChainGen k) A 4 = true) (r : Fin 3510) (v : Fi22V) :
    fi22Form r v = fi22Form (fi22GenPerm k r) (toMat 77 A *ᵥ v) := by
  simp only [actionOK] at h
  have h' := parLt_spec (by norm_num) h r r.2
  simp only [Bool.and_eq_true] at h'
  have e := pullbackOK_spec hA h'.2 v
  rw [rep_fi22Gen hk r] at e
  rw [fi22Form_eq, fi22Form_eq]
  exact e

theorem fi22Form_seed
    {k : ℕ} (hk : k < 2) (r : Fin 3510) (v : Fi22V) :
    fi22Form r v = fi22Form (fi22GenPerm k r) ((if k = 0 then mA else mB) *ᵥ v) := by
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · rw [ite_eq_left rfl, ← toMat_matA]
    exact fi22Form_seed_aux (by norm_num) rowsWF_matA fi22Faithful_check.2.1 r v
  · rw [ite_eq_right one_ne_zero, ← toMat_matB]
    exact fi22Form_seed_aux (by norm_num) rowsWF_matB fi22Faithful_check.2.2.1 r v

theorem fi22InvForm_seed {k : ℕ} (hk : k < 2) (v : Fi22V) :
    fi22InvForm v = fi22InvForm ((if k = 0 then mA else mB) *ᵥ v) := by
  rw [fi22InvForm_eq]
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · rw [ite_eq_left rfl, ← toMat_matA]
    exact pullbackOK_spec rowsWF_matA fi22Faithful_check.2.2.2.1 v
  · rw [ite_eq_right one_ne_zero, ← toMat_matB]
    exact pullbackOK_spec rowsWF_matB fi22Faithful_check.2.2.2.2.1 v

theorem fi22Form_seed_inv
    {k : ℕ} (hk : k < 2) (r : Fin 3510) (v : Fi22V) :
    fi22Form r ((((fi22SeedGL k)⁻¹ : GL (Fin 77) (ZMod 3)) : Matrix (Fin 77) (Fin 77) (ZMod 3)) *ᵥ
      v) = fi22Form (fi22GenPerm k r) v := by
  rw [fi22Form_seed hk, ← fi22SeedGL_val, seedGL_mulVec_inv]

theorem fi22InvForm_seed_inv
    {k : ℕ} (hk : k < 2) (v : Fi22V) :
    fi22InvForm ((((fi22SeedGL k)⁻¹ : GL (Fin 77) (ZMod 3)) :
      Matrix (Fin 77) (Fin 77) (ZMod 3)) *ᵥ v) = fi22InvForm v := by
  rw [fi22InvForm_seed hk, ← fi22SeedGL_val, seedGL_mulVec_inv]

theorem rowsWF_fi22Bi :
    RowsWF fi22Bi := rowsWF_of_wfM fi22Faithful_check.2.2.2.2.2.1

theorem fi22B_mul_Bi : fi22B * toMat 77 fi22Bi = 1 := by
  rw [fi22B_eq, ← toMat_mul (polarRows_size _ _) (rowsWF_polarRows _ _) rowsWF_fi22Bi,
    ← toMat_idM 77]
  exact toMat_eq_of_eqM fi22Faithful_check.2.2.2.2.2.2.2.1

theorem fi22B_inv :
    fi22B⁻¹ = toMat 77 fi22Bi := Matrix.inv_eq_right_inv fi22B_mul_Bi

theorem isUnit_fi22B_det : IsUnit fi22B.det :=
  IsUnit.of_mul_eq_one (toMat 77 fi22Bi).det (by rw [← det_mul, fi22B_mul_Bi, det_one])

theorem isUnit_fi22B :
    IsUnit fi22B := (Matrix.isUnit_iff_isUnit_det _).2 isUnit_fi22B_det

theorem fi22B_mul_inv :
    fi22B * fi22B⁻¹ = 1 := Matrix.mul_nonsing_inv _ isUnit_fi22B_det

theorem toMat_fi22SepMats {i : ℕ} (hi : i < 6) :
    toMat 77 fi22SepMats[i]! = fi22T fi22CentralizerIdx[i]! := by
  rw [fi22SepMats, getElem!_map_toArray (by rw [fi22CentralizerIdx_length]; exact hi),
    toMat_mul fi22Faithful_check.2.2.2.2.2.2.1 rowsWF_fi22Bi (rowsWF_polarRows _ _),
    toMat_polarRows, fi22T, fi22B_inv, fi22Form, polarMatrix_fi22Quad]
  rfl

theorem fi22_commutant (g : Matrix (Fin 77) (Fin 77) (ZMod 3))
    (hg : ∀ r ∈ fi22CentralizerIdx, g * fi22T r = fi22T r * g) : ∃ c : ZMod 3, g = c • 1 := by
  refine scalar_of_sepOK fi22Faithful_check.2.2.2.2.2.2.2.2 g fun i hi => ?_
  rw [fi22SepMats_size] at hi
  rw [toMat_fi22SepMats hi]
  apply hg
  rw [getElem!_pos fi22CentralizerIdx i (by rw [fi22CentralizerIdx_length]; exact hi)]
  exact List.getElem_mem _

theorem mem_ker_fi22CommMap (M : Matrix (Fin 77) (Fin 77) (ZMod 3)) :
    M ∈ LinearMap.ker fi22CommMap ↔ ∃ c : ZMod 3, M = c • 1 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    refine fi22_commutant M fun r hr => ?_
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hr
    have := congrFun h ⟨t, by simpa [fi22CentralizerIdx] using ht⟩
    simp only [fi22CommMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this
    rw [List.getD_eq_getElem _ _ ht] at this
    exact sub_eq_zero.1 this
  · rintro ⟨c, rfl⟩
    funext t
    simp [fi22CommMap]

theorem ker_fi22CommMap :
    LinearMap.ker fi22CommMap = Submodule.span (ZMod 3) {1} := by
  ext M
  rw [mem_ker_fi22CommMap, Submodule.mem_span_singleton]
  exact ⟨fun ⟨c, h⟩ => ⟨c, h.symm⟩, fun ⟨c, h⟩ => ⟨c, h.symm⟩⟩

theorem ker_fi22CommMap_eq_set :
    (LinearMap.ker fi22CommMap : Set (Matrix (Fin 77) (Fin 77) (ZMod 3))) =
      {0, 1, (2 : ZMod 3) • (1 : Matrix (Fin 77) (Fin 77) (ZMod 3))} := by
  ext M
  rw [SetLike.mem_coe, mem_ker_fi22CommMap]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨c, rfl⟩
    rcases (by decide : ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = 2) c with rfl | rfl | rfl
    · left; exact zero_smul _ _
    · right; left; exact one_smul _ _
    · right; right; rfl
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, (zero_smul _ _).symm⟩
    · exact ⟨1, (one_smul _ _).symm⟩
    · exact ⟨2, rfl⟩

theorem finrank_range_fi22CommMap :
    Module.finrank (ZMod 3) (LinearMap.range fi22CommMap) = 5928 := by
  have h := LinearMap.finrank_range_add_finrank_ker fi22CommMap
  rw [ker_fi22CommMap, finrank_span_singleton one_ne_zero, Module.finrank_matrix,
    Module.finrank_self, Fintype.card_fin] at h
  omega

theorem fi22Bil_seed
    (k : Fin 2) (u w : Fi22V) :
    fi22Bil ((fi22SeedLin k : Fi22V →ₗ[ZMod 3] Fi22V) u)
      ((fi22SeedLin k : Fi22V →ₗ[ZMod 3] Fi22V) w) = fi22Bil u w := by
  have hk : (k : ℕ) < 2 := k.2
  rw [fi22Bil_apply, fi22Bil_apply, fi22SeedLin_apply, fi22SeedLin_apply, ← mulVec_add,
    fi22SeedGL_val, ← fi22InvForm_seed hk, ← fi22InvForm_seed hk, ← fi22InvForm_seed hk]

theorem glPullback_fi22Form
    (k : Fin 2) (r : Fin 3510) :
    glPullback (fi22SeedLin k) (fi22Form r) = fi22Form (fi22GenPerm k r) := by
  funext v
  rw [glPullback_apply, fi22SeedLin_inv_apply, fi22Form_seed_inv k.2]

theorem fi22Seed_mapsTo
    (k : Fin 2) : ∀ q ∈ fi22X, glPullback (fi22SeedLin k) q ∈ fi22X := by
  rintro _ ⟨r, hr, rfl⟩
  refine ⟨fi22GenPerm k ⟨r, hr⟩, (fi22GenPerm k ⟨r, hr⟩).2, ?_⟩
  rw [← glPullback_fi22Form k ⟨r, hr⟩]

theorem fi22TLin_spec :
    ∀ q ∈ fi22S, ∀ u w, fi22Bil u (fi22TLin q w) = fi22Beta q u w := by
  intro q _ u w
  rw [fi22Bil, fi22TLin, Matrix.toBilin'_apply', Matrix.toLin'_apply', Matrix.mulVecLin_apply,
    mulVec_mulVec, ← mul_assoc, fi22B_mul_inv, one_mul, fi22Beta, Matrix.toBilin'_apply']

theorem fi22_centralizer :
    {M : Module.End (ZMod 3) Fi22V | ∀ q ∈ fi22S, M * fi22TLin q = fi22TLin q * M} =
      Set.range fun c : ZMod 3 => c • (LinearMap.id : Fi22V →ₗ[ZMod 3] Fi22V) := by
  ext M
  simp only [Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := fi22_commutant (LinearMap.toMatrix' M) fun r hr => by
      have := congrArg LinearMap.toMatrix' (h (fi22Form r) ⟨r, hr, rfl⟩)
      rwa [LinearMap.toMatrix'_mul, LinearMap.toMatrix'_mul, fi22TLin,
        LinearMap.toMatrix'_toLin'] at this
    refine ⟨c, ?_⟩
    rw [← Matrix.toLin'_toMatrix' M, hc, map_smul, Matrix.toLin'_one]
  · rintro ⟨c, rfl⟩ q _
    rw [smul_mul_assoc, mul_smul_comm, ← Module.End.one_eq_id, one_mul, mul_one]

theorem fi22Bil_nondegenerate : fi22Bil.Nondegenerate :=
  LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.2 isUnit_fi22B_det.ne_zero

theorem fi22_faithful :
    (∀ g ∈ fi22G, ∀ q ∈ fi22X, glPullback g q ∈ fi22X) ∧
    ∀ hX : ∀ g ∈ fi22G, ∀ q ∈ fi22X, glPullback g q ∈ fi22X,
      Function.Injective (pullbackPerm fi22G fi22X hX) ∧
      (pullbackPerm fi22G fi22X hX).range = Subgroup.closure (Set.range fun i =>
        pullbackPerm fi22G fi22X hX ⟨fi22SeedLin i, Subgroup.subset_closure ⟨i, rfl⟩⟩) :=
  invariant_quadratic_determinant_faithful_action fi22_hroot fi22Bil fi22Bil_nondegenerate fi22X
    fi22X_finite fi22Beta (fun _ hq u w => fi22Beta_apply hq u w) fi22SeedLin det_fi22SeedLin
    fi22Bil_seed fi22Seed_mapsTo fi22S fi22S_subset fi22TLin fi22TLin_spec fi22_centralizer

theorem fi22G_mapsTo :

    ∀ g ∈ fi22G, ∀ q ∈ fi22X, glPullback g q ∈ fi22X := fi22_faithful.1

@[expose] noncomputable def fi22XEquiv : Fin 3510 ≃ fi22X :=
  Equiv.ofBijective (fun r => ⟨fi22Form r, (r : ℕ), r.2, rfl⟩)
    ⟨fun r r' h => Fin.ext (fi22Form_injective r.2 r'.2 (congrArg Subtype.val h)),
      fun ⟨_, r, hr, hq⟩ => ⟨⟨r, hr⟩, Subtype.ext hq⟩⟩

theorem fi22XEquiv_apply
    (r : Fin 3510) : (fi22XEquiv r : Fi22V → ZMod 3) = fi22Form r := rfl

@[expose] noncomputable def fi22Rho :
    fi22G →* Equiv.Perm (Fin 3510) :=
  fi22XEquiv.symm.permCongrHom.toMonoidHom.comp (pullbackPerm fi22G fi22X fi22G_mapsTo)

theorem fi22XEquiv_rho
    (g : fi22G) (r : Fin 3510) :
    fi22XEquiv (fi22Rho g r) = pullbackPerm fi22G fi22X fi22G_mapsTo g (fi22XEquiv r) := by
  change fi22XEquiv (fi22XEquiv.symm (pullbackPerm fi22G fi22X fi22G_mapsTo g
    (fi22XEquiv.symm.symm r))) = _
  rw [Equiv.apply_symm_apply, Equiv.symm_symm]

theorem fi22Form_rho
    (g : fi22G) (r : Fin 3510) :
    fi22Form (fi22Rho g r) = glPullback g (fi22Form r) := by
  have h := congrArg Subtype.val (fi22XEquiv_rho g r)
  rw [fi22XEquiv_apply, pullbackPerm_apply, fi22XEquiv_apply] at h
  exact h

theorem fi22Rho_injective :
    Function.Injective fi22Rho :=
  fi22XEquiv.symm.permCongrHom.injective.comp (fi22_faithful.2 fi22G_mapsTo).1

theorem fi22Rho_seed
    (k : Fin 2) :
    fi22Rho ⟨fi22SeedLin k, Subgroup.subset_closure ⟨k, rfl⟩⟩ = fi22GenPerm k := by
  refine Equiv.ext fun r => Fin.ext (fi22Form_injective (Fin.isLt _) (Fin.isLt _) ?_)
  rw [fi22Form_rho]
  exact glPullback_fi22Form k r

theorem fi22Rho_range :
    fi22Rho.range = fi22P := by
  rw [fi22Rho, MonoidHom.range_comp, (fi22_faithful.2 fi22G_mapsTo).2, MonoidHom.map_closure,
    fi22P_eq]
  congr 1
  ext σ
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨k, (fi22Rho_seed k).symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨_, ⟨k, rfl⟩, fi22Rho_seed k⟩

@[expose] noncomputable def fi22PermHom :
    Blueprint.NativeSporadic.Fi22 →* Equiv.Perm (Fin 3510)
    where
  toFun u := fi22Rho (fi22EquivG u)
  map_one' := by rw [map_one, map_one]
  map_mul' u w := by rw [map_mul, map_mul]

theorem fi22PermHom_apply
    (u : Blueprint.NativeSporadic.Fi22) :
    fi22PermHom u = fi22Rho (fi22EquivG u) := rfl

theorem fi22PermHom_injective :
    Function.Injective fi22PermHom :=
  fi22Rho_injective.comp fi22EquivG.injective

theorem fi22PermHom_range :
    fi22PermHom.range = fi22P := by
  rw [← fi22Rho_range]
  ext σ
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨fi22EquivG.symm g, by simp [fi22PermHom]⟩

@[expose] noncomputable def fi22PermEquiv :
    Blueprint.NativeSporadic.Fi22 ≃* fi22P :=
  (MonoidHom.ofInjective fi22PermHom_injective).trans (MulEquiv.subgroupCongr fi22PermHom_range)

theorem fi22PermEquiv_apply
    (u : Blueprint.NativeSporadic.Fi22) :
    (fi22PermEquiv u : Equiv.Perm (Fin 3510)) = fi22PermHom u := rfl

theorem fi22PermEquiv_seedA :
    (fi22PermEquiv fi22SeedA : Equiv.Perm (Fin 3510)) = fi22GenPerm 0 := by
  rw [fi22PermEquiv_apply, fi22PermHom_apply, fi22EquivG_seedA]
  exact fi22Rho_seed 0

theorem fi22PermEquiv_seedB :
    (fi22PermEquiv fi22SeedB : Equiv.Perm (Fin 3510)) = fi22GenPerm 1 := by
  rw [fi22PermEquiv_apply, fi22PermHom_apply, fi22EquivG_seedB]
  exact fi22Rho_seed 1

theorem fi22Form_permEquiv
    (u : Blueprint.NativeSporadic.Fi22) (r : Fin 3510) (v : Fi22V) :
    fi22Form ((fi22PermEquiv u : Equiv.Perm (Fin 3510)) r) v =
      fi22Form r ((u⁻¹ : Blueprint.NativeSporadic.Fi22).val.val *ᵥ v) := by
  rw [fi22PermEquiv_apply, fi22PermHom_apply, fi22Form_rho, glPullback_apply]
  congr 1

theorem Fi22_faithful_permutation_action :
    (∀ r < 3510, ∀ r' < 3510, fi22Form r = fi22Form r' → r = r') ∧
    (∀ (r : Fin 3510) (v : Fi22V), fi22Form r (mA⁻¹ *ᵥ v) = fi22Form (fi22GenPerm 0 r) v) ∧
    (∀ (r : Fin 3510) (v : Fi22V), fi22Form r (mB⁻¹ *ᵥ v) = fi22Form (fi22GenPerm 1 r) v) ∧
    (∀ v : Fi22V, fi22InvForm (mA⁻¹ *ᵥ v) = fi22InvForm v) ∧
    (∀ v : Fi22V, fi22InvForm (mB⁻¹ *ᵥ v) = fi22InvForm v) ∧
    IsUnit fi22B ∧ (∀ r, fi22T r = fi22B⁻¹ * polarMatrix (fi22Form r)) ∧
    (LinearMap.ker fi22CommMap : Set (Matrix (Fin 77) (Fin 77) (ZMod 3))) =
      {0, 1, (2 : ZMod 3) • (1 : Matrix (Fin 77) (Fin 77) (ZMod 3))} ∧
    Module.finrank (ZMod 3) (LinearMap.range fi22CommMap) = 5928 ∧
    (∀ (u : Blueprint.NativeSporadic.Fi22) (r : Fin 3510) (v : Fi22V),
      fi22Form ((fi22PermEquiv u : Equiv.Perm (Fin 3510)) r) v =
        fi22Form r ((u⁻¹ : Blueprint.NativeSporadic.Fi22).val.val *ᵥ v)) ∧
    fi22SeedA.val.val = mA ∧ fi22SeedB.val.val = mB ∧
    (fi22PermEquiv fi22SeedA : Equiv.Perm (Fin 3510)) = fi22GenPerm 0 ∧
    (fi22PermEquiv fi22SeedB : Equiv.Perm (Fin 3510)) = fi22GenPerm 1 := by
  have hA : (((fi22SeedGL 0)⁻¹ : GL (Fin 77) (ZMod 3)) : Matrix (Fin 77) (Fin 77) (ZMod 3)) =
      mA⁻¹ := by
    rw [Matrix.coe_units_inv]
    rfl
  have hB : (((fi22SeedGL 1)⁻¹ : GL (Fin 77) (ZMod 3)) : Matrix (Fin 77) (Fin 77) (ZMod 3)) =
      mB⁻¹ := by
    rw [Matrix.coe_units_inv]
    rfl
  refine ⟨fun r hr r' hr' h => fi22Form_injective hr hr' h, fun r v => ?_, fun r v => ?_,
    fun v => ?_, fun v => ?_, isUnit_fi22B, fun _ => rfl, ker_fi22CommMap_eq_set,
    finrank_range_fi22CommMap, fi22Form_permEquiv, fi22SeedA_val, fi22SeedB_val,
    fi22PermEquiv_seedA, fi22PermEquiv_seedB⟩
  · rw [← hA]
    exact fi22Form_seed_inv (by norm_num) r v
  · rw [← hB]
    exact fi22Form_seed_inv (by norm_num) r v
  · rw [← hA]
    exact fi22InvForm_seed_inv (by norm_num) v
  · rw [← hB]
    exact fi22InvForm_seed_inv (by norm_num) v

end CFSG.Monster.B.Fischer
