module

public import CFSG.Sporadic.Schreier.J1CertCheck
public import CFSG.Sporadic.Schreier.J1VecCheck
public import CFSG.Sporadic.J1.Setup

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Blueprint CFSG.ProperTwoGeneratedCore CFSG.Monster.B.Mathieu CFSG.Monster.B.Co2
open CFSG.Sporadic.J1 Matrix
open scoped Pointwise

theorem j1_cert_vectors_length :
    J1Certificate.vectors.length = 3080 :=
  j1Certificate_shapeFacts.2.2.2.2.1

theorem j1_cert_vectors_shape :
    ∀ v ∈ J1Certificate.vectors, v.length = 7 ∧ ∀ e ∈ v, e ≤ 10 :=
  j1Certificate_shapeFacts.2.2.2.2.2.1

theorem j1_cert_generators_length :
    J1Certificate.chain.generators.length = 2 :=
  j1Certificate_shapeFacts.2.2.2.2.2.2.2.2.1

theorem j1_cert_perms :
    ∀ a ∈ J1Certificate.chain.generators ++ J1Certificate.chain.strongGenerators,
      isPermList 3080 a = true :=
  j1Certificate_shapeFacts.2.2.2.2.2.2.2.2.2.1

theorem isPermList_j1A1List : isPermList 3080 j1A1List = true := by
  refine j1_cert_perms _ (List.mem_append_left _ ?_)
  rw [j1A1List, List.getD_eq_getElem _ _ (by rw [j1_cert_generators_length]; norm_num)]
  exact List.getElem_mem _

theorem isPermList_j1A2List : isPermList 3080 j1A2List = true := by
  refine j1_cert_perms _ (List.mem_append_left _ ?_)
  rw [j1A2List, List.getD_eq_getElem _ _ (by rw [j1_cert_generators_length]; norm_num)]
  exact List.getElem_mem _

theorem arrPerm_val {n : ℕ} {l : List ℕ} (hl : isPermList n l = true) (i : Fin n) :
    (arrPerm n l i : ℕ) = l.getD i 0 := by
  simp only [isPermList, Bool.and_eq_true, beq_iff_eq] at hl
  have h : l.toArray[(i : ℕ)]! = (permOfArr n l.toArray i : ℕ) := (rep_permOfArr hl.2).1 i
  have hi : (i : ℕ) < l.length := by
    rw [hl.1]
    exact i.isLt
  rw [getElem!_pos l.toArray (i : ℕ) (by simpa using hi), List.getElem_toArray] at h
  rw [List.getD_eq_getElem _ _ hi, h]
  rfl

theorem j1Idx_eq {l : List ℕ} (hl : isPermList 3080 l = true) (i : Fin 3080) :
    j1Idx l i = arrPerm 3080 l i := by
  apply Fin.ext
  change l.getD i 0 % 3080 = _
  rw [arrPerm_val hl, Nat.mod_eq_of_lt (by rw [← arrPerm_val hl]; exact (arrPerm 3080 l i).isLt)]

theorem j1Idx_A1 (i : Fin 3080) : j1Idx j1A1List i = j1A1 i := by
  rw [j1A1]
  exact j1Idx_eq isPermList_j1A1List i

theorem j1Idx_A2 (i : Fin 3080) : j1Idx j1A2List i = j1A2 i := by
  rw [j1A2]
  exact j1Idx_eq isPermList_j1A2List i

theorem j1Vec_injective :
    Function.Injective j1Vec := by
  intro i j h
  have hi : (i : ℕ) < J1Certificate.vectors.length := by rw [j1_cert_vectors_length]; exact i.2
  have hj : (j : ℕ) < J1Certificate.vectors.length := by rw [j1_cert_vectors_length]; exact j.2
  have hu := j1_cert_vectors_shape _ (List.getElem_mem hi)
  have hw := j1_cert_vectors_shape _ (List.getElem_mem hj)
  have hlist : J1Certificate.vectors[(i : ℕ)] = J1Certificate.vectors[(j : ℕ)] := by
    apply List.ext_getElem (hu.1.trans hw.1.symm)
    intro k hk1 hk2
    have hk : k < 7 := hu.1 ▸ hk1
    have hc := congrFun h ⟨k, hk⟩
    simp only [j1Vec, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj,
      List.getD_eq_getElem _ _ hk1, List.getD_eq_getElem _ _ hk2] at hc
    rw [ZMod.natCast_eq_natCast_iff'] at hc
    rwa [Nat.mod_eq_of_lt (Nat.lt_succ_of_le (hu.2 _ (List.getElem_mem hk1))),
      Nat.mod_eq_of_lt (Nat.lt_succ_of_le (hw.2 _ (List.getElem_mem hk2)))] at hc
  exact Fin.ext ((List.Nodup.getElem_inj_iff j1_vectors_nodup).1 hlist)

@[expose] def j1BasisVec (c : Fin 7) : Fin 7 → ZMod 11 := j1Vec (Fin.castLE (by norm_num) c)

theorem j1BasisMat_col : j1BasisMat.col = j1BasisVec := by
  funext c r
  rfl

theorem j1BasisVec_linearIndependent :
    LinearIndependent (ZMod 11) j1BasisVec := by
  have hu : IsUnit j1BasisMat :=
    (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse j1BasisMat_mul_inv)
  rw [← j1BasisMat_col]
  exact Matrix.linearIndependent_cols_of_isUnit hu

theorem j1BasisVec_span :
    Submodule.span (ZMod 11) (Set.range j1BasisVec) = ⊤ := by
  rw [← j1BasisMat_col, ← Matrix.range_mulVecLin, LinearMap.range_eq_top]
  intro w
  refine ⟨j1BasisInv *ᵥ w, ?_⟩
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, j1BasisMat_mul_inv, Matrix.one_mulVec]

abbrev j1X : Set (Fin 7 → ZMod 11) := Set.range j1Vec

theorem j1X_finite : j1X.Finite := Set.finite_range _

theorem j1X_span : Submodule.span (ZMod 11) j1X = ⊤ := by
  refine eq_top_iff.2 (j1BasisVec_span.symm.le.trans (Submodule.span_mono ?_))
  rintro _ ⟨c, rfl⟩
  exact ⟨_, rfl⟩

@[expose] noncomputable def glLin :
    GL (Fin 7) (ZMod 11) ≃* ((Fin 7 → ZMod 11) ≃ₗ[ZMod 11] (Fin 7 → ZMod 11)) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _)

theorem glLin_apply (g : GL (Fin 7) (ZMod 11)) (v : Fin 7 → ZMod 11) :
    glLin g v = (g : Matrix (Fin 7) (Fin 7) (ZMod 11)) *ᵥ v := by
  simp only [glLin, MulEquiv.trans_apply, LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv,
    Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply]

abbrev j1Stab : Subgroup ((Fin 7 → ZMod 11) ≃ₗ[ZMod 11] (Fin 7 → ZMod 11)) :=
  MulAction.stabilizer ((Fin 7 → ZMod 11) ≃ₗ[ZMod 11] (Fin 7 → ZMod 11)) j1X

theorem glLin_first_mem : glLin j1_first_unit ∈ j1Stab := by
  refine (MulAction.mem_stabilizer_set' j1X_finite).2 ?_
  rintro _ ⟨i, rfl⟩
  refine ⟨j1Idx j1A1List i, ?_⟩
  change j1Vec (j1Idx j1A1List i) = glLin j1_first_unit (j1Vec i)
  rw [glLin_apply]
  exact (j1_first_mulVec i).symm

theorem glLin_second_mem : glLin j1_second_unit ∈ j1Stab := by
  refine (MulAction.mem_stabilizer_set' j1X_finite).2 ?_
  rintro _ ⟨i, rfl⟩
  refine ⟨j1Idx j1A2List i, ?_⟩
  change j1Vec (j1Idx j1A2List i) = glLin j1_second_unit (j1Vec i)
  rw [glLin_apply]
  exact (j1_second_mulVec i).symm

theorem glLin_mem_stab (g : J) : glLin g ∈ j1Stab := by
  have h : J.map glLin.toMonoidHom ≤ j1Stab := by
    rw [MonoidHom.map_closure, Subgroup.closure_le, Set.image_pair]
    rintro _ (rfl | rfl)
    · exact glLin_first_mem
    · exact glLin_second_mem
  exact h ⟨g, g.2, rfl⟩

@[expose] noncomputable def toStab : J →* j1Stab :=
  (glLin.toMonoidHom.comp J.subtype).codRestrict j1Stab glLin_mem_stab

theorem toStab_injective :
    Function.Injective toStab := fun _ _ hgh =>
  Subtype.ext (glLin.injective (congrArg Subtype.val hgh))

@[expose] noncomputable def j1Restr : j1Stab →* Equiv.Perm j1X := MulAction.toPermHom _ _

theorem j1Restr_apply (g : j1Stab) (x : j1X) :
    ((j1Restr g x : j1X) : Fin 7 → ZMod 11) =
      (g : (Fin 7 → ZMod 11) ≃ₗ[ZMod 11] (Fin 7 → ZMod 11)) x := rfl

theorem j1Restr_injective : Function.Injective j1Restr := by
  intro f g h
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext_on j1X_span
  intro x hx
  exact congrArg (fun e : Equiv.Perm j1X => (e ⟨x, hx⟩ : Fin 7 → ZMod 11)) h

@[expose] noncomputable def j1XEquiv :
    j1X ≃ Fin 3080 :=
  (Equiv.ofInjective j1Vec j1Vec_injective).symm

@[expose] noncomputable def j1Rho :
    J →* Equiv.Perm (Fin 3080) :=
  (Equiv.permCongrHom j1XEquiv).toMonoidHom.comp (j1Restr.comp toStab)

theorem j1Vec_rho
    (g : J) (i : Fin 3080) : j1Vec (j1Rho g i) = mat g *ᵥ j1Vec i := by
  change j1Vec (j1XEquiv (j1Restr (toStab g) (j1XEquiv.symm i))) = _
  rw [j1XEquiv, Equiv.apply_ofInjective_symm j1Vec_injective, j1Restr_apply, Equiv.symm_symm,
    Equiv.ofInjective_apply]
  exact glLin_apply g (j1Vec i)

theorem j1Rho_injective :
    Function.Injective j1Rho :=
  (Equiv.permCongrHom j1XEquiv).injective.comp (j1Restr_injective.comp toStab_injective)

theorem j1Rho_a : j1Rho a = j1A1 := by
  refine Equiv.ext fun i => j1Vec_injective ?_
  rw [j1Vec_rho, mat_a, j1_first_mulVec, j1Idx_A1]

theorem j1Rho_b : j1Rho b = j1A2 := by
  refine Equiv.ext fun i => j1Vec_injective ?_
  rw [j1Vec_rho, mat_b, j1_second_mulVec, j1Idx_A2]

theorem range_j1Rho :
    j1Rho.range = j1P := by
  rw [MonoidHom.range_eq_map, ← closure_ab, MonoidHom.map_closure, Set.image_pair, j1Rho_a,
    j1Rho_b]
  rfl

@[expose] def j1Mat (g : NativeSporadic.J1) : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  ((g : NativeSporadic.seedMonoid 11 7 3 NativeSporadic.J1Seed1 NativeSporadic.J1Seed2) :
    Matrix (Fin 7) (Fin 7) (ZMod 11))

theorem seed_closure_eq :
    NativeSporadic.seedMonoid 11 7 3 NativeSporadic.J1Seed1 NativeSporadic.J1Seed2 =
      Submonoid.closure ({(j1_first_unit : Matrix (Fin 7) (Fin 7) (ZMod 11)),
        (j1_second_unit : Matrix (Fin 7) (Fin 7) (ZMod 11))} : Set _) := by
  rw [j1_seed_monoid_eq]
  rfl

@[expose] noncomputable def j1SeedEquiv : NativeSporadic.J1 ≃* J :=
  (Units.mapEquiv (MulEquiv.submonoidCongr seed_closure_eq)).trans
    (NativeSporadic.unitSeedEquiv j1_first_unit j1_second_unit)

theorem mat_j1SeedEquiv (g : NativeSporadic.J1) : mat (j1SeedEquiv g) = j1Mat g := rfl

@[expose] noncomputable def j1PermEquiv :
    NativeSporadic.J1 ≃* j1P :=
  j1SeedEquiv.trans ((MonoidHom.ofInjective j1Rho_injective).trans
    (MulEquiv.subgroupCongr range_j1Rho))

theorem j1PermEquiv_apply
    (g : NativeSporadic.J1) :
    (j1PermEquiv g : Equiv.Perm (Fin 3080)) = j1Rho (j1SeedEquiv g) := rfl

theorem fam_j1_faithful_permutation_action :
    Function.Injective j1Vec ∧ (∀ i, j1Vec i ≠ 0) ∧
      LinearIndependent (ZMod 11) j1BasisVec ∧
      Submodule.span (ZMod 11) (Set.range j1BasisVec) = ⊤ ∧
      (∀ i, NativeSporadic.decode 11 7 3 NativeSporadic.J1Seed1 *ᵥ j1Vec i = j1Vec (j1A1 i)) ∧
      (∀ i, NativeSporadic.decode 11 7 3 NativeSporadic.J1Seed2 *ᵥ j1Vec i = j1Vec (j1A2 i)) ∧
      ∃ φ : NativeSporadic.J1 ≃* j1P,
        (∀ (g : NativeSporadic.J1) (i : Fin 3080),
          j1Mat g *ᵥ j1Vec i = j1Vec ((φ g : Equiv.Perm (Fin 3080)) i)) ∧
        (∃ s : NativeSporadic.J1, j1Mat s = NativeSporadic.decode 11 7 3 NativeSporadic.J1Seed1 ∧
          (φ s : Equiv.Perm (Fin 3080)) = j1A1) ∧
        (∃ s : NativeSporadic.J1, j1Mat s = NativeSporadic.decode 11 7 3 NativeSporadic.J1Seed2 ∧
          (φ s : Equiv.Perm (Fin 3080)) = j1A2) := by
  refine ⟨j1Vec_injective, j1Vec_ne_zero, j1BasisVec_linearIndependent, j1BasisVec_span,
    fun i => ?_, fun i => ?_, j1PermEquiv, fun g i => ?_, ⟨j1SeedEquiv.symm a, ?_, ?_⟩,
    ⟨j1SeedEquiv.symm b, ?_, ?_⟩⟩
  · rw [j1_first_decode_eq, j1_first_mulVec, j1Idx_A1]
  · rw [j1_second_decode_eq, j1_second_mulVec, j1Idx_A2]
  · rw [j1PermEquiv_apply, j1Vec_rho, mat_j1SeedEquiv]
  · rw [← mat_j1SeedEquiv, MulEquiv.apply_symm_apply, mat_a, j1_first_decode_eq]
  · rw [j1PermEquiv_apply, MulEquiv.apply_symm_apply, j1Rho_a]
  · rw [← mat_j1SeedEquiv, MulEquiv.apply_symm_apply, mat_b, j1_second_decode_eq]
  · rw [j1PermEquiv_apply, MulEquiv.apply_symm_apply, j1Rho_b]

end CFSG.Sporadic.Schreier
