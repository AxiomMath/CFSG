
module

public import CFSG.Sporadic.Co2Cert.FaithfulBase
import all CFSG.Sporadic.Co2Cert.FaithfulBase

public import CFSG.Sporadic.Co2Cert.FaithfulCheck
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Certificates.SpanningLinearAction
import all CFSG.Blueprint.NativeSporadic

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Cert

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu
  CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
open scoped Matrix

theorem co2A1_sq : co2A1 * co2A1 = 1 := by
  have h := congrArg (rowsMatrix 22) co2Faithful_check.2.2.2.2.2.2.1
  rwa [rowsMatrix_mulRows, rowsMatrix_idRows, rowsMatrix_co2RowsA] at h

theorem co2A2_pow : co2A2 ^ 5 = 1 := by
  have h := congrArg (rowsMatrix 22) co2Faithful_check.2.2.2.2.2.2.2
  rwa [rowsMatrix_powRows, rowsMatrix_idRows, rowsMatrix_co2RowsB] at h

theorem det_co2A1_ne_zero : co2A1.det ≠ 0 := by
  intro h
  have := congrArg Matrix.det co2A1_sq
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem det_co2A2_ne_zero : co2A2.det ≠ 0 := by
  intro h
  have := congrArg Matrix.det co2A2_pow
  rw [Matrix.det_pow, h, zero_pow (by norm_num), Matrix.det_one] at this
  exact zero_ne_one this

theorem co2Packed_facts {i : ℕ} (hi : i < 2300) :
    co2PackedVecs[i]! < 2 ^ 22 ∧ co2PackedVecs[i]! ≠ 0 ∧
      ∀ j < 2300, co2PackedVecs[i]! = co2PackedVecs[j]! → i = j :=
  co2Faithful_check.2.1 i hi

theorem co2Vec_ne_zero
    {i : ℕ} (hi : i < 2300) : co2Vec i ≠ 0 := by
  intro h
  rw [co2Vec_eq hi, ← toVecD_zero 22] at h
  exact (co2Packed_facts hi).2.1 (toVecD_injective (co2Packed_facts hi).1 (by norm_num) h)

theorem co2Vec_injective
    {i j : ℕ} (hi : i < 2300) (hj : j < 2300)
    (h : co2Vec i = co2Vec j) : i = j := by
  rw [co2Vec_eq hi, co2Vec_eq hj] at h
  exact (co2Packed_facts hi).2.2 j hj (toVecD_injective (co2Packed_facts hi).1 (co2Packed_facts hj).1 h)

theorem rowsMatrix_co2BasisRows_row
    (t : Fin 22) :
    (rowsMatrix 22 co2BasisRows).row t = co2Vec (co2BasisList.getD t 0) := by
  funext j
  have hs : (t : ℕ) < co2BasisRows.size := by rw [co2Faithful_check.2.2.1]; exact t.2
  rw [Matrix.row_apply, rowsMatrix_apply, co2Vec_eq (co2BasisList_lt t t.2),
    ← co2BasisRows_get t.2, Array.getElem?_eq_getElem hs, Option.getD_some,
    getElem!_pos co2BasisRows (t : ℕ) hs]

theorem co2Basis_isUnit : IsUnit (rowsMatrix 22 co2BasisRows) := by
  have h := congrArg (rowsMatrix 22) co2Faithful_check.2.2.2.1
  rw [rowsMatrix_mulRows, rowsMatrix_idRows] at h
  exact IsUnit.of_mul_eq_one_right _ h

theorem co2Basis_linearIndependent :
    LinearIndependent (ZMod 2) fun t : Fin 22 => co2Vec (co2BasisList.getD t 0) := by
  have h := Matrix.linearIndependent_rows_iff_isUnit.2 co2Basis_isUnit
  have e : (rowsMatrix 22 co2BasisRows).row = fun t : Fin 22 => co2Vec (co2BasisList.getD t 0) :=
    funext rowsMatrix_co2BasisRows_row
  rwa [e] at h

theorem co2Basis_span :
    Submodule.span (ZMod 2) (Set.range fun t : Fin 22 => co2Vec (co2BasisList.getD t 0)) = ⊤ :=
  co2Basis_linearIndependent.span_eq_top_of_card_eq_finrank (by simp)

theorem co2X_span :
    Submodule.span (ZMod 2) co2X = ⊤ := by
  rw [eq_top_iff, ← co2Basis_span]
  apply Submodule.span_mono
  rintro _ ⟨t, rfl⟩
  exact ⟨_, co2BasisList_lt t t.2, rfl⟩

theorem co2A1_mulVec
    (i : Fin 2300) : co2A1 *ᵥ co2Vec i = co2Vec (co2Gen 0 i) := by
  rw [co2Vec_eq i.2, ← rowsMatrix_co2RowsA, rowsMatrix_mulVec, co2Faithful_check.2.2.2.2.1 i i.2,
    rep_co2Gen (k := 0) (by norm_num) i, ← co2Vec_eq (co2Gen 0 i).2]

theorem co2A2_mulVec
    (i : Fin 2300) : co2A2 *ᵥ co2Vec i = co2Vec (co2Gen 1 i) := by
  rw [co2Vec_eq i.2, ← rowsMatrix_co2RowsB, rowsMatrix_mulVec,
    co2Faithful_check.2.2.2.2.2.1 i i.2, rep_co2Gen (k := 1) (by norm_num) i,
    ← co2Vec_eq (co2Gen 1 i).2]

@[expose] noncomputable def co2GL1 : GL (Fin 22) (ZMod 2) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero co2A1 det_co2A1_ne_zero

@[expose] noncomputable def co2GL2 : GL (Fin 22) (ZMod 2) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero co2A2 det_co2A2_ne_zero

abbrev co2J :
    Subgroup (GL (Fin 22) (ZMod 2)) := Subgroup.closure {co2GL1, co2GL2}

@[expose] noncomputable def co2MatEquiv :
    Blueprint.NativeSporadic.Co2 ≃* co2J :=
  Blueprint.NativeSporadic.matrixSeedEquiv 2 22 (by norm_num) co2A1 co2A2 det_co2A1_ne_zero
    det_co2A2_ne_zero

theorem co2MatEquiv_val (u : Blueprint.NativeSporadic.Co2) :
    (((co2MatEquiv u : co2J) : GL (Fin 22) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2)) =
      u.val.val :=
  Blueprint.NativeSporadic.matrixSeedEquiv_val 2 22 _ co2A1 co2A2 _ _ u

@[expose] noncomputable def co2SeedGL
    (k : Fin 2) : GL (Fin 22) (ZMod 2) :=
  if k = 0 then co2GL1 else co2GL2

@[expose] noncomputable def co2SeedLin
    (k : Fin 2) : Co2V ≃ₗ[ZMod 2] Co2V := co2GLLin (co2SeedGL k)

@[expose] noncomputable def co2G : Subgroup (Co2V ≃ₗ[ZMod 2] Co2V) :=
  Subgroup.closure (Set.range co2SeedLin)

theorem co2SeedLin_apply
    (k : Fin 2) (i : Fin 2300) :
    co2SeedLin k (co2Vec i) = co2Vec (co2Gen k i) := by
  have h1 : ((co2GL1 : GL (Fin 22) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2)) = co2A1 := rfl
  have h2 : ((co2GL2 : GL (Fin 22) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2)) = co2A2 := rfl
  have e0 : co2SeedGL 0 = co2GL1 := ite_eq_left rfl
  have e1 : co2SeedGL 1 = co2GL2 := ite_eq_right (by decide)
  have v0 : ((0 : Fin 2) : ℕ) = 0 := rfl
  have v1 : ((1 : Fin 2) : ℕ) = 1 := rfl
  revert k
  rw [Fin.forall_fin_two]
  refine ⟨?_, ?_⟩
  · rw [co2SeedLin, co2GLLin_apply, e0, h1, v0]
    exact co2A1_mulVec i
  · rw [co2SeedLin, co2GLLin_apply, e1, h2, v1]
    exact co2A2_mulVec i

theorem co2Seed_mapsTo
    (k : Fin 2) : Set.MapsTo (co2SeedLin k) co2X co2X := by
  rintro _ ⟨i, hi, rfl⟩
  refine ⟨co2Gen k ⟨i, hi⟩, (co2Gen k ⟨i, hi⟩).2, ?_⟩
  rw [co2SeedLin_apply k ⟨i, hi⟩]

theorem co2J_map : co2J.map co2GLLinHom = co2G := by
  rw [MonoidHom.map_closure, co2G]
  congr 1
  ext f
  simp only [Set.image_insert_eq, Set.image_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff, Set.mem_range, co2GLLinHom_apply]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · rintro ⟨k, rfl⟩
    fin_cases k
    · left; rfl
    · right; rfl

@[expose] noncomputable def co2JEquivG : co2J ≃* co2G :=
  (co2J.equivMapOfInjective co2GLLinHom co2GLLinHom_injective).trans
    (MulEquiv.subgroupCongr co2J_map)

theorem co2JEquivG_val (g : co2J) :
    ((co2JEquivG g : co2G) : Co2V ≃ₗ[ZMod 2] Co2V) = co2GLLin (g : GL (Fin 22) (ZMod 2)) := rfl

@[expose] noncomputable def co2Restr :
    co2G →* Equiv.Perm co2X :=
  generatedLinearRestriction co2X co2X_finite co2SeedLin co2Seed_mapsTo

theorem co2Restr_apply
    (g : co2G) (x : co2X) :
    ((co2Restr g x : co2X) : Co2V) = (g : Co2V ≃ₗ[ZMod 2] Co2V) (x : Co2V) := rfl

theorem co2Restr_range :
    co2Restr.range = Subgroup.closure (Set.range fun k : Fin 2 =>
    co2Restr ⟨co2SeedLin k, Subgroup.subset_closure ⟨k, rfl⟩⟩) :=
  generatedLinearRestriction_range co2X co2X_finite co2SeedLin co2Seed_mapsTo

theorem co2Restr_injective :
    Function.Injective co2Restr :=
  (linearSetRestriction_injective co2X co2X_span).comp (Subgroup.inclusion_injective _)

@[expose] noncomputable def co2XEquiv :
    Fin 2300 ≃ co2X :=
  Equiv.ofBijective (fun i => ⟨co2Vec i, (i : ℕ), i.2, rfl⟩)
    ⟨fun i j h => Fin.ext (co2Vec_injective i.2 j.2 (congrArg Subtype.val h)),
      fun ⟨_, i, hi, hv⟩ => ⟨⟨i, hi⟩, Subtype.ext hv⟩⟩

theorem co2XEquiv_apply
    (i : Fin 2300) : (co2XEquiv i : Co2V) = co2Vec i := rfl

@[expose] noncomputable def co2Rho :
    co2G →* Equiv.Perm (Fin 2300) :=
  co2XEquiv.symm.permCongrHom.toMonoidHom.comp co2Restr

theorem co2XEquiv_rho
    (g : co2G) (i : Fin 2300) :
    co2XEquiv (co2Rho g i) = co2Restr g (co2XEquiv i) := by
  change co2XEquiv (co2XEquiv.symm (co2Restr g (co2XEquiv.symm.symm i))) = _
  rw [Equiv.apply_symm_apply, Equiv.symm_symm]

theorem co2Vec_rho
    (g : co2G) (i : Fin 2300) :
    co2Vec (co2Rho g i) = (g : Co2V ≃ₗ[ZMod 2] Co2V) (co2Vec i) := by
  have h := congrArg Subtype.val (co2XEquiv_rho g i)
  rw [co2XEquiv_apply, co2Restr_apply, co2XEquiv_apply] at h
  exact h

theorem co2Rho_injective :
    Function.Injective co2Rho :=
  co2XEquiv.symm.permCongrHom.injective.comp co2Restr_injective

theorem co2Rho_seed (k : Fin 2) :
    co2Rho ⟨co2SeedLin k, Subgroup.subset_closure ⟨k, rfl⟩⟩ = co2Gen k := by
  refine Equiv.ext fun i => Fin.ext (co2Vec_injective (Fin.isLt _) (Fin.isLt _) ?_)
  rw [co2Vec_rho]
  exact co2SeedLin_apply k i

theorem co2Rho_range :
    co2Rho.range = co2P := by
  rw [co2Rho, MonoidHom.range_comp, co2Restr_range, MonoidHom.map_closure, co2P_eq]
  congr 1
  ext σ
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨k, (co2Rho_seed k).symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨_, ⟨k, rfl⟩, co2Rho_seed k⟩

@[expose] noncomputable def co2PermHom :
    Blueprint.NativeSporadic.Co2 →* Equiv.Perm (Fin 2300) :=
  co2Rho.comp ((co2JEquivG : co2J →* co2G).comp
    (co2MatEquiv : Blueprint.NativeSporadic.Co2 →* co2J))

theorem co2PermHom_apply
    (u : Blueprint.NativeSporadic.Co2) :
    co2PermHom u = co2Rho (co2JEquivG (co2MatEquiv u)) := rfl

theorem co2PermHom_injective :
    Function.Injective co2PermHom :=
  co2Rho_injective.comp (co2JEquivG.injective.comp co2MatEquiv.injective)

theorem co2PermHom_range :
    co2PermHom.range = co2P := by
  rw [← co2Rho_range]
  ext σ
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨g, rfl⟩
    refine ⟨co2MatEquiv.symm (co2JEquivG.symm g), ?_⟩
    rw [co2PermHom_apply, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

@[expose] noncomputable def co2PermEquiv :
    Blueprint.NativeSporadic.Co2 ≃* co2P :=
  (MonoidHom.ofInjective co2PermHom_injective).trans (MulEquiv.subgroupCongr co2PermHom_range)

theorem co2PermEquiv_apply
    (u : Blueprint.NativeSporadic.Co2) :
    (co2PermEquiv u : Equiv.Perm (Fin 2300)) = co2PermHom u := rfl

theorem co2Vec_permEquiv
    (u : Blueprint.NativeSporadic.Co2) (i : Fin 2300) :
    co2Vec ((co2PermEquiv u : Equiv.Perm (Fin 2300)) i) = u.val.val *ᵥ co2Vec i := by
  rw [co2PermEquiv_apply, co2PermHom_apply, co2Vec_rho, co2JEquivG_val, co2GLLin_apply,
    co2MatEquiv_val]

@[expose] noncomputable def co2SeedA :
    Blueprint.NativeSporadic.Co2 :=
  co2MatEquiv.symm ⟨co2GL1, Subgroup.subset_closure (Set.mem_insert _ _)⟩

@[expose] noncomputable def co2SeedB :
    Blueprint.NativeSporadic.Co2 :=
  co2MatEquiv.symm ⟨co2GL2, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

theorem co2SeedA_val : co2SeedA.val.val = co2A1 := by
  rw [← co2MatEquiv_val, co2SeedA, MulEquiv.apply_symm_apply]
  rfl

theorem co2SeedB_val : co2SeedB.val.val = co2A2 := by
  rw [← co2MatEquiv_val, co2SeedB, MulEquiv.apply_symm_apply]
  rfl

theorem co2PermEquiv_seed
    {u : Blueprint.NativeSporadic.Co2} {k : Fin 2}
    (hu : u.val.val = (co2SeedGL k : Matrix (Fin 22) (Fin 22) (ZMod 2))) :
    (co2PermEquiv u : Equiv.Perm (Fin 2300)) = co2Gen k := by
  refine Equiv.ext fun i => Fin.ext (co2Vec_injective (Fin.isLt _) (Fin.isLt _) ?_)
  rw [co2Vec_permEquiv, hu, ← co2GLLin_apply, ← co2SeedLin, co2SeedLin_apply]

theorem co2PermEquiv_seedA :
    (co2PermEquiv co2SeedA : Equiv.Perm (Fin 2300)) = co2Gen 0 :=
  co2PermEquiv_seed (k := 0) co2SeedA_val

theorem co2PermEquiv_seedB :
    (co2PermEquiv co2SeedB : Equiv.Perm (Fin 2300)) = co2Gen 1 :=
  co2PermEquiv_seed (k := 1) co2SeedB_val

theorem fam_co2_faithful_permutation_action :
    (∀ i < 2300, co2Vec i ≠ 0) ∧
    (∀ i < 2300, ∀ j < 2300, co2Vec i = co2Vec j → i = j) ∧
    co2BasisList = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 18, 23, 28, 41, 61] ∧
    LinearIndependent (ZMod 2) (fun t : Fin 22 => co2Vec (co2BasisList.getD t 0)) ∧
    Submodule.span (ZMod 2) (Set.range fun t : Fin 22 => co2Vec (co2BasisList.getD t 0)) = ⊤ ∧
    (∀ i : Fin 2300, co2A1 *ᵥ co2Vec i = co2Vec (co2Gen 0 i)) ∧
    (∀ i : Fin 2300, co2A2 *ᵥ co2Vec i = co2Vec (co2Gen 1 i)) ∧
    (∀ (u : Blueprint.NativeSporadic.Co2) (i : Fin 2300),
      co2Vec ((co2PermEquiv u : Equiv.Perm (Fin 2300)) i) = u.val.val *ᵥ co2Vec i) ∧
    co2SeedA.val.val = co2A1 ∧ co2SeedB.val.val = co2A2 ∧
    (co2PermEquiv co2SeedA : Equiv.Perm (Fin 2300)) = co2Gen 0 ∧
    (co2PermEquiv co2SeedB : Equiv.Perm (Fin 2300)) = co2Gen 1 :=
  ⟨fun _ hi => co2Vec_ne_zero hi, fun _ hi _ hj h => co2Vec_injective hi hj h, rfl,
    co2Basis_linearIndependent, co2Basis_span, co2A1_mulVec, co2A2_mulVec, co2Vec_permEquiv,
    co2SeedA_val, co2SeedB_val, co2PermEquiv_seedA, co2PermEquiv_seedB⟩

end CFSG.Sporadic.Co2Cert
