module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Overgroup
public import CFSG.LieType.SteinbergBRBinaryLinearSylow
public import CFSG.LieType.SteinbergBRAutGL32

public section

namespace CFSG.Quasithin.H13.L619

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Vol2Native.A312L

open scoped Pointwise

theorem isSimpleGroup_GL_zmod_two {m : ℕ} (hm : 3 ≤ m) :
    IsSimpleGroup (GL (Fin m) (ZMod 2)) := by
  have := (CFSG.LinearGroups.linear_projective_simple (K := ZMod 2) (n := m) (by omega)
    (Or.inl hm)).2.1
  let e₁ : Matrix.ProjectiveSpecialLinearGroup (Fin m) (ZMod 2) ≃*
      Matrix.ProjGenLinGroup (Fin m) (ZMod 2) :=
    MulEquiv.ofBijective Matrix.ProjectiveSpecialLinearGroup.toPGL
      ⟨Matrix.ProjectiveSpecialLinearGroup.toPGL_injective,
        Matrix.ProjectiveSpecialLinearGroup.toPGL_surj_of_roots fun r =>
          ⟨1, Subsingleton.elim _ _⟩⟩
  have hZ : Subgroup.center (GL (Fin m) (ZMod 2)) = ⊥ := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, eq_bot_iff]
    rintro _ ⟨r, rfl⟩
    rw [Subsingleton.elim r 1, map_one]
    exact Subgroup.one_mem _
  let e₂ : Matrix.ProjGenLinGroup (Fin m) (ZMod 2) ≃* GL (Fin m) (ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact (e₁.trans e₂).symm.isSimpleGroup

theorem isSimpleGroup_GL32 : IsSimpleGroup (GL (Fin 3) (ZMod 2)) :=
  isSimpleGroup_GL_zmod_two le_rfl

theorem card_GL32 : Nat.card (GL (Fin 3) (ZMod 2)) = 168 := by
  rw [Matrix.card_GL_field, ZMod.card]
  decide

theorem inner_of_cube_GL32 {Kt : Type*} [Group Kt] (eK : Kt ≃* GL (Fin 3) (ZMod 2))
    (α : MulAut Kt) (hα : α ^ 3 = 1) : ∃ k : Kt, ∀ x, α x = k * x * k⁻¹ := by
  set β : MulAut (GL (Fin 3) (ZMod 2)) := (eK.symm.trans α).trans eK with hβ
  have hβapp : ∀ y, β y = eK (α (eK.symm y)) := fun y => rfl
  have hβ3 : β ^ 3 = 1 := by
    refine MulEquiv.ext fun y => ?_
    have h1 : α (α (α (eK.symm y))) = eK.symm y := by
      have := congrArg (fun γ : MulAut Kt => γ (eK.symm y)) hα
      simpa [pow_succ, MulAut.mul_apply] using this
    rw [pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply, hβapp, hβapp, hβapp,
      MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, h1, MulEquiv.apply_symm_apply,
      MulAut.one_apply]
  have hH := CFSG.LieType.SteinbergBR.AutGL32.index_inner
  have h2 := Subgroup.mul_self_mem_of_index_two hH β
  have hmem : β ∈ (MulAut.conj : GL (Fin 3) (ZMod 2) →* MulAut _).range := by
    have e : β = β ^ 3 * (β * β)⁻¹ := by group
    rw [e, hβ3, one_mul]
    exact Subgroup.inv_mem _ h2
  obtain ⟨g, hg⟩ := hmem
  refine ⟨eK.symm g, fun x => eK.injective ?_⟩
  have := congrArg (fun γ : MulAut (GL (Fin 3) (ZMod 2)) => γ (eK x)) hg
  simp only [MulAut.conj_apply] at this
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, this, hβapp,
    MulEquiv.symm_apply_apply]

@[expose] noncomputable def levi3 (j : Fin 2) : ↥(Q3 (ZMod 2) j) →* GL (Fin 2) (ZMod 2) :=
  (blkMon (Q3 (ZMod 2) j) (1 - (j : ℕ)) 2 (q3_blk_le j) (q3_blockLeft j)
    (q3_blockRight j)).toHomUnits

theorem levi3_val (j : Fin 2) (x : ↥(Q3 (ZMod 2) j)) :
    ((levi3 j x : GL (Fin 2) (ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2)) =
      blkAt (1 - (j : ℕ)) 2 (q3_blk_le j) (x.1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) := rfl

theorem levi3_surjective (j : Fin 2) : Function.Surjective (levi3 j) := by
  intro A
  have hdet : (A : Matrix (Fin 2) (Fin 2) (ZMod 2)).det = 1 := by
    have h1 : Matrix.GeneralLinearGroup.det A = 1 := Subsingleton.elim _ _
    have h2 := congrArg (fun u : (ZMod 2)ˣ => (u : ZMod 2)) h1
    simpa using h2
  let A' : SpecialLinearGroup (Fin 2) (ZMod 2) := ⟨A, hdet⟩
  refine ⟨⟨embSL j A', embSL_mem_Q3 j A'⟩, Units.ext ?_⟩
  rw [levi3_val]
  exact blkAt_embMat j _

theorem levi3_ker_le (j : Fin 2) {x : ↥(Q3 (ZMod 2) j)} (hx : levi3 j x = 1) :
    (x : SpecialLinearGroup (Fin 3) (ZMod 2)) ∈ unitriangular 3 (ZMod 2) := by
  have h1 : ((levi3 j x : GL (Fin 2) (ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2)) = 1 := by
    rw [hx, Units.val_one]
  rw [levi3_val] at h1
  exact blk3_ker_aux j _ x.2 fun i k => by rw [h1]

theorem isPGroup_levi3_ker (j : Fin 2) : IsPGroup 2 (levi3 j).ker := by
  intro x
  obtain ⟨k, hk⟩ := isPGroup_unitriangular (K := ZMod 2) ⟨1, by rw [Nat.card_zmod]; rfl⟩
    ⟨_, levi3_ker_le j x.2⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg Subtype.val hk
  exact this

theorem Q3_sup_eq_top : Q3 (ZMod 2) 0 ⊔ Q3 (ZMod 2) 1 = ⊤ := by
  rw [Q3_eq, Q3_eq]
  refine CFSG.QuasithinUnique.Setup.Family.flagStabilizer_sup_eq_top_of_disjoint fun i _ _ => ?_
  simp only [Set.mem_singleton_iff, Fin.val_zero, Fin.val_one]
  omega

theorem unitriangular_le_Q3 (j : Fin 2) : unitriangular 3 (ZMod 2) ≤ Q3 (ZMod 2) j :=
  (unitriangular_le_upperTriangular 3 (ZMod 2)).trans (upperTriangular_le_Q3 j)

theorem normalizer_unitriangular_two :
    Subgroup.normalizer (unitriangular 3 (ZMod 2) : Set (SpecialLinearGroup (Fin 3) (ZMod 2))) =
      unitriangular 3 (ZMod 2) := by
  rw [normalizer_unitriangular,
    CFSG.LieType.SteinbergBR.BinaryLinear.upperTriangular_eq_unitriangular (Nat.card_zmod 2)]

theorem sl32_parabolics_of {X : Type*} [Group X] (f : X ≃* SpecialLinearGroup (Fin 3) (ZMod 2))
    {U : Subgroup X} (hmem : ∀ x, x ∈ U ↔ f x ∈ unitriangular 3 (ZMod 2)) :
    Subgroup.normalizer (U : Set X) ≤ U ∧
      ∃ Q : Fin 2 → Subgroup X, (∀ j, U ≤ Q j) ∧ Q 0 ⊔ Q 1 = ⊤ ∧
        ∀ j, ∃ ρ : ↥(Q j) →* GL (Fin 2) (ZMod 2), Function.Surjective ρ ∧ IsPGroup 2 ρ.ker := by
  refine ⟨fun k hk => ?_, fun j => (Q3 (ZMod 2) j).comap f.toMonoidHom, fun j x hx => ?_, ?_,
    fun j => ⟨(levi3 j).comp (f.toMonoidHom.subgroupComap (Q3 (ZMod 2) j)), ?_, ?_⟩⟩
  · rw [hmem, ← normalizer_unitriangular_two]
    refine Subgroup.mem_normalizer_iff.mpr fun h => ?_
    have e1 : h = f (f.symm h) := (f.apply_symm_apply h).symm
    have e2 : f k * h * (f k)⁻¹ = f (k * f.symm h * k⁻¹) := by
      rw [map_mul, map_mul, map_inv, f.apply_symm_apply]
    rw [e2, ← hmem, e1, ← hmem, f.symm_apply_apply]
    exact Subgroup.mem_normalizer_iff.mp hk _
  · exact unitriangular_le_Q3 j ((hmem x).mp hx)
  · show (Q3 (ZMod 2) 0).comap f.toMonoidHom ⊔ (Q3 (ZMod 2) 1).comap f.toMonoidHom = ⊤
    rw [Subgroup.comap_sup_eq f.toMonoidHom _ _ f.surjective, Q3_sup_eq_top, Subgroup.comap_top]
  · exact (levi3_surjective j).comp
      (MonoidHom.subgroupComap_surjective _ _ f.surjective)
  · intro x
    have hx : (f.toMonoidHom.subgroupComap (Q3 (ZMod 2) j)) x ∈ (levi3 j).ker := x.2
    obtain ⟨k, hk⟩ := isPGroup_levi3_ker j ⟨_, hx⟩
    refine ⟨k, Subtype.ext (MonoidHom.subgroupComap_injective _ _ f.injective ?_)⟩
    have := congrArg Subtype.val hk
    rw [SubgroupClass.coe_pow, map_pow, OneMemClass.coe_one, map_one]
    simpa using this

theorem gl32_parabolics {X : Type*} [Group X] (e : X ≃* GL (Fin 3) (ZMod 2)) {U : Subgroup X}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) :
    Subgroup.normalizer (U : Set X) ≤ U ∧
      ∃ Q : Fin 2 → Subgroup X, (∀ j, U ≤ Q j) ∧ Q 0 ⊔ Q 1 = ⊤ ∧
        ∀ j, ∃ ρ : ↥(Q j) →* GL (Fin 2) (ZMod 2), Function.Surjective ρ ∧ IsPGroup 2 ρ.ker := by
  classical
  set f : X ≃* SpecialLinearGroup (Fin 3) (ZMod 2) :=
    e.trans (CFSG.QuasithinUnique.Setup.Family.slEquivGL 3).symm with hf
  have hU2 : IsPGroup 2 (U.map f.toMonoidHom) := hU.2.1.map _
  have hidx : ¬ 2 ∣ (U.map f.toMonoidHom).index := by
    rw [MulEquiv.toMonoidHom_eq_coe, Subgroup.index_map_equiv]
    have := hU.2.2
    rwa [show (U.subgroupOf ⊤).index = U.index from Subgroup.relIndex_top_right U] at this
  obtain ⟨S, hS⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 (n := 3) (by norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin 3) (ZMod 2)) S
    (hU2.toSylow hidx)
  have hg' : U.map f.toMonoidHom = MulAut.conj g • unitriangular 3 (ZMod 2) := by
    have := congrArg (fun P : Sylow 2 (SpecialLinearGroup (Fin 3) (ZMod 2)) =>
      (P : Subgroup (SpecialLinearGroup (Fin 3) (ZMod 2)))) hg
    simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe, hS] at this
    exact this.symm
  refine sl32_parabolics_of (f.trans (MulAut.conj g⁻¹)) fun x => ?_
  have h1 : x ∈ U ↔ f x ∈ U.map f.toMonoidHom := by
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  rw [h1, hg', Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
    MulAut.conj_inv_apply]
  simp

end CFSG.Quasithin.H13.L619
