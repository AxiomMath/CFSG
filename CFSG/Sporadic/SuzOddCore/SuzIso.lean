module

public import CFSG.Sporadic.SuzOddCore.Perms
public import CFSG.Sporadic.SuzOddCore.RelabelCheck
public import CFSG.Sporadic.Suz.Simple

public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th

theorem perm_apply_inv' {α : Type*} (σ : Equiv.Perm α) (x : α) : σ (σ⁻¹ x) = x := by
  rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]

theorem perm_inv_apply' {α : Type*} (σ : Equiv.Perm α) (x : α) : σ⁻¹ (σ x) = x := by
  rw [← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]

theorem perm_conj_apply' {α : Type*} (τ σ : Equiv.Perm α) (x : α) :
    (MulAut.conj τ σ) x = τ (σ (τ⁻¹ x)) := by
  rw [MulAut.conj_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]

@[expose] def relabelPerm : Equiv.Perm (Fin 22880) := permC 22880 relabelArr

theorem rep_relabelPerm :
    CFSG.Monster.B.Co2.Rep 22880 relabelArr relabelPerm :=
  (rep_permC (Bool.and_eq_true_iff.1 arrays_check.2.2.2.2.2.2.2.2.2.2.2.1).2).1

theorem relabel_facts (i : ℕ) (hi : i < 22880) :
    relabelArr[Native.ap CFSG.Sporadic.Suz.orb.alpha i]! = (certArr 0)[relabelArr[i]!]! ∧
      relabelArr[Native.ap CFSG.Sporadic.Suz.orb.beta i]! = (certArr 1)[relabelArr[i]!]! := by
  have h := relabel_check
  simp only [relabelOK, Bool.and_eq_true, beq_iff_eq] at h
  have := allLt_spec h.2 hi
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact this

@[expose] def rhoJ : CFSG.Sporadic.Suz.J →* Equiv.Perm (Fin 22880) :=
  MulAction.toPermHom CFSG.Sporadic.Suz.J (Fin 22880)

theorem rhoJ_apply
    (g : CFSG.Sporadic.Suz.J) (x : Fin 22880) : rhoJ g x = g • x := by
  rw [rhoJ, MulAction.toPermHom_apply, MulAction.toPerm_apply]

theorem rhoJ_injective : Function.Injective rhoJ := by
  intro g h hgh
  apply FaithfulSMul.eq_of_smul_eq_smul (α := Fin 22880)
  intro x
  rw [← rhoJ_apply, ← rhoJ_apply, hgh]

@[expose] def psiJ : CFSG.Sporadic.Suz.J →* Equiv.Perm (Fin 22880) :=
  (MulAut.conj relabelPerm).toMonoidHom.comp rhoJ

theorem psiJ_apply (g : CFSG.Sporadic.Suz.J) (x : Fin 22880) :
    psiJ g x = relabelPerm (g • relabelPerm⁻¹ x) := by
  rw [psiJ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, perm_conj_apply', rhoJ_apply]

theorem psiJ_injective : Function.Injective psiJ :=
  (MulAut.conj relabelPerm).injective.comp rhoJ_injective

theorem relabel_smul
    (g : CFSG.Sporadic.Suz.J) (T : Native.Table) (t : Array ℕ)
    (σ : Equiv.Perm (Fin 22880)) (hT : Rep 22880 T g) (ht : CFSG.Monster.B.Co2.Rep 22880 t σ)
    (h : ∀ i < 22880, relabelArr[Native.ap T i]! = t[relabelArr[i]!]!) :
    psiJ g = σ := by
  ext x
  rw [psiJ_apply]
  set y := relabelPerm⁻¹ x with hy
  have hx : x = relabelPerm y := by rw [hy, perm_apply_inv']
  rw [hx]
  have e := h y.val y.isLt
  rw [hT y.val y.isLt, idx_of_lt g y.isLt, Fin.eta, rep_relabelPerm (g • y), rep_relabelPerm y,
    ht (relabelPerm y)] at e
  exact congrArg Fin.val (Fin.ext e)

theorem psiJ_a :
    psiJ CFSG.Sporadic.Suz.a = suzA0 :=
  relabel_smul _ _ _ _ CFSG.Sporadic.Suz.rep_alpha rep_suzA0 fun i hi => (relabel_facts i hi).1

theorem psiJ_b :
    psiJ CFSG.Sporadic.Suz.b = suzA1 :=
  relabel_smul _ _ _ _ CFSG.Sporadic.Suz.rep_beta rep_suzA1 fun i hi => (relabel_facts i hi).2

theorem psiJ_range :
    psiJ.range = suzP := by
  rw [MonoidHom.range_eq_map, ← CFSG.Sporadic.Suz.closure_ab, MonoidHom.map_closure, suzP]
  congr 1
  rw [Set.image_insert_eq, Set.image_singleton, psiJ_a, psiJ_b]

@[expose] def suzJEquivP :
    CFSG.Sporadic.Suz.J ≃* suzP :=
  (MonoidHom.ofInjective psiJ_injective).trans (MulEquiv.subgroupCongr psiJ_range)

theorem suzJEquivP_apply
    (g : CFSG.Sporadic.Suz.J) :
    ((suzJEquivP g : suzP) : Equiv.Perm (Fin 22880)) = psiJ g := by
  rw [suzJEquivP, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply]

@[expose] def suzA0P : suzP := ⟨suzA0, Subgroup.subset_closure (Set.mem_insert _ _)⟩

@[expose] def suzA1P : suzP :=
  ⟨suzA1, Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩

@[expose] def suzSeedEquiv :
    Blueprint.NativeSporadic.Suz ≃* CFSG.Sporadic.Suz.J :=
  Blueprint.NativeSporadic.matrixSeedEquiv 3 64 (by norm_num) CFSG.Sporadic.Suz.mA
    CFSG.Sporadic.Suz.mB (CFSG.Sporadic.Suz.det_mA_ne_zero CFSG.Sporadic.Suz.matrixFacts)
    (CFSG.Sporadic.Suz.det_mB_ne_zero CFSG.Sporadic.Suz.matrixFacts)

theorem suzSeedEquiv_val (u : Blueprint.NativeSporadic.Suz) :
    ((suzSeedEquiv u : Matrix.GeneralLinearGroup (Fin 64) (ZMod 3)) :
      Matrix (Fin 64) (Fin 64) (ZMod 3)) = u.val.val :=
  Blueprint.NativeSporadic.matrixSeedEquiv_val 3 64 _ _ _ _ _ u

@[expose] def suzSeedA :
    Blueprint.NativeSporadic.Suz := suzSeedEquiv.symm CFSG.Sporadic.Suz.a

@[expose] def suzSeedB :
    Blueprint.NativeSporadic.Suz := suzSeedEquiv.symm CFSG.Sporadic.Suz.b

theorem suzSeedA_val :
    (suzSeedA : Matrix (Fin 64) (Fin 64) (ZMod 3)) =
    Blueprint.NativeSporadic.decode 3 64 1 Blueprint.NativeSporadic.SuzSeed1 := by
  have h := suzSeedEquiv_val suzSeedA
  rw [suzSeedA, MulEquiv.apply_symm_apply] at h
  rw [suzSeedA, ← h]
  exact CFSG.Sporadic.Suz.a_val

theorem suzSeedB_val :
    (suzSeedB : Matrix (Fin 64) (Fin 64) (ZMod 3)) =
    Blueprint.NativeSporadic.decode 3 64 1 Blueprint.NativeSporadic.SuzSeed2 := by
  have h := suzSeedEquiv_val suzSeedB
  rw [suzSeedB, MulEquiv.apply_symm_apply] at h
  rw [suzSeedB, ← h]
  exact CFSG.Sporadic.Suz.b_val

theorem closure_suzSeeds :
    Subgroup.closure ({suzSeedA, suzSeedB} : Set Blueprint.NativeSporadic.Suz) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have key : ∀ y : CFSG.Sporadic.Suz.J,
      suzSeedEquiv.symm y ∈ Subgroup.closure ({suzSeedA, suzSeedB} : Set _) := by
    intro y
    have hy : y ∈ Subgroup.closure
        ({CFSG.Sporadic.Suz.a, CFSG.Sporadic.Suz.b} : Set CFSG.Sporadic.Suz.J) := by
      rw [CFSG.Sporadic.Suz.closure_ab]
      exact Subgroup.mem_top y
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | rfl
      · exact Subgroup.subset_closure (Set.mem_insert _ _)
      · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    | one => rw [map_one]; exact Subgroup.one_mem _
    | mul y z _ _ hy hz => rw [map_mul]; exact Subgroup.mul_mem _ hy hz
    | inv y _ hy => rw [map_inv]; exact Subgroup.inv_mem _ hy
  have := key (suzSeedEquiv x)
  rwa [MulEquiv.symm_apply_apply] at this

@[expose] def suzEquivP :

    Blueprint.NativeSporadic.Suz ≃* suzP := suzSeedEquiv.trans suzJEquivP

theorem suzEquivP_seedA :
    suzEquivP suzSeedA = suzA0P := by
  apply Subtype.ext
  rw [suzEquivP, MulEquiv.trans_apply, suzSeedA, MulEquiv.apply_symm_apply, suzA0P,
    suzJEquivP_apply, psiJ_a]

theorem suzEquivP_seedB :
    suzEquivP suzSeedB = suzA1P := by
  apply Subtype.ext
  rw [suzEquivP, MulEquiv.trans_apply, suzSeedB, MulEquiv.apply_symm_apply, suzA1P,
    suzJEquivP_apply, psiJ_b]

theorem suz_hom_ext
    {G : Type*} [Group G] {f g : Blueprint.NativeSporadic.Suz →* G}
    (hA : f suzSeedA = g suzSeedA) (hB : f suzSeedB = g suzSeedB) : f = g := by
  have h : Subgroup.closure ({suzSeedA, suzSeedB} : Set _) ≤ f.eqLocus g := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hA
    · exact hB
  rw [closure_suzSeeds] at h
  ext x
  exact h (Subgroup.mem_top x)

theorem suzEquivP_unique
    (e : Blueprint.NativeSporadic.Suz ≃* suzP)
    (hA : e suzSeedA = suzA0P) (hB : e suzSeedB = suzA1P) : e = suzEquivP := by
  apply MulEquiv.ext
  intro x
  have hx : x ∈ Subgroup.closure ({suzSeedA, suzSeedB} : Set Blueprint.NativeSporadic.Suz) := by
    rw [closure_suzSeeds]
    exact Subgroup.mem_top x
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · rw [hA, suzEquivP_seedA]
    · rw [hB, suzEquivP_seedB]
  | one => rw [map_one, map_one]
  | mul y z _ _ hy hz => rw [map_mul, map_mul, hy, hz]
  | inv y _ hy => rw [map_inv, map_inv, hy]

theorem suzP_card :
    Nat.card suzP = 448345497600 := by
  rw [← Nat.card_congr suzJEquivP.toEquiv, CFSG.Sporadic.Suz.card_J]

theorem suzP_isSimpleGroup :
    IsSimpleGroup suzP :=
  @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Suz.isSimpleGroup_J suzJEquivP.symm

theorem suzP_isPreprimitive :
    MulAction.IsPreprimitive suzP (Fin 22880) := by
  have hJ := CFSG.Sporadic.Suz.isPreprimitive
  have key : ∀ (g : CFSG.Sporadic.Suz.J) (x : Fin 22880),
      (suzJEquivP g : suzP) • relabelPerm x = relabelPerm (g • x) := by
    intro g x
    rw [Subgroup.smul_def, Equiv.Perm.smul_def, suzJEquivP_apply, psiJ_apply, perm_inv_apply']
  let f : Fin 22880 →ₑ[(suzJEquivP : CFSG.Sporadic.Suz.J → suzP)] Fin 22880 :=
    { toFun := fun x => relabelPerm x
      map_smul' := fun g x => (key g x).symm }
  have hf : Function.Surjective f := fun y => ⟨relabelPerm⁻¹ y, perm_apply_inv' relabelPerm y⟩
  exact MulAction.IsPreprimitive.of_surjective hf

end CFSG.Sporadic.SuzOddCore
