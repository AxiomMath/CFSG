module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.SubrepresentationLattice
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.RepEquiv

namespace CFSG
end CFSG
open CFSG

open LinearMap
open scoped TensorProduct
open scoped MonoidAlgebra

namespace CFSG.Theory.Representation

open _root_.Representation

section extendScalarsRep

variable {F G V W : Type*} [Monoid G] [Field F] [AddCommGroup V] [AddCommGroup W] [Module F V] [Module F W] (F' : Type*) [Field F'] [Algebra F F'] (ρ : Representation F G V) (σ : Representation F G W)

/-- The representation obtained from `ρ` by extending scalars from `F` to `F'`. -/
@[expose]
public def extendScalars : Representation F' G (F' ⊗[F] V) := {
  toFun := fun g => (ρ g).baseChange F'
  map_one' := by rw [map_one, baseChange_one],
  map_mul' := fun g g' => by rw [map_mul, baseChange_mul]
  }

@[simp]
public theorem extendScalars_apply (g : G) : extendScalars F' ρ g = (ρ g).baseChange F' := by rfl


set_option backward.isDefEq.respectTransparency false in
public theorem extendScalars_nontrivial_iff :
    Nontrivial ρ.asModule ↔ Nontrivial (extendScalars F' ρ).asModule := by
  rw [← rank_pos_iff_nontrivial (R := F), ← rank_pos_iff_nontrivial (R := F')]
  have : Module.rank F' (extendScalars F' ρ).asModule = Module.rank F' (F' ⊗[F] V) := rfl
  rw [this, Module.rank_baseChange, Cardinal.zero_lt_lift_iff]
  rfl

public instance extendScalars_nontrivial [inst : Nontrivial V] : Nontrivial (extendScalars F' ρ).asModule := (extendScalars_nontrivial_iff _ _).mp inst

set_option backward.isDefEq.respectTransparency false in
public theorem extendScalars_finite_dimensional_iff :
    FiniteDimensional F ρ.asModule ↔ FiniteDimensional F' (extendScalars F' ρ).asModule := by
  unfold FiniteDimensional
  let : Module.Free F' ((extendScalars F' ρ).asModule) := Module.Free.of_divisionRing F' (F' ⊗[F] V)
  rw [← Module.rank_lt_aleph0_iff, ← Module.rank_lt_aleph0_iff (R := F')]
  have : Module.rank F' (extendScalars F' ρ).asModule = Module.rank F' (F' ⊗[F] V) := rfl
  rw [this, Module.rank_baseChange, Cardinal.lift_lt_aleph0]
  rfl

set_option backward.isDefEq.respectTransparency false in
public instance extendScalars_finite_dimensional [inst : FiniteDimensional F V] : FiniteDimensional F' (extendScalars F' ρ).asModule := (extendScalars_finite_dimensional_iff _ _).mp inst

public theorem extendScalars_faithful_iff :
    Function.Injective ρ ↔ Function.Injective (extendScalars F' ρ) := by
  refine ⟨fun hi g₁ g₂ he => ?_, fun hi g₁ g₂ he => ?_⟩
  · rw [← Function.Injective.eq_iff hi]
    ext v
    exact (Module.FaithfullyFlat.tensorProduct_mk_injective _) (DFunLike.congr_fun he (1 ⊗ₜ v))
  · rw [← Function.Injective.eq_iff hi]
    ext v
    simp only [extendScalars, MonoidHom.coe_mk, OneHom.coe_mk,
      TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
      coe_restrictScalars, baseChange_tmul, he]

public theorem adjoin_eq_span :
    (Algebra.adjoin F (Set.range ρ)).toSubmodule = Submodule.span F (Set.range ρ) := by
  rw [Algebra.adjoin_eq_span, MonoidHom.mclosure_range, MonoidHom.coe_mrange]

set_option backward.isDefEq.respectTransparency false in
open Module.Basis in
lemma baseChange_surj_iff [FiniteDimensional F V] (S : Set (Module.End F V)) :
    Submodule.span F S = ⊤ ↔
    Submodule.span F' {s.baseChange F' | s ∈ S} = ⊤ := by
  let b := ofVectorSpace F V
  set ι := ofVectorSpaceIndex F V
  have : DecidableEq ι := Classical.typeDecidableEq ι
  let b2 := linearMap b b
  let b' := baseChange F' b
  let b2' := linearMap b' b'
  let j : S ≃ {s.baseChange F' | s ∈ S} :=by
    apply Equiv.ofBijective (fun s ↦ ⟨s.val.baseChange F', ⟨s.val, ⟨s.prop, rfl⟩⟩⟩) ⟨?_, ?_⟩
    · intro s₁ s₂ he
      simp only [Subtype.mk.injEq] at he
      rw [← Subtype.val_inj, ← sub_left_inj (a := s₂.val), sub_self]
      rw [← sub_left_inj (a := baseChange F' s₂.val), sub_self, ← baseChange_sub] at he
      set s := s₁.val - s₂.val
      apply Module.Basis.ext b
      intro i
      have he : (baseChange F' s) (b' i) = 0 := he ▸ zero_apply _
      rw [baseChange_apply, baseChange_tmul, Module.FaithfullyFlat.one_tmul_eq_zero_iff] at he
      rw [LinearMap.zero_apply, he]
    · intro s'
      obtain ⟨s, hs1, hs2⟩ := s'.prop
      exact ⟨⟨s, hs1⟩, SetCoe.ext hs2⟩
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [eq_top_iff, ← Module.Basis.span_eq b2', Submodule.span_le]
    intro M ⟨i, hi⟩
    have : b2 i ∈ Submodule.span F S := h ▸ Submodule.mem_top
    rw [← hi, SetLike.mem_coe]
    rw [Submodule.mem_span_set'] at this ⊢
    obtain ⟨n, f, g, h⟩ := this
    have : b2' i = ∑ i, f i • ((g i).val.baseChange F') := by
      apply Module.Basis.ext b'
      intro i'
      have : ∑ i : Fin n, f i • baseChange F' (g i).val = ∑ i : Fin n, baseChange F' (f i • (g i).val) := by simp only [baseChange_smul]
      rw [this]
      have : ∑ i : Fin n, baseChange F' (f i • (g i).val) = baseChange F' (∑ i : Fin n, (f i • (g i).val)) := by
        set d : Module.End F V → Module.End F' (F' ⊗[F] V) := baseChange F'
        let d' : Module.End F V →ₗ[F] Module.End F' (F' ⊗[F] V) := {
          toFun := d
          map_add' := baseChange_add
          map_smul' := baseChange_smul
        }
        show ∑ i, d' (f i • ↑(g i)) = d' (∑ i, f i • ↑(g i))
        rw [map_sum]
      rw [this, h, linearMap_apply_apply]
      have : (baseChange F' (b2 i)) (b' i') = 1 ⊗ₜ (b2 i) (b i') := by
        rw [baseChange_apply, baseChange_tmul]
      rw [this, baseChange_apply, linearMap_apply_apply]
      simp_all only [baseChange_smul]
      split; rfl; rw [TensorProduct.tmul_zero]
    rw [this]
    use n, (algebraMap F F') ∘ f, j ∘ g
    simp only [Function.comp_apply, Equiv.ofBijective_apply,
      algebraMap_smul, j]
  · rw [eq_top_iff, ← Module.Basis.span_eq b2, Submodule.span_le]
    intro M ⟨i, hi⟩
    have : b2' i ∈ Submodule.span F' {s.baseChange F' | s ∈ S} := h ▸ Submodule.mem_top
    rw [← hi, SetLike.mem_coe]
    rw [Submodule.mem_span_set'] at this ⊢
    obtain ⟨n, f, g, h⟩ := this
    obtain ⟨k, hk⟩ := Module.Projective.exists_dual_eq_one (K := F) (V := F') (x := 1) (one_ne_zero' F')
    let Tf : F' ⊗[F] V →ₗ[F] F' ⊗[F] V := LinearMap.rTensor V ((Algebra.linearMap F F').comp k)
    have hTf (i' : ι): Tf (b' i') = b' i' := by
      simp_all only [baseChange_apply, rTensor_tmul, coe_comp,
        Function.comp_apply, Algebra.linearMap_apply, map_one, ι, b2', b', Tf]
    have hTf' (f : F') (s : Module.End F V) (i' : ι) : Tf ((f • s.baseChange F') (b' i')) = 1 ⊗ₜ (k f • s (b i')) := by
      have : (f • s.baseChange F') (b' i') = f • (1 ⊗ₜ s (b i')) := by
        simp only [baseChange_apply, LinearMap.smul_apply, baseChange_tmul, ι, b']
      rw [this, TensorProduct.smul_tmul', rTensor_tmul]
      simp only [smul_eq_mul, mul_one, coe_comp, Function.comp_apply]
      have : (Algebra.linearMap F F') (k f) = (k f) • (1 : F') := by
        have : (k f) = (k f) • (1 : F) := by
          simp only [smul_eq_mul, mul_one]
        nth_rw 1 [this]
        simp only [map_smul, Algebra.linearMap_apply, map_one]
      rw [this, TensorProduct.smul_tmul]
    use n, k ∘ f, j.symm ∘ g
    simp only [Function.comp_apply]
    apply Module.Basis.ext b
    intro i'
    have h : (∑ i, f i • (g i).val) (b' i') = (if i.2 = i' then b' i.1 else 0) := by
      rw [h, Module.Basis.linearMap_apply_apply,
         Module.Basis.baseChange_apply]
    rw [Module.Basis.linearMap_apply_apply, LinearMap.sum_apply]
    split <;> (expose_names; simp only [h_3, ↓reduceIte] at h) <;> have h := LinearMap.congr_arg (f := Tf) h
    · rw [← sub_left_inj (a := b i.1), sub_self]
      rw [← sub_left_inj (a := Tf (b' i.1)), sub_self] at h
      suffices h : (1 : F') ⊗ₜ[F] (∑ d : Fin n, (k (f d) • (j.symm (g d)).val) (b i') - b i.1) = 0 by
        rw [Module.FaithfullyFlat.one_tmul_eq_zero_iff] at h
        exact h
      rw [← h, LinearMap.sum_apply, map_sum]
      have : ∑ x, Tf ((f x • (g x).val) (b' i')) - Tf (b' i.1) = ∑ x, 1 ⊗ₜ (k (f x) • (j.symm (g x)).val (b i')) - (b' i.1) := by
        rw [hTf, ← add_left_inj (a := b' i.1), sub_add, sub_self, sub_zero, sub_add, sub_self, sub_zero, Finset.sum_congr rfl]
        intro x _
        rw [← hTf']
        have : LinearMap.baseChange F' (j.symm (g x)).val = (g x).val := by
          set s := (j.symm (g x)).val
          have : j ⟨s, (j.symm (g x)).prop⟩ = g x := by
            simp only [Subtype.coe_eta,
              _root_.Equiv.apply_symm_apply, j, s]
          rw [← this]
          rfl
        rw [this]
      rw [this, TensorProduct.tmul_sub, Module.Basis.baseChange_apply, ← add_left_inj (a := (1 : F') ⊗ₜ[F] b i.1), sub_add, sub_self, sub_zero, sub_add, sub_self, sub_zero, TensorProduct.tmul_sum]
      rfl
    · suffices h : (1 : F') ⊗ₜ[F] (∑ d : Fin n, (k (f d) • (j.symm (g d)).val) (b i')) = 0 by
        rw [Module.FaithfullyFlat.one_tmul_eq_zero_iff] at h
        exact h
      rw [map_zero] at h
      rw [← h, LinearMap.sum_apply, map_sum]
      have : ∑ x, Tf ((f x • (g x).val) (b' i')) = ∑ x, 1 ⊗ₜ (k (f x) • (j.symm (g x)).val (b i')) := by
        rw [Finset.sum_congr rfl]
        intro x _
        rw [← hTf']
        have : LinearMap.baseChange F' (j.symm (g x)).val = (g x).val := by
          set s := (j.symm (g x)).val
          have : j ⟨s, (j.symm (g x)).prop⟩ = g x := by
            simp only [Subtype.coe_eta,
              _root_.Equiv.apply_symm_apply, j, s]
          rw [← this]
          rfl
        rw [this]
      rw [this, TensorProduct.tmul_sum]
      rfl

public theorem extendScalars_surj_iff [FiniteDimensional F V] :
    Algebra.adjoin F (Set.range ρ) = ⊤ ↔
    Algebra.adjoin F' (Set.range (extendScalars F' ρ)) = ⊤ := by
  have :(Set.range (extendScalars F' ρ)) = {s.baseChange F' | s ∈ (Set.range ρ)}:= by
    unfold extendScalars
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, Set.mem_range, exists_exists_eq_and]
    rfl
  rw [← Algebra.toSubmodule_eq_top, ← Algebra.toSubmodule_eq_top, adjoin_eq_span, adjoin_eq_span, this]
  exact baseChange_surj_iff F' (Set.range ρ)

/-- Base change of subrepresentations along scalar extension. -/
public def subrepresentation_extendScalars :
    Subrepresentation ρ → Subrepresentation (extendScalars F' ρ) := fun φ ↦ by
    refine .mk (φ.toSubmodule.baseChange F') ?_
    intro g v' ⟨v, hv⟩
    have : (baseChange F' (ρ g)) v' = (baseChange F' ((ρ g).comp φ.toSubmodule.subtype)) v := by rw [← hv, baseChange_comp]; rfl
    rw [extendScalars_apply, this]
    let motive : F' ⊗[F] ↥φ.toSubmodule → Prop := fun v ↦ (baseChange F' (ρ g ∘ₗ φ.toSubmodule.subtype)) v ∈ Submodule.baseChange F' φ.toSubmodule
    have zero : motive 0 := by
      unfold motive
      rw [map_zero]
      exact Submodule.zero_mem _
    have tmul : ∀ x y, motive <| x ⊗ₜ[F] y := by
      unfold motive
      intro x y
      simp only [baseChange_tmul, coe_comp, Submodule.coe_subtype, Function.comp_apply]
      apply Submodule.tmul_mem_baseChange_of_mem
      apply Subrepresentation.apply_mem_toSubmodule
      simp only [Submodule.coe_mem]
    have add : ∀ x y, motive x → motive y → motive (x + y) := by
      unfold motive
      intro x y hx hy
      rw [map_add]
      exact add_mem hx hy
    exact TensorProduct.induction_on v zero tmul add

public theorem subrepresentation_extendScalars_apply (φ : Subrepresentation ρ) :
  ((subrepresentation_extendScalars F' ρ) φ).toSubmodule = φ.toSubmodule.baseChange F' := by rfl

public theorem subrepresentation_extendScalars_bot :
    subrepresentation_extendScalars F' ρ ⊥ = ⊥ := by
  apply Subrepresentation.toSubmodule_injective
  have h1 : (⊥ : Subrepresentation ρ).toSubmodule = ⊥ := by rfl
  have h2 : (⊥ : Subrepresentation (extendScalars F' ρ)).toSubmodule = ⊥ := by rfl
  rw [subrepresentation_extendScalars_apply, h1, h2, Submodule.baseChange_bot]

public theorem subrepresentation_extendScalars_top :
    subrepresentation_extendScalars F' ρ ⊤ = ⊤ := by
  apply Subrepresentation.toSubmodule_injective
  have h1 : (⊤ : Subrepresentation ρ).toSubmodule = ⊤ := by rfl
  have h2 : (⊤ : Subrepresentation (extendScalars F' ρ)).toSubmodule = ⊤ := by rfl
  rw [subrepresentation_extendScalars_apply, h1, h2, Submodule.baseChange_top]

set_option backward.isDefEq.respectTransparency false in
lemma mem_of_tmul_mem_baseChange {m : V} {W : Submodule F V} (hm : 1 ⊗ₜ m ∈ W.baseChange F') : m ∈ W := by
  let f := Submodule.mkQ W
  have := LinearMap.exact_subtype_mkQ W
  rw [← Module.FaithfullyFlat.lTensor_exact_iff_exact (R := F) (M := F')] at this
  obtain ⟨v, hv⟩ := hm
  have := Function.Exact.apply_apply_eq_zero this v
  have hv : (lTensor F' W.subtype) v = 1 ⊗ₜ m := hv
  rw [hv] at this
  simp only [lTensor_tmul, Submodule.mkQ_apply, Module.FaithfullyFlat.one_tmul_eq_zero_iff,
    Submodule.Quotient.mk_eq_zero] at this
  exact this

public theorem subrepresentation_extendScalars_inj :
    Function.Injective (subrepresentation_extendScalars F' ρ) := fun φ₁ φ₂ he ↦ by
  suffices φ₁.toSubmodule = φ₂.toSubmodule by
    exact Subrepresentation.toSubmodule_injective this
  have he : (subrepresentation_extendScalars F' ρ φ₁).toSubmodule =
    (subrepresentation_extendScalars F' ρ φ₂).toSubmodule := by rw [he]
  rw [subrepresentation_extendScalars_apply, subrepresentation_extendScalars_apply] at he
  refine le_antisymm (fun v h ↦ ?_) (fun v h ↦ ?_)
  · have : (1 ⊗ₜ v) ∈ Submodule.baseChange F' φ₁.toSubmodule :=
      Submodule.tmul_mem_baseChange_of_mem 1 h
    rw [he] at this
    exact mem_of_tmul_mem_baseChange F' this
  · have : (1 ⊗ₜ v) ∈ Submodule.baseChange F' φ₂.toSubmodule :=
      Submodule.tmul_mem_baseChange_of_mem 1 h
    rw [← he] at this
    exact mem_of_tmul_mem_baseChange F' this

public theorem _root_.Subrepresentation.nontrivial_iff :
    Nontrivial (Subrepresentation ρ) ↔ Nontrivial ρ.asModule := by
  rw [← Submodule.nontrivial_iff (R := F) (M := ρ.asModule)]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨x, y, h⟩ := h
    use x.toSubmodule, y.toSubmodule
    contrapose h
    exact Subrepresentation.toSubmodule_injective h
  · have := top_ne_bot (α := Submodule F ρ.asModule)
    use ⊤, ⊥
    contrapose this
    have : (⊤ : Subrepresentation ρ).toSubmodule = (⊥ : Subrepresentation ρ).toSubmodule := by rw [this]
    exact this

public theorem extendScalars_subrepresentation_nontrivial_iff :
    Nontrivial (Subrepresentation ρ) ↔ Nontrivial (Subrepresentation (extendScalars F' ρ)) := by
  rw [Subrepresentation.nontrivial_iff, Subrepresentation.nontrivial_iff]
  exact extendScalars_nontrivial_iff F' ρ

set_option backward.isDefEq.respectTransparency false in
public theorem irreducible_of_extendScalars [inst : IsIrreducible (extendScalars F' ρ)] :
    IsIrreducible ρ := by
  have : Nontrivial (Subrepresentation ρ) := by
    rw [extendScalars_subrepresentation_nontrivial_iff (F' := F'), Subrepresentation.nontrivial_iff]
    exact Subrepresentation.irreducible_module_nontrivial (extendScalars F' ρ)
  unfold IsIrreducible
  rw [isSimpleOrder_iff]
  by_contra! h
  obtain ⟨a, ha⟩ := h this
  contrapose! ha
  intro ha
  have : (subrepresentation_extendScalars F' ρ a) ≠ ⊥ := by
    contrapose ha
    apply (subrepresentation_extendScalars_inj F' ρ)
    rw [ha, subrepresentation_extendScalars_bot]
  apply subrepresentation_extendScalars_inj F' ρ
  rw [subrepresentation_extendScalars_top]
  exact (inst.eq_bot_or_eq_top (subrepresentation_extendScalars F' ρ a)).resolve_left this

variable {ρ} {σ}

set_option backward.isDefEq.respectTransparency false in
/-- Extend an intertwining map along scalar extension. -/
@[expose]
public def extendScalars_map (e : ρ →ₗ σ) :
    extendScalars F' ρ →ₗ extendScalars F' σ :=
  RepMap.mk (baseChange F' e.toLinearMap) (by
    intro g
    ext x
    simp only [extendScalars_apply, TensorProduct.AlgebraTensorModule.curry_apply,
      restrictScalars_comp, TensorProduct.curry_apply, coe_comp, coe_restrictScalars,
      Function.comp_apply, baseChange_tmul, IntertwiningMap.coe_toLinearMap]
    rw [e.isIntertwining])

public theorem extendScalars_map_toLinearMap {e : ρ →ₗ σ} :
  (extendScalars_map F' e).toLinearMap = baseChange F' e.toLinearMap := by rfl


/-- Iterated scalar extension is canonically equivalent to direct scalar extension. -/
@[expose]
public def extendScalars_comp {F'' : Type*} [Field F''] [Algebra F' F''] [Algebra F F''] [IsScalarTower F F' F''] :
    extendScalars F'' (extendScalars F' ρ) ≃ₗ extendScalars F'' ρ :=
  RepEquiv.mk (TensorProduct.AlgebraTensorModule.cancelBaseChange F F' F'' F'' V) (by
  intro g
  ext x
  simp only [extendScalars_apply, TensorProduct.AlgebraTensorModule.curry_apply,
    restrictScalars_comp, TensorProduct.curry_apply, coe_restrictScalars, coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply, baseChange_tmul,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul])

end extendScalarsRep

/-- Scalar extension preserves invariant subspaces when the finite group order is
nonzero in both coefficient fields. -/
public theorem invariants_extendScalars_eq_baseChange_of_card_ne_zero
    {G : Type*} [Group G] [Finite G] {F : Type*} [Field F]
    {F' : Type*} [Field F'] [Algebra F F'] {V : Type*}
    [AddCommGroup V] [Module F V] (ρ : Representation F G V)
    (hF : (Nat.card G : F) ≠ 0) (hF' : (Nat.card G : F') ≠ 0) :
    Representation.invariants (Theory.Representation.extendScalars F' ρ) =
      (Representation.invariants ρ).baseChange F' := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Invertible (Fintype.card G : F) := by
    simpa [Nat.card_eq_fintype_card] using invertibleOfNonzero hF
  let _ : Invertible (Fintype.card G : F') := by
    simpa [Nat.card_eq_fintype_card] using invertibleOfNonzero hF'
  let S : Submodule F V := Representation.invariants ρ
  let S' : Submodule F' (F' ⊗[F] V) :=
    Representation.invariants (Theory.Representation.extendScalars F' ρ)
  let avg : V →ₗ[F] V := Representation.averageMap ρ
  let avgS : V →ₗ[F] ↥S :=
    avg.codRestrict S (Representation.averageMap_invariant (ρ := ρ))
  let avg' : F' ⊗[F] V →ₗ[F'] F' ⊗[F] V :=
    Representation.averageMap (Theory.Representation.extendScalars F' ρ)
  let avgS' : F' ⊗[F] V →ₗ[F'] ↥S' :=
    avg'.codRestrict S'
      (Representation.averageMap_invariant (ρ := Theory.Representation.extendScalars F' ρ))
  have havg_eq : avg' = LinearMap.baseChange F' avg := by
    ext a
    simp [avg', avg, Representation.averageMap, GroupAlgebra.average,
      Theory.Representation.extendScalars_apply, map_sum, TensorProduct.AlgebraTensorModule.curry_apply]
    rw [Finset.smul_sum]
    simp_rw [TensorProduct.smul_tmul']
    rw [TensorProduct.tmul_sum]
    simp [Algebra.smul_def]
  have havgS_subtype : S.subtype.comp avgS = avg := by
    ext v
    rfl
  have havgS_proj_apply (v : S) : avgS (S.subtype v) = v := by
    apply Subtype.ext
    change avg (S.subtype v) = S.subtype v
    exact Representation.averageMap_id (ρ := ρ) v v.2
  have havgS'_subtype : S'.subtype.comp avgS' = avg' := by
    ext v
    rfl
  have havgS'_proj_apply (v : S') : avgS' (S'.subtype v) = v := by
    apply Subtype.ext
    change avg' (S'.subtype v) = S'.subtype v
    exact Representation.averageMap_id (ρ := Theory.Representation.extendScalars F' ρ) v v.2
  have hrange_avg : LinearMap.range avg = S := by
    rw [← havgS_subtype, LinearMap.range_comp]
    rw [LinearMap.range_eq_of_proj havgS_proj_apply, Submodule.map_top, Submodule.range_subtype]
  have hrange_avg' : LinearMap.range avg' = S' := by
    rw [← havgS'_subtype, LinearMap.range_comp]
    rw [LinearMap.range_eq_of_proj havgS'_proj_apply, Submodule.map_top,
      Submodule.range_subtype]
  have hbc_comp :
      (LinearMap.baseChange F' S.subtype).comp (LinearMap.baseChange F' avgS) =
        LinearMap.baseChange F' avg := by
    rw [← LinearMap.baseChange_comp, havgS_subtype]
  have hbc_proj_eq :
      (LinearMap.baseChange F' avgS).comp (LinearMap.baseChange F' S.subtype) =
        LinearMap.id := by
    ext c
    exact congrArg (fun x => (1 : F') ⊗ₜ[F] x) (havgS_proj_apply c)
  have hbc_surj : Function.Surjective (LinearMap.baseChange F' avgS) := by
    intro a
    refine ⟨(LinearMap.baseChange F' S.subtype) a, ?_⟩
    simpa using DFunLike.congr_fun hbc_proj_eq a
  have hrange_avg_bc :
      LinearMap.range (LinearMap.baseChange F' avg) = S.baseChange F' := by
    rw [← hbc_comp, LinearMap.range_comp]
    rw [LinearMap.range_eq_top.2 hbc_surj, Submodule.map_top, Submodule.baseChange]
  calc
    S' = LinearMap.range avg' := hrange_avg'.symm
    _ = LinearMap.range (LinearMap.baseChange F' avg) := by rw [havg_eq]
    _ = S.baseChange F' := hrange_avg_bc


end CFSG.Theory.Representation
