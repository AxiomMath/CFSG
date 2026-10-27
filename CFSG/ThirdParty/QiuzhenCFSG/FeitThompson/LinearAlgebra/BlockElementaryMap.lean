module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

namespace CFSG
end CFSG
open CFSG

/-- The submodule of endomorphisms that map the `i`-block into the `t`-block
and vanish on every other block. -/
@[expose]
public def CFSG.blockElementaryMap
    {R : Type*} [CommSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M]
    {ι : Type*} (A : ι → Submodule R M) (i : ι) (t : ι) :
  Submodule R (Module.End R M) := {
    carrier := {X : Module.End R M | (∀ v ∈ A i, X v ∈ A t) ∧ (∀ j ≠ i,
    ∀ v ∈ A j, X v = 0)}
    add_mem' := by
      intro X Y ⟨hX1, hX2⟩ ⟨hY1, hY2⟩
      simp only [Set.mem_ofPred_eq]
      refine ⟨fun v hv ↦ ?_, fun j hj v hv ↦ ?_⟩
      · rw [LinearMap.add_apply]
        exact Submodule.add_mem (A t) (hX1 v hv) (hY1 v hv)
      · rw [LinearMap.add_apply, hX2 j hj v hv, hY2 j hj v hv, zero_add]
    zero_mem' := by
      refine ⟨fun v hv ↦ ?_, fun j hj v hv ↦ ?_⟩
      · rw [LinearMap.zero_apply]
        exact (A t).zero_mem
      · rw [LinearMap.zero_apply]
    smul_mem' := by
      intro r X ⟨hX1, hX2⟩
      refine ⟨fun v hv ↦ ?_, fun j hj v hv ↦ ?_⟩
      · rw [LinearMap.smul_apply]
        exact Submodule.smul_of_tower_mem (A t) r (hX1 v hv)
      · rw [LinearMap.smul_apply, hX2 j hj v hv, smul_zero]
  }

public lemma CFSG.mem_blockElementaryMap_iff
    {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    {ι : Type*} [DecidableEq ι]
    (A : ι → Submodule R M) (hA : DirectSum.IsInternal A)
    (i t : ι) (X : Module.End R M) :
    X ∈ blockElementaryMap A i t ↔
      (∀ v ∈ A i, X v ∈ A t) ∧ (∀ j, (A j ≠ A i) → ∀ v ∈ A j, X v = 0) := by
  constructor
  · rintro ⟨hX₁, hX₂⟩
    refine ⟨hX₁, ?_⟩
    intro j hj v hv
    have hij : j ≠ i := by
      intro hji
      apply hj
      simp [hji]
    exact hX₂ j hij v hv
  · rintro ⟨hX₁, hX₂⟩
    refine ⟨hX₁, ?_⟩
    intro j hij v hv
    by_cases hEq : A j = A i
    · have hdisj := hA.submodule_iSupIndep.pairwiseDisjoint hij
      dsimp [Function.onFun] at hdisj
      rw [hEq] at hdisj
      have hBot : A i = ⊥ := hdisj.eq_bot_of_self
      rw [hEq, hBot, Submodule.mem_bot] at hv
      simp [hv]
    · exact hX₂ j hEq v hv

section BlockDecomposition

variable {R M ι : Type*} [CommRing R]
variable [AddCommGroup M] [Module R M]
variable [DecidableEq ι] (A : ι → Submodule R M) (h : DirectSum.IsInternal A)

section Projections

open DirectSum LinearMap

/-- Given an internal direct sum decomposition `h : IsInternal A`, define the projection
  onto the `i`-th component as an endomorphism of `M`. -/
@[expose]
public noncomputable def CFSG.projection (i : ι) : Module.End R M :=
  (A i).subtype ∘ₗ component R ι (fun i => ↥(A i)) i ∘ₗ (LinearEquiv.ofBijective (coeLinearMap A) h).symm.toLinearMap

lemma CFSG.projection_apply (i : ι) (x : M) :
    projection A h i x = ((LinearEquiv.ofBijective (coeLinearMap A) h).symm x i).val := by
  calc
    projection A h i x = (A i).subtype (component R ι (fun i => ↥(A i)) i ((LinearEquiv.ofBijective (coeLinearMap A) h).symm x)) := rfl
    _ = (A i).subtype (((LinearEquiv.ofBijective (coeLinearMap A) h).symm x) i) := by rw [← apply_eq_component]
    _ = ((LinearEquiv.ofBijective (coeLinearMap A) h).symm x i).val := rfl

public lemma CFSG.projection_maps_to (i : ι) (x : M) : projection A h i x ∈ A i := by
  rw [projection_apply]
  exact ((LinearEquiv.ofBijective (coeLinearMap A) h).symm x i).2

public lemma CFSG.projection_of_mem (i : ι) (x : M) (hx : x ∈ A i) : projection A h i x = x := by
  rw [projection_apply]
  have := h.ofBijective_coeLinearMap_of_mem hx
  simp_rw [← Subtype.coe_inj] at this
  exact this

public lemma CFSG.projection_of_mem_ne (i j : ι) (hij : i ≠ j) (x : M) (hx : x ∈ A i) :
    projection A h j x = 0 := by
  rw [projection_apply]
  have := h.ofBijective_coeLinearMap_of_mem_ne hij hx
  simp [this]

public lemma CFSG.submodule_eq_bot_of_eq_of_ne (i j : ι) (h' : DirectSum.IsInternal A) (hij : i ≠ j) (h_eq : A i = A j) : A i = ⊥ := by
  have h_disj := h'.submodule_iSupIndep.pairwiseDisjoint hij
  dsimp [Function.onFun] at h_disj
  rw [h_eq] at h_disj
  have h_bot : A j = ⊥ := h_disj.eq_bot_of_self
  exact h_eq.symm ▸ h_bot

variable [Fintype ι]

lemma CFSG.coeLinearMap_apply (v : ⨁ i, A i) : coeLinearMap A v = ∑ i : ι, (v i).val := by
  classical
  simp only [coeLinearMap, toModule, DFinsupp.lsum, LinearEquiv.coe_mk, coe_mk, AddHom.coe_mk]
  show (DFinsupp.sumAddHom fun i ↦ (A i).subtype.toAddMonoidHom) v = ∑ x, (v x)
  rw [DFinsupp.sumAddHom_apply]
  simp_all only [toAddMonoidHom_coe, Submodule.coe_subtype, ZeroMemClass.coe_zero, implies_true, DFinsupp.sum_eq_sum_fintype, DFinsupp.equivFunOnFintype_apply]


lemma CFSG.sum_projection_id : ∑ i : ι, projection A h i = LinearMap.id := by
  ext x
  classical
  calc
    (∑ i : ι, projection A h i) x = ∑ i : ι, projection A h i x := by simp [LinearMap.sum_apply]
    _ = ∑ i : ι, ((LinearEquiv.ofBijective (coeLinearMap A) h).symm x i).val := by simp [projection_apply]
    _ = coeLinearMap A ((LinearEquiv.ofBijective (coeLinearMap A) h).symm x) := by
      rw [coeLinearMap_apply]
    _ = x := by
      exact LinearEquiv.apply_symm_apply (LinearEquiv.ofBijective (coeLinearMap A) h) x

end Projections

open DirectSum LinearMap
open CompleteLattice



/-- The `(i,t)` block component of an endomorphism with respect to the internal
decomposition `A`. -/
@[expose]
public noncomputable def CFSG.blockComponent (T : Module.End R M) (i t : ι) : Module.End R M :=
  projection A h t ∘ₗ T ∘ₗ projection A h i

public lemma CFSG.blockComponent_apply (T : Module.End R M) (i t : ι) (x : M) :
    blockComponent A h T i t x = projection A h t (T (projection A h i x)) := rfl

noncomputable def CFSG.blockComponentLinear (i t : ι) : Module.End R (Module.End R M) :=
  { toFun := fun T => blockComponent A h T i t
    map_add' := by
      intro T U
      ext x
      simp [blockComponent_apply, LinearMap.add_apply]
    map_smul' := by
      intro r T
      ext x
      simp [blockComponent_apply, LinearMap.smul_apply] }

public lemma CFSG.blockComponent_mem_blockElementaryMap (T : Module.End R M) (i t : ι) :
    blockComponent A h T i t ∈ blockElementaryMap A i t := by
  rw [mem_blockElementaryMap_iff A h i t]
  constructor
  · intro v hv
    rw [blockComponent_apply]
    exact projection_maps_to A h t (T (projection A h i v))
  · intro j hneq v hv
    rw [blockComponent_apply]
    have hij : j ≠ i := by
      intro hji
      apply hneq
      simp [hji]
    have hproj : projection A h i v = 0 := projection_of_mem_ne A h j i hij v hv
    rw [hproj, map_zero, map_zero]

public lemma CFSG.blockComponent_of_mem [Fintype ι] (i t : ι) (X : Module.End R M) (hX : X ∈ blockElementaryMap A i t) :
    blockComponent A h X i t = X := by
  classical
  rcases (mem_blockElementaryMap_iff A h i t X).mp hX with ⟨hX₁, hX₂⟩
  ext x
  have hx : x = ∑ j : ι, projection A h j x := by
    rw [← LinearMap.sum_apply, sum_projection_id A h, LinearMap.id_apply]
  have hsum : X x = ∑ j : ι, X (projection A h j x) := by
    calc
      X x = X (∑ j : ι, projection A h j x) := by
        nth_rw 1 [hx]
      _ = ∑ j : ι, X (projection A h j x) := by rw [map_sum]
  have hzero_of_ne {j : ι} (hj : j ≠ i) : X (projection A h j x) = 0 := by
    by_cases hEq : A j = A i
    · have hBot : A i = ⊥ :=
        submodule_eq_bot_of_eq_of_ne (A := A) (h' := h) (i := i) (j := j) hj.symm hEq.symm
      have hmem : projection A h j x ∈ A i := by
        rw [← hEq]
        exact projection_maps_to A h j x
      rw [hBot, Submodule.mem_bot] at hmem
      simp [hmem]
    · exact hX₂ j hEq (projection A h j x) (projection_maps_to A h j x)
  have hsum' : X x = X (projection A h i x) := by
    calc
      X x = ∑ j : ι, X (projection A h j x) := hsum
      _ = X (projection A h i x) := by
        refine Finset.sum_eq_single i ?_ ?_
        · intro j _ hj
          exact hzero_of_ne hj
        · simp
  rw [blockComponent_apply, hsum']
  exact projection_of_mem A h t _ (hX₁ _ (projection_maps_to A h i x))

lemma CFSG.blockComponent_of_mem_ne (i t i' t' : ι) (hi_disj : i ≠ i' ∨ t ≠ t') (X : Module.End R M) (hX : X ∈ blockElementaryMap A i t) :
    blockComponent A h X i' t' = 0 := by
  rcases (mem_blockElementaryMap_iff A h i t X).mp hX with ⟨h1, h2⟩
  rcases hi_disj with hi | hi_t
  · -- case i ≠ i'
    ext x
    rw [blockComponent_apply, LinearMap.zero_apply]
    by_cases h_eq : A i' = A i
    · have h_bot : A i = ⊥ := submodule_eq_bot_of_eq_of_ne (h' := h) (hij := hi) (h_eq := h_eq.symm)
      have hproj_zero : projection A h i' x = 0 := by
        have hmem' : projection A h i' x ∈ A i' := projection_maps_to A h i' x
        rw [h_eq] at hmem' -- now in A i
        rw [h_bot] at hmem' -- now in ⊥
        exact ((Submodule.mem_bot (R := R) (M := M)).mp hmem')
      rw [hproj_zero, map_zero, map_zero]
    · have hzero : X (projection A h i' x) = 0 :=
        h2 i' h_eq (projection A h i' x) (projection_maps_to A h i' x)
      rw [hzero, map_zero]
  · -- case t ≠ t'
    ext x
    rw [blockComponent_apply, LinearMap.zero_apply]
    by_cases hi' : i' = i
    · have hi_eq : i' = i := hi'
      have hmem' : projection A h i' x ∈ A i := by
        rw [hi_eq]
        exact projection_maps_to A h i x
      have hmem : X (projection A h i' x) ∈ A t :=
        h1 (projection A h i' x) hmem'
      exact projection_of_mem_ne A h t t' hi_t (X (projection A h i' x)) hmem
    · by_cases h_eq : A i' = A i
      · have h_bot : A i = ⊥ := submodule_eq_bot_of_eq_of_ne (h' := h) (hij := Ne.symm hi') (h_eq := h_eq.symm)
        have hproj_zero : projection A h i' x = 0 := by
          have hmem' : projection A h i' x ∈ A i' := projection_maps_to A h i' x
          rw [h_eq] at hmem' -- now in A i
          rw [h_bot] at hmem' -- now in ⊥
          exact ((Submodule.mem_bot (R := R) (M := M)).mp hmem')
        rw [hproj_zero, map_zero, map_zero]
      · have hzero : X (projection A h i' x) = 0 :=
          h2 i' h_eq (projection A h i' x) (projection_maps_to A h i' x)
        rw [hzero, map_zero]

lemma CFSG.blockComponent_of_mem_ne' (it it' : ι × ι) (hne : it ≠ it') (X : Module.End R M)
    (hX : X ∈ blockElementaryMap A it.1 it.2) : blockComponent A h X it'.1 it'.2 = 0 := by
  by_cases h_left : it.1 = it'.1
  · have h_right : it.2 ≠ it'.2 := by
      intro h_eq
      exact hne (Prod.ext h_left h_eq)
    exact blockComponent_of_mem_ne A h it.1 it.2 it'.1 it'.2 (Or.inr h_right) X hX
  · exact blockComponent_of_mem_ne A h it.1 it.2 it'.1 it'.2 (Or.inl h_left) X hX

variable [Fintype ι]

public lemma CFSG.blockElementaryMap_iSupIndep (h : DirectSum.IsInternal A) : iSupIndep (fun (it : ι × ι) => blockElementaryMap A it.1 it.2) := by
  intro it0
  let N := LinearMap.ker (blockComponentLinear A h it0.1 it0.2)
  have hN : ∀ (x : Σ' j : ι × ι, j ≠ it0), blockElementaryMap A x.1.1 x.1.2 ≤ N := by
    intro x X hX
    have hne : x.1 ≠ it0 := x.2
    have hzero := blockComponent_of_mem_ne' A h x.1 it0 hne X hX
    simp [N, blockComponentLinear, LinearMap.mem_ker, hzero]
  have hN'' : ∀ (j : ι × ι), (⨆ (h : j ≠ it0), blockElementaryMap A j.1 j.2) ≤ N := by
    intro j
    refine iSup_le ?_
    intro h
    exact hN ⟨j, h⟩
  refine Submodule.disjoint_def.mpr fun X hX_left hX_right => ?_
  have hX_N := (Submodule.mem_iSup (p := fun (j : ι × ι) => ⨆ (h : j ≠ it0), blockElementaryMap A j.1 j.2)).mp hX_right N hN''
  rw [LinearMap.mem_ker] at hX_N
  have h_zero : blockComponent A h X it0.1 it0.2 = 0 := by
    simpa [blockComponentLinear] using hX_N
  have h_self := blockComponent_of_mem A h it0.1 it0.2 X hX_left
  calc
    X = blockComponent A h X it0.1 it0.2 := h_self.symm
    _ = 0 := h_zero

public lemma CFSG.decompose_endomorphism (T : Module.End R M) : T = ∑ i : ι, ∑ t : ι, blockComponent A h T i t := by
  classical
  ext x
  have hx_sum : x = ∑ i : ι, projection A h i x := by
    rw [← LinearMap.sum_apply, sum_projection_id A h, LinearMap.id_apply]
  calc
    T x = T (∑ i : ι, projection A h i x) := by
      conv_lhs => rw [hx_sum]
    _ = ∑ i : ι, T (projection A h i x) := by rw [map_sum]
    _ = ∑ i : ι, (∑ t : ι, projection A h t) (T (projection A h i x)) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [sum_projection_id A h, LinearMap.id_apply]
    _ = ∑ i : ι, ∑ t : ι, projection A h t (T (projection A h i x)) := by
      simp [LinearMap.sum_apply]
    _ = ∑ i : ι, ∑ t : ι, blockComponent A h T i t x := by
      simp [blockComponent_apply]
    _ = (∑ i : ι, ∑ t : ι, blockComponent A h T i t) x := by
      simp [LinearMap.sum_apply]

public lemma CFSG.blockElementaryMap_iSup_eq_top (h : DirectSum.IsInternal A) : ⨆ it : ι × ι, blockElementaryMap A it.1 it.2 = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro T
  have h_decomp := decompose_endomorphism A h T
  have h_sum_mem : (∑ i : ι, ∑ t : ι, blockComponent A h T i t) ∈ ⨆ it : ι × ι, blockElementaryMap A it.1 it.2 := by
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun t _ => ?_
    have hmem := blockComponent_mem_blockElementaryMap A h T i t
    have h_le : blockElementaryMap A i t ≤ ⨆ it : ι × ι, blockElementaryMap A it.1 it.2 :=
      le_iSup (fun it : ι × ι => blockElementaryMap A it.1 it.2) (i, t)
    exact h_le hmem
  rw [← h_decomp] at h_sum_mem
  exact h_sum_mem

public lemma CFSG.isInternal_blockElementaryMap (h : DirectSum.IsInternal A) : DirectSum.IsInternal (fun (it : ι × ι) => blockElementaryMap A it.1 it.2) := by
  refine (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top (R := R) (ι := ι × ι) (M := Module.End R M) (A := fun (it : ι × ι) => blockElementaryMap A it.1 it.2)).mpr ?_
  exact ⟨blockElementaryMap_iSupIndep A h, blockElementaryMap_iSup_eq_top A h⟩

end BlockDecomposition

open scoped DirectSum in
/-- The canonical identification between `(i,t)` block maps and linear maps from
the `i`-block to the `t`-block. -/
@[expose]
public noncomputable def CFSG.blockElementaryMap_iso
    {R : Type*} [Field R]
    {M : Type*} [AddCommGroup M] [Module R M]
    {ι : Type*} [DecidableEq ι] [Fintype ι] (A : ι → Submodule R M) (hA : DirectSum.IsInternal A)
    (i : ι) (t : ι) :
    blockElementaryMap A i t ≃ₗ[R] (A i) →ₗ[R] (A t) := by
  let f : blockElementaryMap A i t →ₗ[R] (A i) →ₗ[R] (A t) := {
    toFun := fun X ↦ {
      toFun := fun x ↦ ⟨X.1 x.1, by
        have hX := X.2
        simp only [blockElementaryMap, ne_eq, Submodule.mem_mk, AddSubmonoid.mem_mk,
          AddSubsemigroup.mem_mk, Set.mem_ofPred_eq] at hX
        exact hX.1 x.1 x.2⟩
      map_add' := by simp
      map_smul' := by simp
    }
    map_add' := by
      intro x y
      ext z
      simp
    map_smul' := by
      intro r x
      ext z
      simp
  }
  have hf : Function.Injective f := by
    intro x y h
    subst f
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.mk.injEq, AddHom.mk.injEq] at h
    have hxy_on (z : A i) : x.val z = y.val z := by
      have hz := congrFun h z
      rw [Subtype.mk.injEq] at hz
      exact hz
    ext z
    rcases (mem_blockElementaryMap_iff A hA i t x.val).mp x.2 with ⟨hx1, _⟩
    rcases (mem_blockElementaryMap_iff A hA i t y.val).mp y.2 with ⟨hy1, _⟩
    have hxz : x.val z = x.val (projection A hA i z) := by
      have hxcomp := congrArg (fun T => T z) (blockComponent_of_mem A hA i t x.val x.2)
      simpa [blockComponent_apply,
        projection_of_mem A hA t _ (hx1 _ (projection_maps_to A hA i z))] using hxcomp.symm
    have hyz : y.val z = y.val (projection A hA i z) := by
      have hycomp := congrArg (fun T => T z) (blockComponent_of_mem A hA i t y.val y.2)
      simpa [blockComponent_apply,
        projection_of_mem A hA t _ (hy1 _ (projection_maps_to A hA i z))] using hycomp.symm
    have hxy : x.val (projection A hA i z) = y.val (projection A hA i z) := by
      let zi : A i := ⟨projection A hA i z, projection_maps_to A hA i z⟩
      simpa [zi] using hxy_on zi
    exact hxz.trans (hxy.trans hyz.symm)
  have hf_surj : Function.Surjective f := by
    intro X
    let c := LinearEquiv.ofBijective (DirectSum.coeLinearMap A) hA
    let d : (⨁ j : ι, A j) →ₗ[R] M :=
      DirectSum.toModule R ι M fun j ↦
        if h : j = i then (by rw [h]; exact (A t).subtype.comp X) else 0
    refine ⟨⟨d.comp c.symm.toLinearMap, ?_⟩, ?_⟩
    · rw [mem_blockElementaryMap_iff A hA i t]
      constructor
      · intro v hv
        have hv' : c.symm v = DirectSum.lof R ι (fun j ↦ A j) i ⟨v, hv⟩ := by
          ext j
          by_cases hij : i = j
          · subst hij
            simpa [c] using
              congrArg Subtype.val (hA.ofBijective_coeLinearMap_of_mem (i := i) (x := v) hv)
          · have hleft : c.symm v j = 0 := by
              simpa [c] using
                hA.ofBijective_coeLinearMap_of_mem_ne (i := i) (j := j) hij (x := v) hv
            have hright : (DirectSum.lof R ι (fun j ↦ A j) i ⟨v, hv⟩) j = 0 := by
              rw [DirectSum.lof_eq_of]
              exact DirectSum.of_eq_of_ne _ _ _ (fun h => hij h.symm)
            rw [hleft, hright]
        change d (c.symm v) ∈ A t
        rw [hv']
        simp [d]
      · intro j hj v hv
        have hij : j ≠ i := by
          intro hji
          apply hj
          simp [hji]
        have hv' : c.symm v = DirectSum.lof R ι (fun k ↦ A k) j ⟨v, hv⟩ := by
          ext k
          by_cases hjk : j = k
          · subst hjk
            simpa [c] using
              congrArg Subtype.val (hA.ofBijective_coeLinearMap_of_mem (i := j) (x := v) hv)
          · have hleft : c.symm v k = 0 := by
              simpa [c] using
                hA.ofBijective_coeLinearMap_of_mem_ne (i := j) (j := k) hjk (x := v) hv
            have hright : (DirectSum.lof R ι (fun k ↦ A k) j ⟨v, hv⟩) k = 0 := by
              rw [DirectSum.lof_eq_of]
              exact DirectSum.of_eq_of_ne _ _ _ (fun h => hjk h.symm)
            rw [hleft, hright]
        change d (c.symm v) = 0
        rw [hv']
        simp [d, hij]
    · ext x
      have hx' : c.symm x.1 = DirectSum.lof R ι (fun j ↦ A j) i x := by
        ext j
        by_cases hij : i = j
        · subst hij
          simp [c]
        · have hleft : c.symm x.1 j = 0 := by
            simpa [c] using hA.ofBijective_coeLinearMap_of_ne (i := i) (j := j) hij x
          have hright : (DirectSum.lof R ι (fun j ↦ A j) i x) j = 0 := by
            rw [DirectSum.lof_eq_of]
            exact DirectSum.of_eq_of_ne _ _ _ (fun h => hij h.symm)
          rw [hleft, hright]
      change d (c.symm x.1) = (X x).1
      rw [hx']
      simp [d]
  exact LinearEquiv.ofBijective f ⟨hf, hf_surj⟩

open Module in
public theorem CFSG.blockElementaryMap_finrank
    {R : Type*} [Field R]
    {M : Type*} [AddCommGroup M] [Module R M] [FiniteDimensional R M]
    {ι : Type*} [DecidableEq ι] [Fintype ι] (A : ι → Submodule R M) (hA : DirectSum.IsInternal A)
    (i : ι) (t : ι) :
    finrank R (blockElementaryMap A i t) = finrank R (A i) * finrank R (A t) := by
  rw [LinearEquiv.finrank_eq (blockElementaryMap_iso _ hA _ _), Module.finrank_linearMap]
