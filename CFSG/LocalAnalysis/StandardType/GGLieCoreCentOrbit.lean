module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreCent
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcToral
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcLang.Family
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.C14Lattice
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open Matrix
open CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open scoped commutatorElement

private theorem ggLieCentOrbit_jointChar_apply {τ : Tag} {L : Type} [Field L]
    (a₁ a₂ : Fin τ.rank → Lˣ) (v : Multiplicative (Fin τ.rank → ℤ)) :
    jointChar a₁ a₂ v = (rootChar a₁ (Multiplicative.toAdd v),
      rootChar a₂ (Multiplicative.toAdd v)) := rfl

private theorem ggLieCentOrbit_familyKernel_pair {τ : Tag} {L : Type} [Field L]
    (a₁ a₂ : Fin τ.rank → Lˣ) :
    familyKernel ![a₁, a₂] = kernelRoots (jointChar a₁ a₂) := by
  ext α
  simp only [familyKernel, kernelRoots, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hroot, hα⟩
    have h0 := hα 0
    have h1 := hα 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    refine ⟨hroot, ?_⟩
    rw [ggLieCentOrbit_jointChar_apply, Prod.mk_eq_one]
    exact ⟨h0, h1⟩
  · rintro ⟨hroot, hα⟩
    refine ⟨hroot, fun i => ?_⟩
    have hα' := (Prod.mk_eq_one.1 ((ggLieCentOrbit_jointChar_apply a₁ a₂
      (Multiplicative.ofAdd α)).symm.trans hα))
    fin_cases i
    · show rootChar a₁ (Multiplicative.toAdd (Multiplicative.ofAdd α)) = 1
      exact hα'.1
    · show rootChar a₂ (Multiplicative.toAdd (Multiplicative.ofAdd α)) = 1
      exact hα'.2

private theorem ggLieCentOrbit_familyCentralizer_pair {τ : Tag} {L : Type} [Field L]
    (a₁ a₂ : Fin τ.rank → Lˣ) :
    familyCentralizer τ L ![a₁, a₂] = adjointGroup τ L ⊓
      Subgroup.centralizer ((Subgroup.closure {rootDiagUnit τ a₁, rootDiagUnit τ a₂} :
        Subgroup (ModGL τ L)) : Set (ModGL τ L)) := by
  ext g
  rw [mem_familyCentralizer]
  simp only [Subgroup.mem_inf, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Subgroup.centralizer_closure]
  constructor
  · rintro ⟨hg, h1, h2⟩
    refine ⟨hg, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact (Subgroup.mem_centralizer_iff.1 (conj_eq_iff_mem_centralizer.1 h1)) _ (by simp)
    · exact (Subgroup.mem_centralizer_iff.1 (conj_eq_iff_mem_centralizer.1 h2)) _ (by simp)
  · rintro ⟨hg, hc⟩
    refine ⟨hg, ?_, ?_⟩
    · exact conj_eq_iff_mem_centralizer.2
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (by simp)) hc)
    · exact conj_eq_iff_mem_centralizer.2
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (by simp)) hc)

private theorem ggLieCentOrbit_familyGroup_normal
    {τ : Tag} {L : Type} [Field L] {ι : Type} (a : ι → Fin τ.rank → Lˣ) :
    ((familyGroup (K := L) a).subgroupOf (familyCentralizer τ L a)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (familyGroup_le_familyCentralizer a)]
  intro x g hx hg
  obtain ⟨w, hw, m, hm, rfl⟩ := familyCentralizer_le_mul τ L a hg
  have hnorm := canonicalRep_mem_normalizer_familyGroup (K := L) (a := a) hw
  have h1 : canonicalRep (coxeterSystem τ) L w * x *
      (canonicalRep (coxeterSystem τ) L w)⁻¹ ∈ familyGroup (K := L) a :=
    (Subgroup.mem_normalizer_iff.1 hnorm x).1 hx
  have hgoal : (m * canonicalRep (coxeterSystem τ) L w) * x *
      (m * canonicalRep (coxeterSystem τ) L w)⁻¹ =
      m * (canonicalRep (coxeterSystem τ) L w * x *
        (canonicalRep (coxeterSystem τ) L w)⁻¹) * m⁻¹ := by group
  rw [hgoal]
  exact mul_mem (mul_mem hm h1) (inv_mem hm)

private theorem ggLieCentOrbit_rootsTrivialOn_pair {τ : Tag} {L : Type} [Field L]
    (a₁ a₂ : Fin τ.rank → Lˣ) :
    rootsTrivialOn (Subgroup.closure {rootDiagUnit τ a₁, rootDiagUnit τ a₂}) =
      kernelRoots (jointChar a₁ a₂) := by
  ext γ
  rw [rootsTrivialOn, kernelRoots]
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    rw [ggLieCentOrbit_jointChar_apply, Prod.mk_eq_one]
    exact ⟨h.2 a₁ (Subgroup.subset_closure (by simp)),
           h.2 a₂ (Subgroup.subset_closure (by simp))⟩
  · rintro ⟨hroot, hχ⟩
    rw [ggLieCentOrbit_jointChar_apply, Prod.mk_eq_one] at hχ
    obtain ⟨h1, h2⟩ := hχ
    refine ⟨hroot, ?_⟩
    intro a ha
    have hmap : (Subgroup.closure {rootDiagUnit τ a₁, rootDiagUnit τ a₂} :
        Subgroup (ModGL τ L)) = (Subgroup.closure {a₁, a₂}).map (rootDiagUnitHom τ L) := by
      rw [MonoidHom.map_closure]
      congr 1
      rw [Set.image_insert_eq, Set.image_singleton]
      rfl
    have hmem : rootDiagUnit τ a ∈ (Subgroup.closure {a₁, a₂}).map (rootDiagUnitHom τ L) :=
      hmap ▸ ha
    obtain ⟨b, hb, hba⟩ := hmem
    have hba' : b = a := rootDiagUnit_injective hba
    subst hba'
    let ψ : (Fin τ.rank → Lˣ) →* Lˣ :=
      { toFun := fun x => rootChar x γ
        map_one' := by simp [rootChar]
        map_mul' := fun x y => by
          simp only [Pi.mul_apply, rootChar]
          rw [← Finset.prod_mul_distrib]
          exact Finset.prod_congr rfl fun i _ => by rw [mul_zpow] }
    have hker : Subgroup.closure ({a₁, a₂} : Set (Fin τ.rank → Lˣ)) ≤ ψ.ker := by
      refine (Subgroup.closure_le _).2 ?_
      rintro x (rfl | rfl)
      · simpa [ψ] using h1
      · simpa [ψ] using h2
    simpa [ψ] using hker hb

private def ggLieCentOrbit_orbitRoots {τ : Tag} {M : Type*} [CommGroup M]
    (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (i : KernelComponent χ) :
    Set (Fin τ.rank → ℤ) :=
  {γ | ∃ (k : ℕ) (δ : Fin τ.rank → ℤ), δ ∈ componentRoots χ i ∧
    γ = (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k] δ}

private theorem ggLieCentOrbit_orbitRoots_mapsTo {τ : Tag} {M : Type*} [CommGroup M]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (i : KernelComponent χ) :
    Set.MapsTo (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))
      (ggLieCentOrbit_orbitRoots ρ χ i) (ggLieCentOrbit_orbitRoots ρ χ i) := by
  rintro _ ⟨k, δ, hδ, rfl⟩
  exact ⟨k + 1, δ, hδ, by rw [Function.iterate_succ_apply']⟩

private theorem ggLieCentOrbit_iterate_mem_kernelRoots {τ : Tag} {M : Type*} [CommGroup M]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ) (k : ℕ) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ kernelRoots χ) :
    (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k] γ ∈ kernelRoots χ := by
  induction k with
  | zero => exact hγ
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact hker _ ih

private theorem ggLieCentOrbit_orbitRoots_subset_kernelRoots {τ : Tag} {M : Type*} [CommGroup M]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ) (i : KernelComponent χ) :
    ggLieCentOrbit_orbitRoots ρ χ i ⊆ kernelRoots χ := by
  rintro _ ⟨k, δ, ⟨hδ, -⟩, rfl⟩
  exact ggLieCentOrbit_iterate_mem_kernelRoots hker k hδ

private theorem ggLieCentOrbit_eqvGen_map {X : Type*} {r : X → X → Prop} (f : X → X)
    (hf : ∀ x y, r x y → r (f x) (f y)) {x y : X} (h : Relation.EqvGen r x y) :
    Relation.EqvGen r (f x) (f y) := by
  induction h with
  | rel x y h => exact .rel _ _ (hf x y h)
  | refl x => exact .refl _
  | symm x y _ ih => exact .symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact .trans _ _ _ ih1 ih2

private theorem ggLieCentOrbit_eqvGen_equiv_iff {X : Type*} {r : X → X → Prop} (e : X ≃ X)
    (hr : ∀ x y, r (e x) (e y) ↔ r x y) (x y : X) :
    Relation.EqvGen r (e x) (e y) ↔ Relation.EqvGen r x y := by
  refine ⟨fun h => ?_, ggLieCentOrbit_eqvGen_map e fun x y h => (hr x y).2 h⟩
  have := ggLieCentOrbit_eqvGen_map e.symm
    (fun a b h => (hr (e.symm a) (e.symm b)).1 (by simpa using h)) h
  simpa using this

private theorem ggLieCentOrbit_iform_iterate {τ : Tag} {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    (hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ) (k : ℕ) (x y : Fin τ.rank → ℤ) :
    iform ((ρ : (Fin τ.rank → ℤ) → _)^[k] x) ((ρ : (Fin τ.rank → ℤ) → _)^[k] y) =
      iform x y := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, hform]

open Matrix in
private theorem ggLieCentOrbit_kernelComponent_eq_iff {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (x y : kernelRoots χ) :
    (⟦x⟧ : KernelComponent χ) = ⟦y⟧ ↔ Relation.EqvGen
      (fun α β : kernelRoots χ =>
        (α : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (β : Fin τ.rank → ℤ)) ≠ 0) x y :=
  Quotient.eq (r := kernelRootSetoid χ)

open Matrix in
private theorem ggLieCentOrbit_orbitRoots_closed
    {τ : Tag} {M : Type*} [CommGroup M]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ) (i : KernelComponent χ)
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ ggLieCentOrbit_orbitRoots ρ χ i) {β : Fin τ.rank → ℤ}
    (hβ : β ∈ kernelRoots χ)
    (h : (⟦⟨β, hβ⟩⟧ : KernelComponent χ) =
      ⟦⟨γ, ggLieCentOrbit_orbitRoots_subset_kernelRoots hker i hγ⟩⟧) :
    β ∈ ggLieCentOrbit_orbitRoots ρ χ i := by
  classical
  have hfin : (kernelRoots χ).Finite := (finite_setOf_isRoot τ).subset fun α h => h.1
  have : Finite (kernelRoots χ) := hfin.to_subtype
  let σ : kernelRoots χ → kernelRoots χ := fun x => ⟨ρ x, hker x x.2⟩
  have hσinj : Function.Injective σ := fun x y h =>
    Subtype.ext (ρ.injective (congrArg Subtype.val h))
  let e : Equiv.Perm (kernelRoots χ) := Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hσinj)
  have he_iter : ∀ (k : ℕ) (x : kernelRoots χ),
      (((e ^ k) x : kernelRoots χ) : Fin τ.rank → ℤ) = (ρ : (Fin τ.rank → ℤ) → _)^[k] x := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ', Equiv.Perm.mul_apply]
      show ρ (((e ^ k) x : kernelRoots χ) : Fin τ.rank → ℤ) = _
      rw [ih, Function.iterate_succ_apply']
  have hr : ∀ (k : ℕ) (x y : kernelRoots χ),
      (((e ^ k) x : kernelRoots χ) : Fin τ.rank → ℤ) ⬝ᵥ
          (τ.symmetrizedCartan *ᵥ (((e ^ k) y : kernelRoots χ) : Fin τ.rank → ℤ)) ≠ 0 ↔
        (x : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (y : Fin τ.rank → ℤ)) ≠ 0 := by
    intro k x y
    rw [dotProduct_mulVec_eq_iform, dotProduct_mulVec_eq_iform, he_iter, he_iter,
      ggLieCentOrbit_iform_iterate hform]
  obtain ⟨k, δ, ⟨hδ, hδi⟩, rfl⟩ := hγ
  set y : kernelRoots χ := (e ^ k)⁻¹ ⟨β, hβ⟩ with hy
  have hey : (e ^ k) y = ⟨β, hβ⟩ := by simp [hy]
  have hex : (e ^ k) ⟨δ, hδ⟩ =
      ⟨(ρ : (Fin τ.rank → ℤ) → _)^[k] δ, ggLieCentOrbit_iterate_mem_kernelRoots hker k hδ⟩ :=
    Subtype.ext (he_iter k ⟨δ, hδ⟩)
  have hyx : (⟦y⟧ : KernelComponent χ) = ⟦⟨δ, hδ⟩⟧ := by
    rw [ggLieCentOrbit_kernelComponent_eq_iff]
    refine (ggLieCentOrbit_eqvGen_equiv_iff (e ^ k) (hr k) y ⟨δ, hδ⟩).1 ?_
    rw [hey, hex]
    exact (ggLieCentOrbit_kernelComponent_eq_iff _ _).1 h
  refine ⟨k, y, ⟨y.2, hyx.trans hδi⟩, ?_⟩
  have := congrArg Subtype.val hey
  rw [he_iter] at this
  exact this.symm

private theorem ggLieCentOrbit_orbitRoots_of_apply_mem {τ : Tag}
    {M : Type*} [CommGroup M] {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (i : KernelComponent χ) {δ : Fin τ.rank → ℤ} (h : ρ δ ∈ ggLieCentOrbit_orbitRoots ρ χ i) :
    δ ∈ ggLieCentOrbit_orbitRoots ρ χ i := by
  have hfin : (ggLieCentOrbit_orbitRoots ρ χ i).Finite :=
    ((finite_setOf_isRoot τ).subset fun α hα => hα.1 : (kernelRoots χ).Finite).subset
      (ggLieCentOrbit_orbitRoots_subset_kernelRoots hker i)
  have hbij := (hfin.injOn_iff_bijOn_of_mapsTo (ggLieCentOrbit_orbitRoots_mapsTo i)).1
    ρ.injective.injOn
  obtain ⟨γ, hγ, hγδ⟩ := hbij.surjOn h
  exact ρ.injective hγδ ▸ hγ

private theorem ggLieCentOrbit_orbitRoots_of_iterate_mem {τ : Tag}
    {M : Type*} [CommGroup M] {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (i : KernelComponent χ) (n : ℕ) {δ : Fin τ.rank → ℤ}
    (h : (ρ : (Fin τ.rank → ℤ) → _)^[n] δ ∈ ggLieCentOrbit_orbitRoots ρ χ i) :
    δ ∈ ggLieCentOrbit_orbitRoots ρ χ i := by
  induction n generalizing δ with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h
    exact ggLieCentOrbit_orbitRoots_of_apply_mem hker i (ih h)

private theorem ggLieCentOrbit_iterate_mem_orbitRoots {τ : Tag} {M : Type*} [CommGroup M]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (i : KernelComponent χ) (n : ℕ) {γ : Fin τ.rank → ℤ}
    (h : γ ∈ ggLieCentOrbit_orbitRoots ρ χ i) :
    (ρ : (Fin τ.rank → ℤ) → _)^[n] γ ∈ ggLieCentOrbit_orbitRoots ρ χ i := by
  obtain ⟨k, δ, hδ, rfl⟩ := h
  exact ⟨n + k, δ, hδ, by rw [Function.iterate_add_apply]⟩

private theorem ggLieCentOrbit_orbitRoots_subset_of_mem_inter
    {τ : Tag} {M : Type*} [CommGroup M] {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ) {i j : KernelComponent χ}
    {δ : Fin τ.rank → ℤ} (hi : δ ∈ ggLieCentOrbit_orbitRoots ρ χ i)
    (hj : δ ∈ ggLieCentOrbit_orbitRoots ρ χ j) :
    ggLieCentOrbit_orbitRoots ρ χ j ⊆ ggLieCentOrbit_orbitRoots ρ χ i := by
  obtain ⟨n, δ₂, ⟨hδ₂, hδ₂j⟩, rfl⟩ := hj
  have hδ₂i : δ₂ ∈ ggLieCentOrbit_orbitRoots ρ χ i :=
    ggLieCentOrbit_orbitRoots_of_iterate_mem hker i n hi
  rintro _ ⟨l, ε₂, ⟨hε₂, hε₂j⟩, rfl⟩
  exact ggLieCentOrbit_iterate_mem_orbitRoots i l
    (ggLieCentOrbit_orbitRoots_closed hker hform i hδ₂i hε₂ (hε₂j.trans hδ₂j.symm))

private theorem ggLieCentOrbit_orbitRoots_eq_of_mem_inter {τ : Tag}
    {M : Type*} [CommGroup M] {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ) {i j : KernelComponent χ}
    {δ : Fin τ.rank → ℤ} (hi : δ ∈ ggLieCentOrbit_orbitRoots ρ χ i)
    (hj : δ ∈ ggLieCentOrbit_orbitRoots ρ χ j) :
    ggLieCentOrbit_orbitRoots ρ χ i = ggLieCentOrbit_orbitRoots ρ χ j :=
  le_antisymm (ggLieCentOrbit_orbitRoots_subset_of_mem_inter hker hform hj hi)
    (ggLieCentOrbit_orbitRoots_subset_of_mem_inter hker hform hi hj)

private theorem ggLieCentOrbit_commute_rootSpan_orbitRoots
    {τ : Tag} {L : Type} [Field L] {M : Type*} [CommGroup M]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ) {i j : KernelComponent χ}
    (hij : ggLieCentOrbit_orbitRoots ρ χ i ≠ ggLieCentOrbit_orbitRoots ρ χ j) :
    ∀ x ∈ rootSpan τ L (ggLieCentOrbit_orbitRoots ρ χ i),
      ∀ y ∈ rootSpan τ L (ggLieCentOrbit_orbitRoots ρ χ j), Commute x y := by
  have hle : rootSpan τ L (ggLieCentOrbit_orbitRoots ρ χ i) ≤
      Subgroup.centralizer (rootSpan τ L (ggLieCentOrbit_orbitRoots ρ χ j) :
        Set (ModGL τ L)) := by
    refine iSup₂_le fun γ hγ => ?_
    rw [Subgroup.le_centralizer_iff]
    refine iSup₂_le fun δ hδ => ?_
    rw [Subgroup.le_centralizer_iff]
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hγk := ggLieCentOrbit_orbitRoots_subset_kernelRoots hker i hγ
    have hδk := ggLieCentOrbit_orbitRoots_subset_kernelRoots hker j hδ
    have hne : (⟦⟨γ, hγk⟩⟧ : KernelComponent χ) ≠ ⟦⟨δ, hδk⟩⟧ := fun h =>
      hij (ggLieCentOrbit_orbitRoots_eq_of_mem_inter hker hform
        (ggLieCentOrbit_orbitRoots_closed hker hform i hγ hδk h.symm) hδ)
    exact (commute_of_mk_ne hne L y hy x hx).eq.symm
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.1 (hle hx) y hy).symm

private theorem ggLieCentOrbit_step_mem_rootSpan
    {τ : Tag} {L : Type} [Field L]
    (D : LangDatum τ L) (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (hρ : FrobRootMap D ρ)
    {T : Set (Fin τ.rank → ℤ)} (hT : ∀ γ ∈ T, IsRoot τ γ)
    (hρT : Set.MapsTo (ρ : (Fin τ.rank → ℤ) → _) T T) {x : ModGL τ L}
    (hx : x ∈ rootSpan τ L T) : D.step x ∈ rootSpan τ L T := by
  have h1 : D.step x ∈ (rootSpan τ L T).map D.step := Subgroup.mem_map_of_mem _ hx
  have h2 : (rootSpan τ L T).map D.step =
      rootSpan τ L ((ρ : (Fin τ.rank → ℤ) → _) '' T) := by
    simp only [rootSpan, Subgroup.map_iSup]
    rw [iSup_image]
    exact iSup_congr fun γ => iSup_congr fun hγ => hρ.map_rootSubgroup γ (hT γ hγ)
  rw [h2] at h1
  exact rootSpan_mono hρT.image_subset h1

private theorem ggLieCentOrbit_comp_le_or_commutator_eq_bot {G : Type*} [Group G]
    {X K U : Subgroup G} [Finite ↥X] (hK : IsComponentOf K X) (hU : IsSubnormal U X) :
    K ≤ U ∨ ⁅K, U⁆ = ⊥ := by
  have hUX : U ≤ X := hU.le
  have hK' := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
    hK.1).1 hK
  rcases CFSG.LocalCores.component_subnormal_subgroup hK' hU.subgroupOf with h | h
  · exact Or.inl (CFSG.LocalCores.le_of_subgroupOf_le hK.1 h)
  · right
    have := CFSG.LocalCores.commutator_inf_eq_bot_of_subgroupOf hK.1 h
    rwa [inf_of_le_left hUX] at this

private theorem ggLieCentOrbit_isSubnormal_of_le_of_le' {G : Type*} [Group G] {K C M : Subgroup G}
    (h : IsSubnormal K C) (hKM : K ≤ M) (hMC : M ≤ C) : IsSubnormal K M := by
  have := h.inf M
  rwa [inf_eq_left.2 hKM, inf_eq_right.2 hMC] at this

private theorem ggLieCentOrbit_exists_noncomm_of_isQuasisimple {Q : Type*} [Group Q]
    (hQ : CFSG.Assembly.IsQuasisimple Q) : ∃ a b : Q, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hc : Subgroup.center Q = ⊤ :=
    (Subgroup.eq_top_iff' _).2 fun a => Subgroup.mem_center_iff.2 fun b => h b a
  have := hQ.2.toNontrivial
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  exact hxy (QuotientGroup.eq.2 (by rw [hc]; trivial))

theorem ggLieCentOrbit_perfect_le_rootSpan
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (a₁ a₂ : Fin τ.rank → Lˣ)
    (h₁ : rootDiagUnit τ a₁ ^ p = 1) (h₂ : rootDiagUnit τ a₂ ^ p = 1)
    {P : Subgroup (ModGL τ L)} [Finite P]
    (hP : P ≤ adjointGroup τ L ⊓ Subgroup.centralizer
        ((Subgroup.closure {rootDiagUnit τ a₁, rootDiagUnit τ a₂} : Subgroup (ModGL τ L)) :
          Set (ModGL τ L)))
    (hperf : ⁅P, P⁆ = P) :
    P ≤ rootSpan τ L (kernelRoots (jointChar a₁ a₂)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set C : Subgroup (ModGL τ L) := familyCentralizer τ L ![a₁, a₂] with hC
  set N : Subgroup (ModGL τ L) := familyGroup (K := L) ![a₁, a₂] with hN
  have hPC : P ≤ C := by
    rw [hC, ggLieCentOrbit_familyCentralizer_pair]
    exact hP
  have hNnorm : (N.subgroupOf C).Normal := ggLieCentOrbit_familyGroup_normal _
  have hconn : centConn (Subgroup.closure {rootDiagUnit τ a₁, rootDiagUnit τ a₂}) = N := by
    rw [hN, familyGroup, centConn, ggLieCentOrbit_rootsTrivialOn_pair,
      ← ggLieCentOrbit_familyKernel_pair]
  let φ : C →* C ⧸ N.subgroupOf C := QuotientGroup.mk' (N.subgroupOf C)
  let Q : Subgroup (C ⧸ N.subgroupOf C) := (P.subgroupOf C).map φ
  haveI : Finite ↥(P.subgroupOf C) :=
    Finite.of_injective
      (fun x : ↥(P.subgroupOf C) => (⟨(x.1 : ModGL τ L), Subgroup.mem_subgroupOf.1 x.2⟩ : P))
      (fun a b h => by
        have h' : ((a.1 : C) : ModGL τ L) = ((b.1 : C) : ModGL τ L) :=
          congrArg (fun z : P => (z : ModGL τ L)) h
        exact Subtype.ext (Subtype.ext h'))
  haveI : Finite ↥Q :=
    Finite.of_surjective
      (fun x : ↥(P.subgroupOf C) => (⟨φ x, Subgroup.mem_map_of_mem φ x.2⟩ : Q))
      (fun q => by
        obtain ⟨x, hx, hxq⟩ := Subgroup.mem_map.1 q.2
        exact ⟨⟨x, hx⟩, Subtype.ext hxq⟩)
  have hPGroup : IsPGroup p Q := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro g
    obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.1 g.2
    have hyP : (y : ModGL τ L) ∈ P := Subgroup.mem_subgroupOf.1 hy
    obtain ⟨k, hk⟩ := ggLieCentStructure_pow_mem hp hp2 a₁ a₂ h₁ h₂ (y : ModGL τ L)
      (hP hyP)
    have hkN : (y : ModGL τ L) ^ p ^ k ∈ N := hconn ▸ hk
    refine ⟨k, ?_⟩
    apply Subtype.ext
    show (g : C ⧸ N.subgroupOf C) ^ p ^ k = 1
    rw [← hyg, ← map_pow]
    exact MonoidHom.mem_ker.1 (by
      rw [show φ.ker = N.subgroupOf C from QuotientGroup.ker_mk' (N.subgroupOf C)]
      exact Subgroup.mem_subgroupOf.2 hkN)
  have hperf_sub : ⁅P.subgroupOf C, P.subgroupOf C⁆ = P.subgroupOf C := by
    apply Subgroup.map_injective (f := C.subtype) Subtype.coe_injective
    have hmap : (P.subgroupOf C).map C.subtype = P := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hPC]
    rw [Subgroup.map_commutator, hmap, hperf]
  have hperfQ : Group.IsPerfect Q := by
    have hsub : Group.IsPerfect ↥(P.subgroupOf C) := Subgroup.isPerfect_iff.2 hperf_sub
    have := Group.IsPerfect.map (f := φ) (H := P.subgroupOf C)
    simpa only [Q] using this
  have hsolv : Group.IsSolvable Q := by
    haveI : Group.IsNilpotent Q := IsPGroup.isNilpotent hPGroup
    exact IsNilpotent.to_isSolvable
  have hQbot : Q = ⊥ := by
    haveI : Subsingleton Q := by
      by_contra h
      rw [not_subsingleton_iff_nontrivial] at h
      haveI : Nontrivial Q := h
      exact Group.IsPerfect.not_isSolvable (G := Q) hsolv
    exact Subgroup.eq_bot_of_subsingleton Q
  have hle : P.subgroupOf C ≤ N.subgroupOf C := by
    have hmapbot : (P.subgroupOf C).map φ = ⊥ := by simpa only [Q] using hQbot
    have := (Subgroup.map_eq_bot_iff (P.subgroupOf C)).1 hmapbot
    rwa [show φ.ker = N.subgroupOf C from QuotientGroup.ker_mk' (N.subgroupOf C)] at this
  have hPN : P ≤ N := by
    intro x hx
    have hxC : x ∈ C := hPC hx
    have hmem : (⟨x, hxC⟩ : C) ∈ P.subgroupOf C := Subgroup.mem_subgroupOf.2 hx
    exact Subgroup.mem_subgroupOf.1 (hle hmem)
  have hperfN : ⁅N, N⁆ ≤ rootSpan τ L (kernelRoots (jointChar a₁ a₂)) := by
    have hcomm := CFSG.StandardType.LayerExc.commutator_torus_sup_rootSpan_le (K := L)
      (S := familyKernel ![a₁, a₂]) (fun α hα => hα.1)
    rw [hN, familyGroup, ← ggLieCentOrbit_familyKernel_pair a₁ a₂]
    exact hcomm
  calc P = ⁅P, P⁆ := hperf.symm
    _ ≤ ⁅N, N⁆ := Subgroup.commutator_mono hPN hPN
    _ ≤ rootSpan τ L (kernelRoots (jointChar a₁ a₂)) := hperfN

theorem ggLieCentOrbit_component_le_orbitSpan
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (D : LangDatum τ L)
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (hρ : FrobRootMap D ρ) (hfin : Finite D.model)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a₁ a₂ : Fin τ.rank → Lˣ)
    (t₁ : rootDiagUnit τ a₁ ∈ D.torus) (t₂ : rootDiagUnit τ a₂ ∈ D.torus)
    (h₁ : rootDiagUnit τ a₁ ^ p = 1) (h₂ : rootDiagUnit τ a₂ ^ p = 1)
    (K : Subgroup (ModGL τ L))
    (hK : IsComponentOf K (D.Γ ⊓ Subgroup.centralizer
        ((Subgroup.closure {rootDiagUnit τ a₁, rootDiagUnit τ a₂} : Subgroup (ModGL τ L)) :
          Set (ModGL τ L)))) :
    ∃ i : KernelComponent (jointChar a₁ a₂),
      K ≤ rootSpan τ L (ratOrbit (fun u => ρ u) (componentRoots (jointChar a₁ a₂) i)) := by
  classical
  set χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ × Lˣ := jointChar a₁ a₂ with hχ
  have hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ := by
    rintro γ ⟨hγroot, hγχ⟩
    rw [hχ, ggLieCentOrbit_jointChar_apply] at hγχ
    obtain ⟨h1', h2'⟩ := Prod.mk_eq_one.1 hγχ
    have h1'' : rootChar a₁ γ = 1 := h1'
    have h2'' : rootChar a₂ γ = 1 := h2'
    refine ⟨(hρ.isRoot_iff γ).2 hγroot, ?_⟩
    rw [hχ, ggLieCentOrbit_jointChar_apply, Prod.mk_eq_one]
    refine ⟨?_, ?_⟩
    · show rootChar a₁ (ρ γ) = 1
      rw [hρ.rootChar_eq a₁ t₁ γ hγroot, h1'', one_pow]
    · show rootChar a₂ (ρ γ) = 1
      rw [hρ.rootChar_eq a₂ t₂ γ hγroot, h2'', one_pow]
  have hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ := hρ.iform_eq
  have hΓle : D.Γ ≤ D.model := Subgroup.commutator_le_self D.model
  have hΓ : D.Γ ≤ adjointGroup τ L := hΓle.trans inf_le_left
  have hΓfix : ∀ x ∈ D.Γ, D.step x = x := fun x hx => (hΓle hx).2
  have hKperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.1 ⟨hK.2.2.1⟩
  have hKmodel : K ≤ D.model := (hK.1.trans inf_le_left).trans hΓle
  haveI : Finite D.model := hfin
  haveI : Finite ↥K :=
    Finite.of_injective (Subgroup.inclusion hKmodel) (Subgroup.inclusion_injective _)
  have hKadj : K ≤ adjointGroup τ L ⊓ Subgroup.centralizer
      ((Subgroup.closure {rootDiagUnit τ a₁, rootDiagUnit τ a₂} : Subgroup (ModGL τ L)) :
        Set (ModGL τ L)) := fun x hx => ⟨hΓ (hK.1 hx).1, (hK.1 hx).2⟩
  have hKU : K ≤ rootSpan τ L (kernelRoots χ) :=
    ggLieCentOrbit_perfect_le_rootSpan hp hp2 a₁ a₂ h₁ h₂ hKadj hKperf
  haveI : Finite (kernelRoots χ) := ((finite_setOf_isRoot τ).subset fun α h => h.1).to_subtype
  haveI : Finite (KernelComponent χ) := inferInstance
  haveI : Finite (Set.range (ggLieCentOrbit_orbitRoots ρ χ)) := (Set.finite_range _).to_subtype
  let A : Set.range (ggLieCentOrbit_orbitRoots ρ χ) → Subgroup (ModGL τ L) :=
    fun O => rootSpan τ L O.1
  have hc : ∀ O O', O ≠ O' → ∀ x ∈ A O, ∀ y ∈ A O', Commute x y := by
    rintro ⟨_, i, rfl⟩ ⟨_, j, rfl⟩ hne
    exact ggLieCentOrbit_commute_rootSpan_orbitRoots hker hform (fun h => hne (Subtype.ext h))
  have hF : ∀ O, ∀ x ∈ A O, D.step x ∈ A O := by
    rintro ⟨_, i, rfl⟩ x hx
    exact ggLieCentOrbit_step_mem_rootSpan D ρ hρ
      (fun γ hγ => (ggLieCentOrbit_orbitRoots_subset_kernelRoots hker i hγ).1)
      (ggLieCentOrbit_orbitRoots_mapsTo i) hx
  have hU : ⨆ O, A O = rootSpan τ L (kernelRoots χ) := by
    refine le_antisymm (iSup_le fun O => ?_) ?_
    · obtain ⟨_, i, rfl⟩ := O
      exact rootSpan_mono (ggLieCentOrbit_orbitRoots_subset_kernelRoots hker i)
    · refine le_trans (iSup_componentRootSpan L (χ := χ)).ge (iSup_le fun i => ?_)
      have h : componentRootSpan L χ i ≤ A ⟨_, i, rfl⟩ :=
        rootSpan_mono fun γ hγ => ⟨0, γ, hγ, rfl⟩
      exact h.trans (le_iSup A ⟨_, i, rfl⟩)
  have hAadj : ∀ O, A O ≤ adjointGroup τ L := fun O => rootSpan_le_adjointGroup L O.1
  have h1 := perfect_le_iSup_inf_fixed D.step A hc hF hKperf (hKU.trans hU.ge)
    fun x hx => hΓfix x (Subgroup.mem_inf.1 (hK.1 hx)).1
  have hc2 : ∀ O O', O ≠ O' → ∀ x ∈ A O ⊓ D.step.eqLocus (MonoidHom.id _),
      ∀ y ∈ A O' ⊓ D.step.eqLocus (MonoidHom.id _), Commute x y :=
    fun O O' hne x hx y hy => hc O O' hne x hx.1 y hy.1
  have h2 : K ≤ ⨆ O, A O ⊓ D.Γ := by
    refine (perfect_le_iSup_commutator (fun O => A O ⊓ D.step.eqLocus (MonoidHom.id _)) hc2
      hKperf h1).trans (iSup_mono fun O => le_inf ?_ ?_)
    · exact (Subgroup.commutator_mono inf_le_left inf_le_left).trans
        (Subgroup.commutator_le_self _)
    · exact Subgroup.commutator_mono (fun x hx => ⟨hAadj O hx.1, hx.2⟩)
        (fun x hx => ⟨hAadj O hx.1, hx.2⟩)
  have hker₁ : ∀ i γ, γ ∈ ggLieCentOrbit_orbitRoots ρ χ i → rootChar a₁ γ = 1 := by
    intro i γ hγ
    have h := (ggLieCentOrbit_orbitRoots_subset_kernelRoots hker i hγ).2
    rw [hχ, ggLieCentOrbit_jointChar_apply] at h
    exact (Prod.mk_eq_one.1 h).1
  have hker₂ : ∀ i γ, γ ∈ ggLieCentOrbit_orbitRoots ρ χ i → rootChar a₂ γ = 1 := by
    intro i γ hγ
    have h := (ggLieCentOrbit_orbitRoots_subset_kernelRoots hker i hγ).2
    rw [hχ, ggLieCentOrbit_jointChar_apply] at h
    exact (Prod.mk_eq_one.1 h).2
  have hcent : ∀ O, A O ≤ Subgroup.centralizer
      (Subgroup.closure {rootDiagUnit τ a₁, rootDiagUnit τ a₂} : Set (ModGL τ L)) := by
    rintro ⟨_, i, rfl⟩ x hx
    rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hy with rfl | rfl
    · exact (Subgroup.mem_centralizer_iff.1 (rootSpan_le_centralizer a₁
        (fun γ hγ => ⟨(ggLieCentOrbit_orbitRoots_subset_kernelRoots hker i hγ).1,
          hker₁ i γ hγ⟩) hx)) _ (by simp)
    · exact (Subgroup.mem_centralizer_iff.1 (rootSpan_le_centralizer a₂
        (fun γ hγ => ⟨(ggLieCentOrbit_orbitRoots_subset_kernelRoots hker i hγ).1,
          hker₂ i γ hγ⟩) hx)) _ (by simp)
  set P' : Subgroup (ModGL τ L) := ⨆ O, A O ⊓ D.Γ with hP'
  have hP'X : P' ≤ D.Γ ⊓ Subgroup.centralizer
      (Subgroup.closure {rootDiagUnit τ a₁, rootDiagUnit τ a₂} : Set (ModGL τ L)) :=
    iSup_le fun O => le_inf inf_le_right (inf_le_left.trans (hcent O))
  have hKP' : K ≤ P' := h2
  haveI : Finite ↥P' := Finite.of_injective
    (Subgroup.inclusion (((hP'X.trans inf_le_left).trans hΓle) : P' ≤ D.model))
    (Subgroup.inclusion_injective _)
  have hKcomp : IsComponentOf K P' :=
    ⟨hKP', ggLieCentOrbit_isSubnormal_of_le_of_le' hK.2.1 hKP' hP'X, hK.2.2⟩
  have hnorm : ∀ O, ((A O ⊓ D.Γ).subgroupOf P').Normal := by
    intro O
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (le_iSup (fun O => A O ⊓ D.Γ) O)]
    refine iSup_le fun O' => ?_
    by_cases hOO : O' = O
    · rw [hOO]
      exact Subgroup.le_normalizer
    · refine le_trans ?_ (Subgroup.centralizer_le_normalizer (A O ⊓ D.Γ : Set (ModGL τ L)))
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hc O O' (Ne.symm hOO) y hy.1 x hx.1).eq
  have hsub : ∀ O, IsSubnormal (A O ⊓ D.Γ) P' := fun O =>
    IsSubnormal.step (le_iSup (fun O => A O ⊓ D.Γ) O) (hnorm O) (IsSubnormal.refl P')
  have hex : ∃ O, K ≤ A O ⊓ D.Γ := by
    by_contra hcon
    push Not at hcon
    have hcomm : ∀ O, ⁅K, A O ⊓ D.Γ⁆ = ⊥ := fun O =>
      (ggLieCentOrbit_comp_le_or_commutator_eq_bot hKcomp (hsub O)).resolve_left (hcon O)
    have hP'c : P' ≤ Subgroup.centralizer (K : Set (ModGL τ L)) :=
      iSup_le fun O => Subgroup.commutator_eq_bot_iff_le_centralizer.1
        ((Subgroup.commutator_comm _ _).trans (hcomm O))
    have hKc : K ≤ Subgroup.centralizer (K : Set (ModGL τ L)) := hKP'.trans hP'c
    obtain ⟨x, y, hxy⟩ := ggLieCentOrbit_exists_noncomm_of_isQuasisimple hK.2.2
    exact hxy (Subtype.ext (Subgroup.mem_centralizer_iff.1 (hKc y.2) x x.2))
  obtain ⟨⟨_, i, rfl⟩, hKi⟩ := hex
  exact ⟨i, hKi.trans inf_le_left⟩

end CFSG.StandardType.LieCore
