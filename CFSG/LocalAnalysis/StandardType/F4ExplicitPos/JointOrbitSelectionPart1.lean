module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.CyclicFinish
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.FamilyPosition

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.JointOrbitSelection

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.StandardType.LieCore
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups

open CFSG.Assembly

open CFSG.StandardType.F4ExplicitPos.FamilyPosition

open CFSG.LieType.Steinberg.Adjoint

open Matrix

open scoped commutatorElement Pointwise

variable {τ : Tag} {L : Type} [Field L]

theorem ratOrbit_iterate_mem_kernelRoots {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ) (k : ℕ) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ kernelRoots χ) :
    (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k] γ ∈ kernelRoots χ := by
  induction k with
  | zero => exact hγ
  | succ k ih => rw [Function.iterate_succ_apply']; exact hker _ ih

theorem ratOrbit_subset_kernelRoots {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ) (i : KernelComponent χ) :
    ratOrbit (fun u => ρ u) (componentRoots χ i) ⊆ kernelRoots χ := by
  rintro _ ⟨k, δ, ⟨hδ, -⟩, rfl⟩
  exact ratOrbit_iterate_mem_kernelRoots hker k hδ

theorem ratOrbit_eqvGen_map {X : Type*} {r : X → X → Prop} (f : X → X)
    (hf : ∀ x y, r x y → r (f x) (f y)) {x y : X} (h : Relation.EqvGen r x y) :
    Relation.EqvGen r (f x) (f y) := by
  induction h with
  | rel x y h => exact .rel _ _ (hf x y h)
  | refl x => exact .refl _
  | symm x y _ ih => exact .symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact .trans _ _ _ ih1 ih2

theorem ratOrbit_eqvGen_equiv_iff {X : Type*} {r : X → X → Prop} (e : X ≃ X)
    (hr : ∀ x y, r (e x) (e y) ↔ r x y) (x y : X) :
    Relation.EqvGen r (e x) (e y) ↔ Relation.EqvGen r x y := by
  refine ⟨fun h => ?_, ratOrbit_eqvGen_map e fun x y h => (hr x y).2 h⟩
  have := ratOrbit_eqvGen_map e.symm
    (fun a b h => (hr (e.symm a) (e.symm b)).1 (by simpa using h)) h
  simpa using this

theorem ratOrbit_iform_iterate {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    (hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ) (k : ℕ) (x y : Fin τ.rank → ℤ) :
    iform ((ρ : (Fin τ.rank → ℤ) → _)^[k] x) ((ρ : (Fin τ.rank → ℤ) → _)^[k] y) =
      iform x y := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, hform]

theorem ratOrbit_kernelComponent_eq_iff {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (x y : kernelRoots χ) :
    (⟦x⟧ : KernelComponent χ) = ⟦y⟧ ↔ Relation.EqvGen
      (fun α β : kernelRoots χ =>
        (α : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (β : Fin τ.rank → ℤ)) ≠ 0) x y :=
  Quotient.eq (r := kernelRootSetoid χ)

theorem ratOrbit_closed {M : Type*} [CommGroup M]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ) (i : KernelComponent χ)
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ ratOrbit (fun u => ρ u) (componentRoots χ i))
    {β : Fin τ.rank → ℤ} (hβ : β ∈ kernelRoots χ)
    (h : (⟦⟨β, hβ⟩⟧ : KernelComponent χ) =
      ⟦⟨γ, ratOrbit_subset_kernelRoots hker i hγ⟩⟧) :
    β ∈ ratOrbit (fun u => ρ u) (componentRoots χ i) := by
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
      ratOrbit_iform_iterate hform]
  obtain ⟨k, δ, ⟨hδ, hδi⟩, rfl⟩ := hγ
  set y : kernelRoots χ := (e ^ k)⁻¹ ⟨β, hβ⟩ with hy
  have hey : (e ^ k) y = ⟨β, hβ⟩ := by simp [hy]
  have hex : (e ^ k) ⟨δ, hδ⟩ =
      ⟨(ρ : (Fin τ.rank → ℤ) → _)^[k] δ, ratOrbit_iterate_mem_kernelRoots hker k hδ⟩ :=
    Subtype.ext (he_iter k ⟨δ, hδ⟩)
  have hyx : (⟦y⟧ : KernelComponent χ) = ⟦⟨δ, hδ⟩⟧ := by
    rw [ratOrbit_kernelComponent_eq_iff]
    refine (ratOrbit_eqvGen_equiv_iff (e ^ k) (hr k) y ⟨δ, hδ⟩).1 ?_
    rw [hey, hex]
    exact (ratOrbit_kernelComponent_eq_iff _ _).1 h
  refine ⟨k, y, ⟨y.2, hyx.trans hδi⟩, ?_⟩
  have := congrArg Subtype.val hey
  rw [he_iter] at this
  exact this.symm

theorem ratOrbit_mapsTo {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    (i : KernelComponent χ) :
    Set.MapsTo (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))
      (ratOrbit (fun u => ρ u) (componentRoots χ i))
      (ratOrbit (fun u => ρ u) (componentRoots χ i)) := by
  rintro _ ⟨k, δ, hδ, rfl⟩
  exact ⟨k + 1, δ, hδ, by rw [Function.iterate_succ_apply']⟩

theorem ratOrbit_of_apply_mem {M : Type*} [CommGroup M]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (i : KernelComponent χ) {δ : Fin τ.rank → ℤ}
    (h : ρ δ ∈ ratOrbit (fun u => ρ u) (componentRoots χ i)) :
    δ ∈ ratOrbit (fun u => ρ u) (componentRoots χ i) := by
  have hfin : (ratOrbit (fun u => ρ u) (componentRoots χ i)).Finite :=
    ((finite_setOf_isRoot τ).subset fun α hα => hα.1 : (kernelRoots χ).Finite).subset
      (ratOrbit_subset_kernelRoots hker i)
  have hbij := (hfin.injOn_iff_bijOn_of_mapsTo (ratOrbit_mapsTo i)).1 ρ.injective.injOn
  obtain ⟨γ, hγ, hγδ⟩ := hbij.surjOn h
  exact ρ.injective hγδ ▸ hγ

theorem ratOrbit_of_iterate_mem {M : Type*} [CommGroup M]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (i : KernelComponent χ) (n : ℕ) {δ : Fin τ.rank → ℤ}
    (h : (ρ : (Fin τ.rank → ℤ) → _)^[n] δ ∈ ratOrbit (fun u => ρ u) (componentRoots χ i)) :
    δ ∈ ratOrbit (fun u => ρ u) (componentRoots χ i) := by
  induction n generalizing δ with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h
    exact ratOrbit_of_apply_mem hker i (ih h)

theorem ratOrbit_iterate_mem {M : Type*} [CommGroup M]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (i : KernelComponent χ) (n : ℕ) {γ : Fin τ.rank → ℤ}
    (h : γ ∈ ratOrbit (fun u => ρ u) (componentRoots χ i)) :
    (ρ : (Fin τ.rank → ℤ) → _)^[n] γ ∈ ratOrbit (fun u => ρ u) (componentRoots χ i) := by
  obtain ⟨k, δ, hδ, rfl⟩ := h
  exact ⟨n + k, δ, hδ, by rw [Function.iterate_add_apply]⟩

theorem ratOrbit_subset_of_mem_inter {M : Type*} [CommGroup M]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ) {i j : KernelComponent χ}
    {δ : Fin τ.rank → ℤ} (hi : δ ∈ ratOrbit (fun u => ρ u) (componentRoots χ i))
    (hj : δ ∈ ratOrbit (fun u => ρ u) (componentRoots χ j)) :
    ratOrbit (fun u => ρ u) (componentRoots χ j) ⊆
      ratOrbit (fun u => ρ u) (componentRoots χ i) := by
  obtain ⟨n, δ₂, ⟨hδ₂, hδ₂j⟩, rfl⟩ := hj
  have hδ₂i : δ₂ ∈ ratOrbit (fun u => ρ u) (componentRoots χ i) :=
    ratOrbit_of_iterate_mem hker i n hi
  rintro _ ⟨l, ε₂, ⟨hε₂, hε₂j⟩, rfl⟩
  exact ratOrbit_iterate_mem i l
    (ratOrbit_closed hker hform i hδ₂i hε₂ (hε₂j.trans hδ₂j.symm))

theorem ratOrbit_eq_of_mem_inter {M : Type*} [CommGroup M]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ) {i j : KernelComponent χ}
    {δ : Fin τ.rank → ℤ} (hi : δ ∈ ratOrbit (fun u => ρ u) (componentRoots χ i))
    (hj : δ ∈ ratOrbit (fun u => ρ u) (componentRoots χ j)) :
    ratOrbit (fun u => ρ u) (componentRoots χ i) =
      ratOrbit (fun u => ρ u) (componentRoots χ j) :=
  le_antisymm (ratOrbit_subset_of_mem_inter hker hform hj hi)
    (ratOrbit_subset_of_mem_inter hker hform hi hj)

theorem ratOrbit_commute_rootSpan
    {M : Type*} [CommGroup M]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hcomm : ∀ i j : KernelComponent χ, i ≠ j →
      ∀ u ∈ componentRootSpan L χ i, ∀ v ∈ componentRootSpan L χ j, Commute u v)
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ) {i j : KernelComponent χ}
    (hij : ratOrbit (fun u => ρ u) (componentRoots χ i) ≠
      ratOrbit (fun u => ρ u) (componentRoots χ j)) :
    ∀ x ∈ rootSpan τ L (ratOrbit (fun u => ρ u) (componentRoots χ i)),
      ∀ y ∈ rootSpan τ L (ratOrbit (fun u => ρ u) (componentRoots χ j)), Commute x y := by
  have hle : rootSpan τ L (ratOrbit (fun u => ρ u) (componentRoots χ i)) ≤
      Subgroup.centralizer (rootSpan τ L (ratOrbit (fun u => ρ u) (componentRoots χ j)) :
        Set (ModGL τ L)) := by
    refine iSup₂_le fun γ hγ => ?_
    rw [Subgroup.le_centralizer_iff]
    refine iSup₂_le fun δ hδ => ?_
    rw [Subgroup.le_centralizer_iff]
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hγk := ratOrbit_subset_kernelRoots hker i hγ
    have hδk := ratOrbit_subset_kernelRoots hker j hδ
    have hne : (⟦⟨γ, hγk⟩⟧ : KernelComponent χ) ≠ ⟦⟨δ, hδk⟩⟧ := fun h =>
      hij (ratOrbit_eq_of_mem_inter hker hform
        (ratOrbit_closed hker hform i hγ hδk h.symm) hδ)
    exact (hcomm _ _ hne y (rootSubgroup_le_componentRootSpan (K := L) ⟨γ, hγk⟩ hy)
      x (rootSubgroup_le_componentRootSpan (K := L) ⟨δ, hδk⟩ hx)).eq.symm
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.1 (hle hx) y hy).symm

theorem ratOrbit_step_mem_rootSpan
    (D : LangDatum τ L)
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} (hρ : FrobRootMap D ρ)
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

theorem f4_ratOrbit_commute_rootSpan
    {M : Type*} [CommGroup M]
    {ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)}
    {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ) {i j : KernelComponent χ}
    (hij : ratOrbit (fun u => ρ u) (componentRoots χ i) ≠
      ratOrbit (fun u => ρ u) (componentRoots χ j)) :
    ∀ x ∈ rootSpan Tag.F4 L (ratOrbit (fun u => ρ u) (componentRoots χ i)),
      ∀ y ∈ rootSpan Tag.F4 L (ratOrbit (fun u => ρ u) (componentRoots χ j)), Commute x y :=
  ratOrbit_commute_rootSpan
    (fun _ _ hij => CyclicFinish.f4_componentRootSpan_commute _ _ hij)
    hker hform hij

theorem jointChar_apply (a₁ a₂ : Fin τ.rank → Lˣ)
    (v : Multiplicative (Fin τ.rank → ℤ)) :
    jointChar a₁ a₂ v =
      (rootChar a₁ (Multiplicative.toAdd v), rootChar a₂ (Multiplicative.toAdd v)) := rfl

section PerfectJoint

variable {K : Type} [Field K] {ι : Type}

theorem perfect_le_left_of_solvable_right {G : Type*} [Group G] {M Y P : Subgroup G}
    (hYnorm : Y ≤ Subgroup.normalizer (M : Set G)) [hY : Group.IsSolvable ↥Y]
    (hperf : ⁅P, P⁆ = P) (hPMY : P ≤ M ⊔ Y) : P ≤ M := by
  obtain ⟨k, hk⟩ := CFSG.StandardType.LayerCores.exists_ggDer_eq_bot (U := Y) hY
  calc P = CFSG.StandardType.LayerFacts.ggDer P k :=
        (CFSG.StandardType.LayerFacts.ggDer_of_perfect hperf k).symm
    _ ≤ CFSG.StandardType.LayerFacts.ggDer (M ⊔ Y) k :=
        CFSG.StandardType.LayerFacts.ggDer_mono hPMY k
    _ ≤ M ⊔ CFSG.StandardType.LayerFacts.ggDer Y k :=
        CFSG.StandardType.LayerExc.ggDer_sup_le_of_le_normalizer hYnorm k
    _ = M := by rw [hk, sup_bot_eq]

theorem f4_isSolvable_monomialSubgroup :
    Group.IsSolvable ↥(monomialSubgroup Tag.F4 K) := by
  have hTsub : Group.IsSolvable
      ↥((torusGroup Tag.F4 K).subgroupOf (monomialSubgroup Tag.F4 K)) :=
    Group.isSolvable_of_comm fun x y =>
      Subtype.ext (Subtype.ext
        (CFSG.StandardType.LayerExc.commute_of_mem_torusGroup x.2 y.2))
  have hW : Group.IsSolvable (WeylGroup Tag.F4) :=
    CFSG.StandardType.LayerExc.isSolvable_weylGroup_F4
  obtain ⟨-, ⟨ρ, -, -, -, hker⟩, -⟩ :=
    Weyl_normalizer_quotient (τ := Tag.F4) K
  refine Group.isSolvable_of_ker_le_range
    (Subgroup.subtype ((torusGroup Tag.F4 K).subgroupOf (monomialSubgroup Tag.F4 K))) ρ ?_
  rw [hker.2, Subgroup.range_subtype]

def familyWeylSubgroup
    (a : ι → Fin Tag.F4.rank → Kˣ) : Subgroup (ModGL Tag.F4 K) :=
  Subgroup.closure
    ((fun w : WeylGroup Tag.F4 => canonicalRep (coxeterSystem Tag.F4) K w) '' familyStabilizer a)

theorem familyWeylSubgroup_le_monomialSubgroup
    (a : ι → Fin Tag.F4.rank → Kˣ) :
    familyWeylSubgroup (K := K) a ≤ monomialSubgroup Tag.F4 K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨w, -, rfl⟩
  exact canonicalRep_mem_monomialSubgroup K w

theorem familyWeylSubgroup_le_normalizer_familyGroup
    (a : ι → Fin Tag.F4.rank → Kˣ) :
    familyWeylSubgroup (K := K) a ≤
      Subgroup.normalizer (familyGroup (K := K) a : Set (ModGL Tag.F4 K)) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨w, hw, rfl⟩
  exact canonicalRep_mem_normalizer_familyGroup (K := K) hw

end PerfectJoint
end CFSG.StandardType.F4ExplicitPos.JointOrbitSelection
end

end
