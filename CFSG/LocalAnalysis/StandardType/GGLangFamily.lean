module

public import CFSG.LocalAnalysis.StandardType.GGLangRatSingleOrbit
public import CFSG.LocalAnalysis.StandardType.GGFamRatComp
import CFSG.LocalAnalysis.StandardType.GGWeylFamQuotSolvFin

public section

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.TableCRes
open scoped commutatorElement

private def orbitRoots {τ : Tag} {M : Type*} [CommGroup M] (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (i : KernelComponent χ) :
    Set (Fin τ.rank → ℤ) :=
  {γ | ∃ (k : ℕ) (δ : Fin τ.rank → ℤ), δ ∈ componentRoots χ i ∧
    γ = (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k] δ}

private theorem orbitRoots_mapsTo {τ : Tag} {M : Type*} [CommGroup M]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (i : KernelComponent χ) :
    Set.MapsTo (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) (orbitRoots ρ χ i) (orbitRoots ρ χ i) := by
  rintro _ ⟨k, δ, hδ, rfl⟩
  exact ⟨k + 1, δ, hδ, by rw [Function.iterate_succ_apply']⟩

private theorem orbit_iterate_mem_kernelRoots {τ : Tag} {M : Type*} [CommGroup M]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ) (k : ℕ) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ kernelRoots χ) :
    (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k] γ ∈ kernelRoots χ := by
  induction k with
  | zero => exact hγ
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact hker _ ih

private theorem orbitRoots_subset_kernelRoots {τ : Tag} {M : Type*} [CommGroup M]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ) (i : KernelComponent χ) :
    orbitRoots ρ χ i ⊆ kernelRoots χ := by
  rintro _ ⟨k, δ, ⟨hδ, -⟩, rfl⟩
  exact orbit_iterate_mem_kernelRoots hker k hδ

private theorem orbit_eqvGen_map {X : Type*} {r : X → X → Prop} (f : X → X)
    (hf : ∀ x y, r x y → r (f x) (f y)) {x y : X} (h : Relation.EqvGen r x y) :
    Relation.EqvGen r (f x) (f y) := by
  induction h with
  | rel x y h => exact .rel _ _ (hf x y h)
  | refl x => exact .refl _
  | symm x y _ ih => exact .symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact .trans _ _ _ ih1 ih2

private theorem orbit_eqvGen_equiv_iff {X : Type*} {r : X → X → Prop} (e : X ≃ X)
    (hr : ∀ x y, r (e x) (e y) ↔ r x y) (x y : X) :
    Relation.EqvGen r (e x) (e y) ↔ Relation.EqvGen r x y := by
  refine ⟨fun h => ?_, orbit_eqvGen_map e fun x y h => (hr x y).2 h⟩
  have := orbit_eqvGen_map e.symm (fun a b h => (hr (e.symm a) (e.symm b)).1 (by simpa using h)) h
  simpa using this

private theorem orbit_iform_iterate {τ : Tag} {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    (hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ) (k : ℕ) (x y : Fin τ.rank → ℤ) :
    iform ((ρ : (Fin τ.rank → ℤ) → _)^[k] x) ((ρ : (Fin τ.rank → ℤ) → _)^[k] y) = iform x y := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, hform]

open Matrix in
private theorem orbit_kernelComponent_eq_iff {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (x y : kernelRoots χ) :
    (⟦x⟧ : KernelComponent χ) = ⟦y⟧ ↔ Relation.EqvGen
      (fun α β : kernelRoots χ =>
        (α : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (β : Fin τ.rank → ℤ)) ≠ 0) x y :=
  Quotient.eq (r := kernelRootSetoid χ)

open Matrix in
private theorem orbitRoots_closed {τ : Tag} {M : Type*} [CommGroup M]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ) (i : KernelComponent χ)
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ orbitRoots ρ χ i) {β : Fin τ.rank → ℤ}
    (hβ : β ∈ kernelRoots χ)
    (h : (⟦⟨β, hβ⟩⟧ : KernelComponent χ) = ⟦⟨γ, orbitRoots_subset_kernelRoots hker i hγ⟩⟧) :
    β ∈ orbitRoots ρ χ i := by
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
      orbit_iform_iterate hform]
  obtain ⟨k, δ, ⟨hδ, hδi⟩, rfl⟩ := hγ
  set y : kernelRoots χ := (e ^ k)⁻¹ ⟨β, hβ⟩ with hy
  have hey : (e ^ k) y = ⟨β, hβ⟩ := by simp [hy]
  have hex : (e ^ k) ⟨δ, hδ⟩ = ⟨(ρ : (Fin τ.rank → ℤ) → _)^[k] δ, orbit_iterate_mem_kernelRoots hker k hδ⟩ :=
    Subtype.ext (he_iter k ⟨δ, hδ⟩)
  have hyx : (⟦y⟧ : KernelComponent χ) = ⟦⟨δ, hδ⟩⟧ := by
    rw [orbit_kernelComponent_eq_iff]
    refine (orbit_eqvGen_equiv_iff (e ^ k) (hr k) y ⟨δ, hδ⟩).1 ?_
    rw [hey, hex]
    exact (orbit_kernelComponent_eq_iff _ _).1 h
  refine ⟨k, y, ⟨y.2, hyx.trans hδi⟩, ?_⟩
  have := congrArg Subtype.val hey
  rw [he_iter] at this
  exact this.symm

private theorem orbitRoots_of_apply_mem {τ : Tag} {M : Type*}
    [CommGroup M] {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (i : KernelComponent χ) {δ : Fin τ.rank → ℤ} (h : ρ δ ∈ orbitRoots ρ χ i) :
    δ ∈ orbitRoots ρ χ i := by
  have hfin : (orbitRoots ρ χ i).Finite :=
    ((finite_setOf_isRoot τ).subset fun α hα => hα.1 : (kernelRoots χ).Finite).subset
      (orbitRoots_subset_kernelRoots hker i)
  have hbij := (hfin.injOn_iff_bijOn_of_mapsTo (orbitRoots_mapsTo i)).1 ρ.injective.injOn
  obtain ⟨γ, hγ, hγδ⟩ := hbij.surjOn h
  exact ρ.injective hγδ ▸ hγ

private theorem orbitRoots_of_iterate_mem {τ : Tag} {M : Type*}
    [CommGroup M] {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (i : KernelComponent χ) (n : ℕ) {δ : Fin τ.rank → ℤ}
    (h : (ρ : (Fin τ.rank → ℤ) → _)^[n] δ ∈ orbitRoots ρ χ i) : δ ∈ orbitRoots ρ χ i := by
  induction n generalizing δ with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h
    exact orbitRoots_of_apply_mem hker i (ih h)

private theorem iterate_mem_orbitRoots {τ : Tag} {M : Type*} [CommGroup M]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (i : KernelComponent χ) (n : ℕ) {γ : Fin τ.rank → ℤ}
    (h : γ ∈ orbitRoots ρ χ i) : (ρ : (Fin τ.rank → ℤ) → _)^[n] γ ∈ orbitRoots ρ χ i := by
  obtain ⟨k, δ, hδ, rfl⟩ := h
  exact ⟨n + k, δ, hδ, by rw [Function.iterate_add_apply]⟩

private theorem orbitRoots_subset_of_mem_inter {τ : Tag} {M : Type*}
    [CommGroup M] {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ) {i j : KernelComponent χ}
    {δ : Fin τ.rank → ℤ} (hi : δ ∈ orbitRoots ρ χ i) (hj : δ ∈ orbitRoots ρ χ j) :
    orbitRoots ρ χ j ⊆ orbitRoots ρ χ i := by
  obtain ⟨n, δ₂, ⟨hδ₂, hδ₂j⟩, rfl⟩ := hj
  have hδ₂i : δ₂ ∈ orbitRoots ρ χ i := orbitRoots_of_iterate_mem hker i n hi
  rintro _ ⟨l, ε₂, ⟨hε₂, hε₂j⟩, rfl⟩
  exact iterate_mem_orbitRoots i l
    (orbitRoots_closed hker hform i hδ₂i hε₂ (hε₂j.trans hδ₂j.symm))

private theorem orbitRoots_eq_of_mem_inter {τ : Tag} {M : Type*}
    [CommGroup M] {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ) {i j : KernelComponent χ}
    {δ : Fin τ.rank → ℤ} (hi : δ ∈ orbitRoots ρ χ i) (hj : δ ∈ orbitRoots ρ χ j) :
    orbitRoots ρ χ i = orbitRoots ρ χ j :=
  le_antisymm (orbitRoots_subset_of_mem_inter hker hform hj hi)
    (orbitRoots_subset_of_mem_inter hker hform hi hj)

private theorem commute_rootSpan_orbitRoots
    {τ : Tag} {L : Type} [Field L] {M : Type*} [CommGroup M]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ) {i j : KernelComponent χ}
    (hij : orbitRoots ρ χ i ≠ orbitRoots ρ χ j) :
    ∀ x ∈ rootSpan τ L (orbitRoots ρ χ i), ∀ y ∈ rootSpan τ L (orbitRoots ρ χ j),
      Commute x y := by
  have hle : rootSpan τ L (orbitRoots ρ χ i) ≤
      Subgroup.centralizer (rootSpan τ L (orbitRoots ρ χ j) : Set (ModGL τ L)) := by
    refine iSup₂_le fun γ hγ => ?_
    rw [Subgroup.le_centralizer_iff]
    refine iSup₂_le fun δ hδ => ?_
    rw [Subgroup.le_centralizer_iff]
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hγk := orbitRoots_subset_kernelRoots hker i hγ
    have hδk := orbitRoots_subset_kernelRoots hker j hδ
    have hne : (⟦⟨γ, hγk⟩⟧ : KernelComponent χ) ≠ ⟦⟨δ, hδk⟩⟧ := fun h =>
      hij (orbitRoots_eq_of_mem_inter hker hform
        (orbitRoots_closed hker hform i hγ hδk h.symm) hδ)
    exact (commute_of_mk_ne hne L y hy x hx).eq.symm
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.1 (hle hx) y hy).symm

private theorem rho_mem_kernelRoots_pi
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {ι : Type} {a : ι → Fin τ.rank → Lˣ} (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) :
    ∀ γ ∈ kernelRoots (Pi.monoidHom fun u => rootCharHom (a u)),
      S.ρ γ ∈ kernelRoots (Pi.monoidHom fun u => rootCharHom (a u)) := by
  rintro γ ⟨hγ, h⟩
  refine ⟨(S.frob.isRoot_iff γ).2 hγ, funext fun u => ?_⟩
  have h' : rootChar (a u) γ = 1 := congrFun h u
  show rootChar (a u) (S.ρ γ) = 1
  rw [S.frob.rootChar_eq (a u) (hT u) γ hγ, h', one_pow]

private noncomputable def famGroup {τ : Tag} {L : Type} [Field L] {ι : Type} (a : ι → Fin τ.rank → Lˣ)
    (hd : ∀ u, rootDiagUnit τ (a u) ∈ adjointGroup τ L) : Subgroup ↥(adjointGroup τ L) :=
  Subgroup.closure (Set.range fun u => (⟨rootDiagUnit τ (a u), hd u⟩ : ↥(adjointGroup τ L)))

private theorem fam_mem_of_mem_torusTuples_famGroup
    {τ : Tag} {L : Type} [Field L] {ι : Type} (a : ι → Fin τ.rank → Lˣ)
    (hd : ∀ u, rootDiagUnit τ (a u) ∈ adjointGroup τ L)
    (T : Subgroup (Fin τ.rank → Lˣ)) (haT : ∀ u, a u ∈ T) :
    ∀ b ∈ LayerExc.torusTuples (famGroup a hd), b ∈ T := by
  have hle : famGroup a hd ≤ (T.map (rootDiagUnitHom τ L)).comap (adjointGroup τ L).subtype := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨u, rfl⟩
    exact ⟨a u, haT u, rfl⟩
  intro b hb
  obtain ⟨x, hx, hxeq⟩ := hb
  have hxmap : (adjointGroup τ L).subtype x ∈ T.map (rootDiagUnitHom τ L) := hle hx
  rw [Subgroup.mem_map] at hxmap
  obtain ⟨c, hcT, hceq⟩ := hxmap
  have h1 : rootDiagUnit τ c = (x : ModGL τ L) := hceq
  have h2 : rootDiagUnit τ b = (x : ModGL τ L) := hxeq.symm
  have hcb : c = b := rootDiagUnit_injective (h1.trans h2.symm)
  show b ∈ T
  rw [← hcb]
  exact hcT

private theorem pow_eq_one_of_mem_torusTuples_famGroup
    {τ : Tag} {L : Type} [Field L] {ι : Type} (a : ι → Fin τ.rank → Lˣ) {p : ℕ}
    (hap : ∀ u j, a u j ^ p = 1) (hd : ∀ u, rootDiagUnit τ (a u) ∈ adjointGroup τ L) :
    ∀ b ∈ LayerExc.torusTuples (famGroup a hd), ∀ j, b j ^ p = 1 := by
  have haT : ∀ u, a u ∈ (powMonoidHom p : (Fin τ.rank → Lˣ) →* (Fin τ.rank → Lˣ)).ker :=
    fun u => by
      rw [MonoidHom.mem_ker, powMonoidHom_apply]
      funext j
      simpa [Pi.pow_apply] using hap u j
  intro b hb j
  have hbT : b ∈ (powMonoidHom p : (Fin τ.rank → Lˣ) →* (Fin τ.rank → Lˣ)).ker :=
    fam_mem_of_mem_torusTuples_famGroup a hd _ haT b hb
  have hbp : (powMonoidHom p : (Fin τ.rank → Lˣ) →* (Fin τ.rank → Lˣ)) b = 1 :=
    MonoidHom.mem_ker.mp hbT
  rw [powMonoidHom_apply] at hbp
  simpa [Pi.pow_apply] using congrFun hbp j

private theorem famKernel_torusTuples_famGroup
    {τ : Tag} {L : Type} [Field L] {ι : Type} (a : ι → Fin τ.rank → Lˣ)
    (hd : ∀ u, rootDiagUnit τ (a u) ∈ adjointGroup τ L) :
    CFSG.RankThree.PartOne.KE8F.famKernel (LayerExc.torusTuples (famGroup a hd)) =
      kernelRoots (Pi.monoidHom fun u => rootCharHom (a u)) := by
  ext α
  change (IsRoot τ α ∧ ∀ b ∈ LayerExc.torusTuples (famGroup a hd), rootChar b α = 1) ↔
    (IsRoot τ α ∧ (Pi.monoidHom fun u => rootCharHom (a u)) (Multiplicative.ofAdd α) = 1)
  constructor
  · rintro ⟨hroot, hfam⟩
    refine ⟨hroot, ?_⟩
    funext u
    exact hfam (a u) ⟨⟨rootDiagUnit τ (a u), hd u⟩, Subgroup.subset_closure ⟨u, rfl⟩, rfl⟩
  · rintro ⟨hroot, hker⟩
    refine ⟨hroot, ?_⟩
    let ψ : (Fin τ.rank → Lˣ) →* Lˣ :=
      { toFun := fun c => rootChar c α
        map_one' := by simp [rootChar]
        map_mul' := fun c d => by
          simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib] }
    have haT : ∀ u, a u ∈ ψ.ker := fun u => by
      rw [MonoidHom.mem_ker]
      show ψ (a u) = 1
      exact congrFun hker u
    intro b hb
    exact fam_mem_of_mem_torusTuples_famGroup a hd ψ.ker haT b hb

private theorem mem_centralizer_famGroup {τ : Tag} {L : Type} [Field L] {ι : Type}
    (a : ι → Fin τ.rank → Lˣ) (hd : ∀ u, rootDiagUnit τ (a u) ∈ adjointGroup τ L)
    {g : ↥(adjointGroup τ L)}
    (hg : (g : ModGL τ L) ∈ Subgroup.centralizer (Set.range fun u => rootDiagUnit τ (a u))) :
    g ∈ Subgroup.centralizer (famGroup a hd : Set ↥(adjointGroup τ L)) := by
  have hle : famGroup a hd ≤ Subgroup.centralizer ({g} : Set ↥(adjointGroup τ L)) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨u, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hg _ ⟨u, rfl⟩)
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hh)

private theorem exists_ggDer_famStabilizerSubgroup_le_reflection_of_pow
    {τ : Tag} {L : Type} [Field L] {p : ℕ} (hp : p.Prime)
    (F : Set (Fin τ.rank → Lˣ)) (hF : ∀ b ∈ F, ∀ j, b j ^ p = 1) :
    ∃ k, LayerFacts.ggDer (LayerExc.famStabilizerSubgroup F) k ≤ LayerExc.famReflectionGroup F := by
  have hpoly : (Polynomial.X ^ p - 1 : Polynomial L) ≠ 0 :=
    (Polynomial.monic_X_pow_sub_one hp.ne_zero).ne_zero
  have hμ : Set.Finite {x : L | x ^ p = 1} := by
    simpa [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one, sub_eq_zero] using
      (Polynomial.finite_setOf_isRoot (p := (Polynomial.X ^ p - 1 : Polynomial L)) hpoly)
  have hμ' : Set.Finite {x : Lˣ | (x : L) ^ p = 1} :=
    Set.Finite.of_injOn (f := fun x : Lˣ => (x : L))
      (fun _ hx => hx) (fun a _ b _ h => Units.ext h) hμ
  have hFfin : F.Finite :=
    (Set.Finite.pi fun _ : Fin τ.rank => hμ').subset fun b hb j _ => by
      have := congrArg (fun u : Lˣ => (u : L)) (hF b hb j)
      simpa [Units.val_pow_eq_pow_val] using this
  exact LayerExc.exists_ggDer_famStabilizerSubgroup_le_reflection_of_finite hp F hFfin
    (fun a ha => ⟨1, by
      have h : a ^ p = 1 := funext fun j => hF a ha j
      simpa using h⟩)

private theorem ggDer_centralizer_le_rootSpan_famKernel
    {τ : Tag} {L : Type} [Field L] (A : Subgroup ↥(adjointGroup τ L)) {k : ℕ}
    (hk : LayerFacts.ggDer (LayerExc.famStabilizerSubgroup (LayerExc.torusTuples A)) k ≤
      LayerExc.famReflectionGroup (LayerExc.torusTuples A)) :
    LayerFacts.ggDer ((Subgroup.centralizer (A : Set ↥(adjointGroup τ L))).map
      (adjointGroup τ L).subtype) (k + 1) ≤
        rootSpan τ L (CFSG.RankThree.PartOne.KE8F.famKernel (LayerExc.torusTuples A)) := by
  have hMle := LayerExc.map_centralizer_le_sup A
  have hYN := LayerExc.map_famWeylReps_le_normalizer (K := L) (LayerExc.torusTuples A)
  rw [LayerFacts.ggDer_succ]
  have h1 := (LayerFacts.ggDer_mono hMle k).trans
    ((LayerExc.ggDer_sup_le_of_le_normalizer hYN k).trans
      (sup_le le_rfl (LayerExc.ggDer_map_famWeylReps_le hk)))
  exact (Subgroup.commutator_mono h1 h1).trans
    (LayerExc.commutator_torus_sup_rootSpan_le fun α hα => hα.1)

private theorem perfect_le_rootSpan_kernelRoots_pi
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ} (S : LangSetup τ L p₀)
    (hp : p.Prime) {ι : Type} (a : ι → Fin τ.rank → Lˣ)
    (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    {P : Subgroup (ModGL τ L)}
    (hP : P ≤ S.Γ ⊓ Subgroup.centralizer (Set.range fun u => rootDiagUnit τ (a u)))
    (hperf : ⁅P, P⁆ = P) :
    P ≤ rootSpan τ L (kernelRoots (Pi.monoidHom fun u => rootCharHom (a u))) := by
  have hd : ∀ u, rootDiagUnit τ (a u) ∈ adjointGroup τ L := fun u =>
    CFSG.RankThree.PartOne.KE.twistedTorusOf_le_adjointGroup S.D.n S.D.Φ (hT u)
  have hF := pow_eq_one_of_mem_torusTuples_famGroup a hap hd
  obtain ⟨k, hk⟩ := exists_ggDer_famStabilizerSubgroup_le_reflection_of_pow hp
    (LayerExc.torusTuples (famGroup a hd)) hF
  have hder := ggDer_centralizer_le_rootSpan_famKernel (famGroup a hd) hk
  rw [famKernel_torusTuples_famGroup a hd] at hder
  have hΓle : S.Γ ≤ S.D.model := Subgroup.commutator_le_self S.D.model
  have hΓ : S.Γ ≤ adjointGroup τ L := hΓle.trans inf_le_left
  have hPX : P ≤ (Subgroup.centralizer (famGroup a hd : Set ↥(adjointGroup τ L))).map
      (adjointGroup τ L).subtype := by
    intro x hx
    obtain ⟨hxΓ, hxc⟩ := hP hx
    have hxL : x ∈ adjointGroup τ L := hΓ hxΓ
    have hmem : (⟨x, hxL⟩ : ↥(adjointGroup τ L)) ∈
        Subgroup.centralizer (famGroup a hd : Set ↥(adjointGroup τ L)) :=
      mem_centralizer_famGroup a hd (g := ⟨x, hxL⟩) (by simpa using hxc)
    exact Subgroup.mem_map.2 ⟨⟨x, hxL⟩, hmem, rfl⟩
  calc P = LayerFacts.ggDer P (k + 1) := (LayerFacts.ggDer_of_perfect hperf (k + 1)).symm
    _ ≤ LayerFacts.ggDer ((Subgroup.centralizer (famGroup a hd : Set ↥(adjointGroup τ L))).map
          (adjointGroup τ L).subtype) (k + 1) := LayerFacts.ggDer_mono hPX (k + 1)
    _ ≤ rootSpan τ L (kernelRoots (Pi.monoidHom fun u => rootCharHom (a u))) := hder

private theorem fam_subnormal_subgroupOf_of_open {G : Type*} [Group G] {X U : Subgroup G}
    (hUX : U ≤ X) (h : CFSG.Open.IsSubnormal U X) : (U.subgroupOf X).IsSubnormal :=
  (CFSG.ComponentClassification.AssemblyBPredicates.isSubnormal_top_iff_mathlib _).1
    ((CFSG.ComponentClassification.AssemblyBPredicates.isSubnormal_iff_open _ _).2
      ((CFSG.ComponentClassification.LBalance.subnormal_subgroupOf_iff hUX).2 h))

private theorem comp_le_or_commutator_eq_bot {G : Type*} [Group G] {X K U : Subgroup G}
    [Finite ↥X] (hK : IsComponentOf K X) (hU : IsSubnormal U X) : K ≤ U ∨ ⁅K, U⁆ = ⊥ := by
  have hUX : U ≤ X := CFSG.Open.IsSubnormal.le hU
  have hE' := (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open K X).2 hK
  have hK' := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
    hK.1).1 hE'
  rcases CFSG.LocalCores.component_subnormal_subgroup hK'
      (fam_subnormal_subgroupOf_of_open hUX hU) with h | h
  · exact Or.inl (CFSG.LocalCores.le_of_subgroupOf_le hK.1 h)
  · right
    have := CFSG.LocalCores.commutator_inf_eq_bot_of_subgroupOf hK.1 h
    rwa [inf_of_le_left hUX] at this

private theorem isSubnormal_of_le_of_le' {G : Type*} [Group G] {K C M : Subgroup G}
    (h : IsSubnormal K C) (hKM : K ≤ M) (hMC : M ≤ C) : IsSubnormal K M := by
  have := h.inf M
  rwa [inf_eq_left.2 hKM, inf_eq_right.2 hMC] at this

private theorem exists_noncomm_of_isQuasisimple {Q : Type*} [Group Q]
    (hQ : CFSG.Open.IsQuasisimple Q) : ∃ a b : Q, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hc : Subgroup.center Q = ⊤ :=
    (Subgroup.eq_top_iff' _).2 fun a => Subgroup.mem_center_iff.2 fun b => h b a
  have := hQ.2.toNontrivial
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  exact hxy (QuotientGroup.eq.2 (by rw [hc]; trivial))

theorem commute_rootSpan_inf_Γ_of_ne
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus)
    {O O' : Set.range (rationalRootsM S.ρ (Pi.monoidHom fun u => rootCharHom (a u)))}
    (hne : O ≠ O') :
    ∀ x ∈ rootSpan τ L O.1 ⊓ S.Γ, ∀ y ∈ rootSpan τ L O'.1 ⊓ S.Γ, Commute x y := by
  obtain ⟨_, i, rfl⟩ := O
  obtain ⟨_, j, rfl⟩ := O'
  have hker : ∀ γ ∈ kernelRoots (Pi.monoidHom fun u => rootCharHom (a u)),
      S.ρ γ ∈ kernelRoots (Pi.monoidHom fun u => rootCharHom (a u)) :=
    rho_mem_kernelRoots_pi S hT
  have hform : ∀ γ δ, iform (S.ρ γ) (S.ρ δ) = iform γ δ := S.frob.iform_eq
  intro x hx y hy
  exact commute_rootSpan_orbitRoots hker hform (fun h => hne (Subtype.ext h)) x hx.1 y hy.1

open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple in
theorem perfect_le_iSup_commutator_rationalSpanM
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ} (S : LangSetup τ L p₀)
    (hp : p.Prime) {ι : Type} (a : ι → Fin τ.rank → Lˣ)
    (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    {P : Subgroup (ModGL τ L)}
    (hP : P ≤ S.Γ ⊓ Subgroup.centralizer (Set.range fun u => rootDiagUnit τ (a u)))
    (hperf : ⁅P, P⁆ = P) :
    P ≤ ⨆ O : Set.range (rationalRootsM S.ρ (Pi.monoidHom fun u => rootCharHom (a u))),
      ⁅rootSpan τ L O.1 ⊓ S.Γ, rootSpan τ L O.1 ⊓ S.Γ⁆ := by
  classical
  set χ : Multiplicative (Fin τ.rank → ℤ) →* (ι → Lˣ) :=
    Pi.monoidHom fun u => rootCharHom (a u) with hχ
  have hker : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ := rho_mem_kernelRoots_pi S hT
  have hform : ∀ γ δ, iform (S.ρ γ) (S.ρ δ) = iform γ δ := S.frob.iform_eq
  have hΓle : S.Γ ≤ S.D.model := Subgroup.commutator_le_self S.D.model
  have hΓfix : ∀ x ∈ S.Γ, S.D.step x = x := fun x hx => (hΓle hx).2
  have hKU : P ≤ rootSpan τ L (kernelRoots χ) :=
    perfect_le_rootSpan_kernelRoots_pi S hp a hT hap hP hperf
  haveI : Finite (kernelRoots χ) := ((finite_setOf_isRoot τ).subset fun α h => h.1).to_subtype
  haveI : Finite (KernelComponent χ) := inferInstance
  haveI : Finite (Set.range (rationalRootsM S.ρ χ)) := (Set.finite_range _).to_subtype
  let A : Set.range (rationalRootsM S.ρ χ) → Subgroup (ModGL τ L) := fun O => rootSpan τ L O.1
  have hc : ∀ O O', O ≠ O' → ∀ x ∈ A O, ∀ y ∈ A O', Commute x y := by
    rintro ⟨_, i, rfl⟩ ⟨_, j, rfl⟩ hne
    exact commute_rootSpan_orbitRoots hker hform (fun h => hne (Subtype.ext h))
  have hF : ∀ O, ∀ x ∈ A O, S.D.step x ∈ A O := by
    rintro ⟨_, i, rfl⟩ x hx
    exact step_mem_rootSpan S (fun γ hγ => (orbitRoots_subset_kernelRoots hker i hγ).1)
      (orbitRoots_mapsTo i) hx
  have hU : ⨆ O, A O = rootSpan τ L (kernelRoots χ) := by
    refine le_antisymm (iSup_le fun O => ?_) ?_
    · obtain ⟨_, i, rfl⟩ := O
      exact rootSpan_mono (orbitRoots_subset_kernelRoots hker i)
    · refine le_trans (iSup_componentRootSpan L (χ := χ)).ge (iSup_le fun i => ?_)
      have h : componentRootSpan L χ i ≤ A ⟨_, i, rfl⟩ :=
        rootSpan_mono fun γ hγ => ⟨0, γ, hγ, rfl⟩
      exact h.trans (le_iSup A ⟨_, i, rfl⟩)
  have hAadj : ∀ O, A O ≤ adjointGroup τ L := fun O => rootSpan_le_adjointGroup L O.1
  have h1 := perfect_le_iSup_inf_fixed S.D.step A hc hF hperf (hKU.trans hU.ge)
    fun x hx => hΓfix x (Subgroup.mem_inf.1 (hP hx)).1
  have hc2 : ∀ O O', O ≠ O' → ∀ x ∈ A O ⊓ S.D.step.eqLocus (MonoidHom.id _),
      ∀ y ∈ A O' ⊓ S.D.step.eqLocus (MonoidHom.id _), Commute x y :=
    fun O O' hne x hx y hy => hc O O' hne x hx.1 y hy.1
  have h2 : P ≤ ⨆ O, A O ⊓ S.Γ := by
    refine (perfect_le_iSup_commutator (fun O => A O ⊓ S.D.step.eqLocus (MonoidHom.id _)) hc2
      hperf h1).trans (iSup_mono fun O => le_inf ?_ ?_)
    · exact (Subgroup.commutator_mono inf_le_left inf_le_left).trans
        (Subgroup.commutator_le_self _)
    · exact Subgroup.commutator_mono (fun x hx => ⟨hAadj O hx.1, hx.2⟩)
        (fun x hx => ⟨hAadj O hx.1, hx.2⟩)
  have hcΓ : ∀ O O', O ≠ O' → ∀ x ∈ A O ⊓ S.Γ, ∀ y ∈ A O' ⊓ S.Γ, Commute x y :=
    fun O O' hne x hx y hy => hc O O' hne x hx.1 y hy.1
  exact perfect_le_iSup_commutator (fun O => A O ⊓ S.Γ) hcΓ hperf h2

open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple in
theorem langFamilyComponentsInRootSpan
    :
    ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] (p₀ p : ℕ) (S : LangSetup τ L p₀),
      (τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) → p.Prime → p ≠ 2 → (p : L) ≠ 0 →
      ∀ (ι : Type) (a : ι → Fin τ.rank → Lˣ),
        (∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) → (∀ u j, a u j ^ p = 1) →
        ∀ K : Subgroup (ModGL τ L),
          IsComponentOf K (S.Γ ⊓ Subgroup.centralizer (Set.range fun u => rootDiagUnit τ (a u))) →
          ∃ i : KernelComponent (Pi.monoidHom fun u => rootCharHom (a u)),
            K ≤ rootSpan τ L {γ | ∃ (k : ℕ) (δ : Fin τ.rank → ℤ),
              δ ∈ componentRoots (Pi.monoidHom fun u => rootCharHom (a u)) i ∧
                γ = (S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k] δ} := by
  classical
  intro τ L _ _ p₀ p S _ hp _ _ ι a hT hap K hK
  set χ : Multiplicative (Fin τ.rank → ℤ) →* (ι → Lˣ) :=
    Pi.monoidHom fun u => rootCharHom (a u) with hχ
  have hker : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ := rho_mem_kernelRoots_pi S hT
  have hform : ∀ γ δ, iform (S.ρ γ) (S.ρ δ) = iform γ δ := S.frob.iform_eq
  have hΓle : S.Γ ≤ S.D.model := Subgroup.commutator_le_self S.D.model
  have hΓ : S.Γ ≤ adjointGroup τ L := hΓle.trans inf_le_left
  have hΓfix : ∀ x ∈ S.Γ, S.D.step x = x := fun x hx => (hΓle hx).2
  have hKperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.1 ⟨hK.2.2.1⟩
  have hKU : K ≤ rootSpan τ L (kernelRoots χ) :=
    perfect_le_rootSpan_kernelRoots_pi S hp a hT hap hK.1 hKperf
  haveI : Finite (kernelRoots χ) := ((finite_setOf_isRoot τ).subset fun α h => h.1).to_subtype
  haveI : Finite (KernelComponent χ) := inferInstance
  haveI : Finite (Set.range (orbitRoots S.ρ χ)) := (Set.finite_range _).to_subtype
  let A : Set.range (orbitRoots S.ρ χ) → Subgroup (ModGL τ L) := fun O => rootSpan τ L O.1
  have hc : ∀ O O', O ≠ O' → ∀ x ∈ A O, ∀ y ∈ A O', Commute x y := by
    rintro ⟨_, i, rfl⟩ ⟨_, j, rfl⟩ hne
    exact commute_rootSpan_orbitRoots hker hform (fun h => hne (Subtype.ext h))
  have hF : ∀ O, ∀ x ∈ A O, S.D.step x ∈ A O := by
    rintro ⟨_, i, rfl⟩ x hx
    exact step_mem_rootSpan S (fun γ hγ => (orbitRoots_subset_kernelRoots hker i hγ).1)
      (orbitRoots_mapsTo i) hx
  have hU : ⨆ O, A O = rootSpan τ L (kernelRoots χ) := by
    refine le_antisymm (iSup_le fun O => ?_) ?_
    · obtain ⟨_, i, rfl⟩ := O
      exact rootSpan_mono (orbitRoots_subset_kernelRoots hker i)
    · refine le_trans (iSup_componentRootSpan L (χ := χ)).ge (iSup_le fun i => ?_)
      have h : componentRootSpan L χ i ≤ A ⟨_, i, rfl⟩ :=
        rootSpan_mono fun γ hγ => ⟨0, γ, hγ, rfl⟩
      exact h.trans (le_iSup A ⟨_, i, rfl⟩)
  have hAadj : ∀ O, A O ≤ adjointGroup τ L := fun O => rootSpan_le_adjointGroup L O.1
  have h1 := perfect_le_iSup_inf_fixed S.D.step A hc hF hKperf (hKU.trans hU.ge)
    fun x hx => hΓfix x (Subgroup.mem_inf.1 (hK.1 hx)).1
  have hc2 : ∀ O O', O ≠ O' → ∀ x ∈ A O ⊓ S.D.step.eqLocus (MonoidHom.id _),
      ∀ y ∈ A O' ⊓ S.D.step.eqLocus (MonoidHom.id _), Commute x y :=
    fun O O' hne x hx y hy => hc O O' hne x hx.1 y hy.1
  have h2 : K ≤ ⨆ O, A O ⊓ S.Γ := by
    refine (perfect_le_iSup_commutator (fun O => A O ⊓ S.D.step.eqLocus (MonoidHom.id _)) hc2
      hKperf h1).trans (iSup_mono fun O => le_inf ?_ ?_)
    · exact (Subgroup.commutator_mono inf_le_left inf_le_left).trans
        (Subgroup.commutator_le_self _)
    · exact Subgroup.commutator_mono (fun x hx => ⟨hAadj O hx.1, hx.2⟩)
        (fun x hx => ⟨hAadj O hx.1, hx.2⟩)
  have hcent : ∀ O, A O ≤ Subgroup.centralizer (Set.range fun u => rootDiagUnit τ (a u)) := by
    rintro ⟨_, i, rfl⟩ x hx
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨u, rfl⟩
    have hsub : orbitRoots S.ρ χ i ⊆ rootCharKernel (a u) := fun γ hγ =>
      ⟨(orbitRoots_subset_kernelRoots hker i hγ).1, congrFun (orbitRoots_subset_kernelRoots hker i hγ).2 u⟩
    exact Subgroup.mem_centralizer_iff.1 (rootSpan_le_centralizer (a u) hsub hx) _ rfl
  set P' : Subgroup (ModGL τ L) := ⨆ O, A O ⊓ S.Γ with hP'
  have hP'X : P' ≤ S.Γ ⊓ Subgroup.centralizer (Set.range fun u => rootDiagUnit τ (a u)) :=
    iSup_le fun O => le_inf inf_le_right (inf_le_left.trans (hcent O))
  have hKP' : K ≤ P' := h2
  haveI : Finite S.D.model := S.finite
  haveI : Finite ↥P' := Finite.of_injective
    (Subgroup.inclusion (((hP'X.trans inf_le_left).trans hΓle) : P' ≤ S.D.model))
    (Subgroup.inclusion_injective _)
  have hKcomp : IsComponentOf K P' := ⟨hKP', isSubnormal_of_le_of_le' hK.2.1 hKP' hP'X, hK.2.2⟩
  have hnorm : ∀ O, ((A O ⊓ S.Γ).subgroupOf P').Normal := by
    intro O
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (le_iSup (fun O => A O ⊓ S.Γ) O)]
    refine iSup_le fun O' => ?_
    by_cases hOO : O' = O
    · rw [hOO]
      exact Subgroup.le_normalizer
    · refine le_trans ?_ (Subgroup.centralizer_le_normalizer (A O ⊓ S.Γ : Set (ModGL τ L)))
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hc O O' (Ne.symm hOO) y hy.1 x hx.1).eq
  have hsub : ∀ O, IsSubnormal (A O ⊓ S.Γ) P' := fun O =>
    IsSubnormal.step (le_iSup (fun O => A O ⊓ S.Γ) O) (hnorm O) (IsSubnormal.refl P')
  have hex : ∃ O, K ≤ A O ⊓ S.Γ := by
    by_contra hcon
    push Not at hcon
    have hcomm : ∀ O, ⁅K, A O ⊓ S.Γ⁆ = ⊥ := fun O =>
      (comp_le_or_commutator_eq_bot hKcomp (hsub O)).resolve_left (hcon O)
    have hP'c : P' ≤ Subgroup.centralizer (K : Set (ModGL τ L)) :=
      iSup_le fun O => Subgroup.commutator_eq_bot_iff_le_centralizer.1
        ((Subgroup.commutator_comm _ _).trans (hcomm O))
    have hKc : K ≤ Subgroup.centralizer (K : Set (ModGL τ L)) := hKP'.trans hP'c
    obtain ⟨x, y, hxy⟩ := exists_noncomm_of_isQuasisimple hK.2.2
    exact hxy (Subtype.ext (Subgroup.mem_centralizer_iff.1 (hKc y.2) x x.2))
  obtain ⟨⟨_, i, rfl⟩, hKi⟩ := hex
  exact ⟨i, hKi.trans inf_le_left⟩

end CFSG.StandardType.LangRat
