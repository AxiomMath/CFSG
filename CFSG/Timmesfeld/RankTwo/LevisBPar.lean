module

public import CFSG.Timmesfeld.RankTwo.LevisBCone
public import CFSG.Timmesfeld.RankTwo.ModelG2
public import CFSG.LieType.Steinberg.PartB

public section

namespace CFSG.Timmesfeld.RankTwo

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.Timmesfeld.GradedPresentation
open scoped commutatorElement

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {k : Type*} [Field k]
  {x : (Fin D.rank → ℤ) → k → K}

open Classical in
@[expose] noncomputable def phiOf (D : UniversalRootDatum K) (x : (Fin D.rank → ℤ) → k → K)
    {G : Type*} [Group G] (ψ : (Fin D.rank → ℤ) → k → G) : ∀ γ, D.rootGroup γ → G :=
  fun γ y => if h : ∃ c, x γ c = y then ψ γ h.choose else 1

section Param

variable (hx : IsParametrization (Φ := RootSystem.ofCartan D.isFiniteType D.divisible)
  D.rootGroup x)
include hx

theorem x_mem_rootGroup {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) (c : k) :
    x γ c ∈ D.rootGroup γ :=
  ((hx γ hγ).1 _).2 ⟨c, rfl⟩

theorem exists_x_eq {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) {y : K} (hy : y ∈ D.rootGroup γ) :
    ∃ c, x γ c = y :=
  ((hx γ hγ).1 y).1 hy

theorem phiOf_x {G : Type*} [Group G] (ψ : (Fin D.rank → ℤ) → k → G) {γ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) (c : k) (hy : x γ c ∈ D.rootGroup γ) :
    phiOf D x ψ γ ⟨x γ c, hy⟩ = ψ γ c := by
  classical
  have h : ∃ c', x γ c' = x γ c := ⟨c, rfl⟩
  simp only [phiOf, dite_eq_left h]
  exact congrArg (ψ γ) ((hx γ hγ).2.2 h.choose_spec)

theorem range_phiOf {G : Type*} [Group G] (ψ : (Fin D.rank → ℤ) → k → G) {γ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) : Set.range (phiOf D x ψ γ) = Set.range (ψ γ) := by
  ext g
  constructor
  · rintro ⟨⟨y, hy⟩, rfl⟩
    obtain ⟨c, rfl⟩ := exists_x_eq hx hγ hy
    exact ⟨c, (phiOf_x hx ψ hγ c hy).symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨⟨x γ c, x_mem_rootGroup hx hγ c⟩, phiOf_x hx ψ hγ c _⟩

theorem isPGroup_of_param [CharP k 2] {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) :
    IsPGroup 2 (D.rootGroup γ) := by
  intro y
  refine ⟨1, Subtype.ext ?_⟩
  obtain ⟨c, hc⟩ := exists_x_eq hx hγ y.2
  rw [pow_one, Subgroup.coe_pow, ← hc, sq, ← (hx γ hγ).2.1, CharTwo.add_self_eq_zero]
  have h0 := (hx γ hγ).2.1 0 0
  rw [add_zero] at h0
  exact left_eq_mul.1 h0

variable (hW : ∀ i, ∀ β ∈ D.roots, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ (t : kˣ) (u : k),
    weylElement x i t * x β u * (weylElement x i t)⁻¹ =
      x (CFSG.LieType.RootSystem.reflection D.cartan i β)
        ((ε : k) * ((t ^ (-(∑ j, D.cartan i j * β j)) : kˣ) : k) * u))
include hW

omit hx in
theorem weylElement_conj_x [CharP k 2] (i : Fin D.rank) {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots)
    (c : k) : weylElement x i 1 * x γ c * (weylElement x i 1)⁻¹ =
      x ((RootSystem.ofCartan D.isFiniteType D.divisible).refl i γ) c := by
  obtain ⟨ε, hε, hn⟩ := hW i γ hγ
  rw [hn 1 c, one_zpow, Units.val_one, mul_one]
  have hε1 : (ε : k) = 1 := by
    rcases hε with rfl | rfl
    · simp
    · simp [CharTwo.neg_eq]
  rw [hε1, one_mul]
  rfl

theorem conj_mem_refl (i : Fin D.rank) {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) {y : K}
    (hy : y ∈ D.rootGroup γ) :
    weylElement x i 1 * y * (weylElement x i 1)⁻¹ ∈
      D.rootGroup ((RootSystem.ofCartan D.isFiniteType D.divisible).refl i γ) := by
  obtain ⟨c, rfl⟩ := exists_x_eq hx hγ hy
  obtain ⟨ε, -, hn⟩ := hW i γ hγ
  rw [hn 1 c]
  exact x_mem_rootGroup hx ((RootSystem.ofCartan D.isFiniteType D.divisible).refl_mem i γ hγ) _

theorem conj_phiOf_refl [CharP k 2] {G : Type*} [Group G] (ψ : (Fin D.rank → ℤ) → k → G)
    (ñ : Fin D.rank → G) (p : Fin D.rank → Prop) {P : Set (Fin D.rank → ℤ)}
    (hP : P ⊆ D.roots)
    (hψ : ∀ i, p i → ∀ γ ∈ P, ∀ c, ñ i * ψ γ c * (ñ i)⁻¹ =
      ψ ((RootSystem.ofCartan D.isFiniteType D.divisible).refl i γ) c) :
    ∀ i, p i → ∀ γ ∈ P, ∀ (z : D.rootGroup γ)
      (y : D.rootGroup ((RootSystem.ofCartan D.isFiniteType D.divisible).refl i γ)),
      (y : K) = weylElement x i 1 * z * (weylElement x i 1)⁻¹ →
        ñ i * phiOf D x ψ γ z * (ñ i)⁻¹ =
          phiOf D x ψ ((RootSystem.ofCartan D.isFiniteType D.divisible).refl i γ) y := by
  intro i hi γ hγ z y hy
  have hγR := hP hγ
  have hsR := (RootSystem.ofCartan D.isFiniteType D.divisible).refl_mem i γ hγR
  obtain ⟨⟨z, hz⟩, rfl⟩ : ∃ z', z' = z := ⟨z, rfl⟩
  obtain ⟨c, rfl⟩ := exists_x_eq hx hγR hz
  obtain ⟨⟨y, hy'⟩, rfl⟩ : ∃ y', y' = y := ⟨y, rfl⟩
  have e : y = x ((RootSystem.ofCartan D.isFiniteType D.divisible).refl i γ) c := by
    rw [show y = _ from hy, weylElement_conj_x hW i hγR c]
  subst e
  rw [phiOf_x hx ψ hγR c hz, phiOf_x hx ψ hsR c hy']
  exact hψ i hi γ hγ c

end Param

omit [Field k] in
theorem extendsToHom_rankOne {k : Type} [Field k]
    {x : (Fin D.rank → ℤ) → k → K}
    (hx : IsParametrization (Φ := RootSystem.ofCartan D.isFiniteType D.divisible)
      D.rootGroup x) (i : Fin D.rank)
    {φ : Matrix.SpecialLinearGroup (Fin 2) k →* K} (hφ : Function.Injective φ)
    (hφU : ∀ c, φ (sl2Upper c) = x (Pi.single i 1) c)
    (hφL : ∀ c, φ (sl2Lower c) = x (-Pi.single i 1) c) {G : Type*} [Group G]
    (ψ : (Fin D.rank → ℤ) → k → G) {Θ : Matrix.SpecialLinearGroup (Fin 2) k →* G}
    (hΘU : ∀ c, Θ (sl2Upper c) = ψ (Pi.single i 1) c)
    (hΘL : ∀ c, Θ (sl2Lower c) = ψ (-Pi.single i 1) c) :
    ExtendsToHom D.rootGroup {Pi.single i 1, -Pi.single i 1} (phiOf D x ψ) := by
  set e := MonoidHom.ofInjective hφ with he
  have hpos : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  have hneg : (-Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ hpos
  refine ⟨φ.range, Θ.comp e.symm.toMonoidHom, fun γ hγ z => ?_⟩
  obtain ⟨z, hz⟩ := z
  rcases hγ with rfl | hγ
  · obtain ⟨c, rfl⟩ := exists_x_eq hx hpos hz
    refine ⟨⟨sl2Upper c, hφU c⟩, ?_⟩
    have h1 : e.symm ⟨x (Pi.single i 1) c, ⟨sl2Upper c, hφU c⟩⟩ = sl2Upper c :=
      e.symm_apply_eq.2 (Subtype.ext (hφU c).symm)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1, hΘU]
    exact (phiOf_x hx ψ hpos c hz).symm
  · rw [Set.mem_singleton_iff] at hγ
    subst hγ
    obtain ⟨c, rfl⟩ := exists_x_eq hx hneg hz
    refine ⟨⟨sl2Lower c, hφL c⟩, ?_⟩
    have h1 : e.symm ⟨x (-Pi.single i 1) c, ⟨sl2Lower c, hφL c⟩⟩ = sl2Lower c :=
      e.symm_apply_eq.2 (Subtype.ext (hφL c).symm)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1, hΘL]
    exact (phiOf_x hx ψ hneg c hz).symm

omit [Field k] in
theorem extendsToHom_of_wordRels {k : Type} [Field k] [Finite k]
    {x : (Fin D.rank → ℤ) → k → K}
    (hx : IsParametrization (Φ := RootSystem.ofCartan D.isFiniteType D.divisible)
      D.rootGroup x)
    {ι : Type} [Fintype ι] [DecidableEq ι] {cm : ι → k → ι → k → FreeGroup (Σ _ : ι, k)}
    {ht : ι → ℕ} (hgr : ∀ α s β t, cm α s β t ∈ above (F := fun _ => k) ht (max (ht α) (ht β)))
    (r : ι → Fin D.rank → ℤ) (hr : Function.Injective r) (hrR : ∀ i, r i ∈ D.roots)
    (hrelK : ∀ w ∈ rels (F := fun _ => k) cm,
      FreeGroup.lift (fun g : Σ _ : ι, k => x (r g.1) g.2) w = 1)
    (L : List ι) (hL : ∀ i, i ∈ L) (hprod : ProdInjectiveFor D.rootGroup (L.map r))
    {P : Set (Fin D.rank → ℤ)} (hP : ∀ γ ∈ P, ∃ i, r i = γ) {G : Type*} [Group G]
    (ψ : (Fin D.rank → ℤ) → k → G)
    (hψ : ∀ w ∈ rels (F := fun _ => k) cm,
      FreeGroup.lift (fun g : Σ _ : ι, k => ψ (r g.1) g.2) w = 1) :
    ExtendsToHom D.rootGroup P (phiOf D x ψ) := by
  have := Fintype.ofFinite k
  exact extendsToHom_of_rels (F := fun _ => k) hgr r (fun i c => x (r i) c)
    (fun i c => x_mem_rootGroup hx (hrR i) c) hrelK L
    (injective_prod_of_prodInjectiveFor (F := fun _ => k) r hr (fun i c => x (r i) c)
      (fun i c => x_mem_rootGroup hx (hrR i) c) (fun i => (hx _ (hrR i)).2.2) L hL hprod) hP
    (fun i y hy => exists_x_eq hx (hrR i) hy) (fun g => ψ (r g.1) g.2) hψ
    (fun i c => phiOf_x hx ψ (hrR i) c _)

end CFSG.Timmesfeld.RankTwo
