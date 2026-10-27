module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private structure fr_Rad {Γ : Type} [Fintype Γ] [DecidableEq Γ] (M : CoxeterMatrix Γ) (p : ℕ) where
  C : Matrix Γ Γ ℤ
  hC : GGIntCartan M C
  hM : GGIsWeylMatrixFixed M
  hp : p ≠ 2
  r : Γ → ZMod p
  i₀ : Γ
  hr₀ : r i₀ = 1
  hr : ∀ i, ∑ j, ((C i j : ℤ) : ZMod p) * r j = 0
  hker : ∀ x : Γ → ZMod p, (∀ i, ∑ j, ((C i j : ℤ) : ZMod p) * x j = 0) → x = x i₀ • r
  hconn : ∀ i j, Relation.ReflTransGen (fun a b => ((C a b : ℤ) : ZMod p) ≠ 0) i j
  k : ℕ
  ι : Fin k → Γ
  hι : ∀ c : Fin k → ZMod p, (∀ j, ∑ a, c a * ((C (ι a) j : ℤ) : ZMod p) = 0) → c = 0
  hcard : ¬ p ^ k ∣ Nat.card M.Group

private noncomputable def fr_phi {Γ : Type} [Fintype Γ] [DecidableEq Γ] {M : CoxeterMatrix Γ}
    {p : ℕ} (D : fr_Rad M p) (i : Γ) : Module.Dual (ZMod p) (Γ → ZMod p) :=
  ∑ j, ((D.C i j : ℤ) : ZMod p) • LinearMap.proj j

private theorem fr_phi_apply {Γ : Type} [Fintype Γ] [DecidableEq Γ] {M : CoxeterMatrix Γ}
    {p : ℕ} (D : fr_Rad M p) (i : Γ) (x : Γ → ZMod p) :
    fr_phi D i x = ∑ j, ((D.C i j : ℤ) : ZMod p) * x j := by
  simp [fr_phi]

private theorem fr_phi_single {Γ : Type} [Fintype Γ] [DecidableEq Γ] {M : CoxeterMatrix Γ}
    {p : ℕ} (D : fr_Rad M p) (i j : Γ) :
    fr_phi D i (Pi.single j 1) = ((D.C i j : ℤ) : ZMod p) := by
  simp [fr_phi_apply, Pi.single_apply]

private theorem fr_phi_self {Γ : Type} [Fintype Γ] [DecidableEq Γ] {M : CoxeterMatrix Γ}
    {p : ℕ} (D : fr_Rad M p) (i : Γ) : fr_phi D i (Pi.single i 1) = 2 := by
  rw [fr_phi_single, D.hC.1 i]
  norm_num

private noncomputable def fr_rho {Γ : Type} [Fintype Γ] [DecidableEq Γ] {M : CoxeterMatrix Γ}
    {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V] {C : Matrix Γ Γ ℤ}
    (hC : GGIntCartan M C) (h : Γ → V) (α : Γ → Module.Dual R V) (hα : ∀ i, α i (h i) = 2)
    (hP : ∀ i j, α i (h j) = (C i j : R)) : M.Group →* (V ≃ₗ[R] V) :=
  M.toCoxeterSystem.lift
    ⟨fun i => Module.reflection (hα i), isLiftable_reflection_of_intCartan hC h α hα hP⟩

private theorem fr_rho_simple {Γ : Type} [Fintype Γ] [DecidableEq Γ] {M : CoxeterMatrix Γ}
    {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V] {C : Matrix Γ Γ ℤ}
    (hC : GGIntCartan M C) (h : Γ → V) (α : Γ → Module.Dual R V) (hα : ∀ i, α i (h i) = 2)
    (hP : ∀ i j, α i (h j) = (C i j : R)) (i : Γ) :
    fr_rho hC h α hα hP (M.simple i) = Module.reflection (hα i) := by
  rw [← CoxeterMatrix.toCoxeterSystem_simple, fr_rho, CoxeterSystem.lift_apply_simple]

private theorem fr_rho_intertwine {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    {M : CoxeterMatrix Γ} {R : Type} [CommRing R] {V₁ V₂ : Type} [AddCommGroup V₁] [Module R V₁]
    [AddCommGroup V₂] [Module R V₂] {C : Matrix Γ Γ ℤ}
    (hC : GGIntCartan M C) (h₁ : Γ → V₁) (α₁ : Γ → Module.Dual R V₁)
    (hα₁ : ∀ i, α₁ i (h₁ i) = 2) (hP₁ : ∀ i j, α₁ i (h₁ j) = (C i j : R))
    (h₂ : Γ → V₂) (α₂ : Γ → Module.Dual R V₂)
    (hα₂ : ∀ i, α₂ i (h₂ i) = 2) (hP₂ : ∀ i j, α₂ i (h₂ j) = (C i j : R)) (π : V₁ →ₗ[R] V₂)
    (hπ : ∀ i x, π (Module.reflection (hα₁ i) x) = Module.reflection (hα₂ i) (π x))
    (g : M.Group) (x : V₁) :
    π (fr_rho hC h₁ α₁ hα₁ hP₁ g x) = fr_rho hC h₂ α₂ hα₂ hP₂ g (π x) := by
  induction g using M.toCoxeterSystem.simple_induction_left generalizing x with
  | one => simp
  | mul_simple_left w i ih =>
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      CoxeterMatrix.toCoxeterSystem_simple, fr_rho_simple, fr_rho_simple, hπ, ih]

private noncomputable def fr_rhoP {Γ : Type} [Fintype Γ] [DecidableEq Γ] {M : CoxeterMatrix Γ}
    {p : ℕ} (D : fr_Rad M p) : M.Group →* ((Γ → ZMod p) ≃ₗ[ZMod p] (Γ → ZMod p)) :=
  fr_rho D.hC (fun j => Pi.single j 1) (fr_phi D) (fr_phi_self D) (fr_phi_single D)

private theorem fr_rhoP_injective {Γ : Type} [Fintype Γ] [DecidableEq Γ] {M : CoxeterMatrix Γ}
    {p : ℕ} [Fact p.Prime] (D : fr_Rad M p) : Function.Injective (fr_rhoP D) := by
  have hind : LinearIndependent (ZMod p) (fun j : Γ => (Pi.single j 1 : Γ → ZMod p)) := by
    have : (fun j : Γ => (Pi.single j 1 : Γ → ZMod p)) = ⇑(Pi.basisFun (ZMod p) Γ) :=
      funext fun i => by simp [Pi.basisFun_apply]
    rw [this]
    exact (Pi.basisFun (ZMod p) Γ).linearIndependent
  exact ggCartanFaithfulInputFixed_holds p Fact.out D.hp Γ M D.C D.hM D.hC _
    (fun j => Pi.single j 1) (fr_phi D) (fr_phi_self D) (fr_phi_single D) hind

private theorem fr_rhoP_simple {Γ : Type} [Fintype Γ] [DecidableEq Γ] {M : CoxeterMatrix Γ}
    {p : ℕ} (D : fr_Rad M p) (i : Γ) :
    fr_rhoP D (M.simple i) = Module.reflection (fr_phi_self D i) :=
  fr_rho_simple _ _ _ _ _ i

private theorem fr_refl_apply {Γ : Type} [Fintype Γ] [DecidableEq Γ] {M : CoxeterMatrix Γ}
    {p : ℕ} (D : fr_Rad M p) (i : Γ) (x : Γ → ZMod p) :
    Module.reflection (fr_phi_self D i) x = x - fr_phi D i x • Pi.single i 1 := by
  simp [Module.reflection_apply]

private theorem fr_rhoP_rv {Γ : Type} [Fintype Γ] [DecidableEq Γ] {M : CoxeterMatrix Γ}
    {p : ℕ} (D : fr_Rad M p) (w : M.Group) : fr_rhoP D w D.r = D.r := by
  induction w using M.toCoxeterSystem.simple_induction_left with
  | one => simp
  | mul_simple_left w i ih =>
    rw [map_mul, LinearEquiv.mul_apply, ih, CoxeterMatrix.toCoxeterSystem_simple, fr_rhoP_simple,
      fr_refl_apply]
    have : fr_phi D i D.r = 0 := by
      rw [fr_phi_apply]
      exact D.hr i
    rw [this, zero_smul, sub_zero]

private def fr_Shape {Γ : Type} [Fintype Γ] [DecidableEq Γ] {M : CoxeterMatrix Γ} {p : ℕ}
    (D : fr_Rad M p) (g : M.Group) : Prop :=
  ∀ x, fr_rhoP D g x - x ∈ Submodule.span (ZMod p) {D.r}

private noncomputable def fr_lam {Γ : Type} [Fintype Γ] [DecidableEq Γ] {M : CoxeterMatrix Γ}
    {p : ℕ} (D : fr_Rad M p) (g : M.Group) : Module.Dual (ZMod p) (Γ → ZMod p) :=
  (LinearMap.proj D.i₀) ∘ₗ
    ((fr_rhoP D g : (Γ → ZMod p) →ₗ[ZMod p] (Γ → ZMod p)) - LinearMap.id)

private theorem fr_lam_apply {Γ : Type} [Fintype Γ] [DecidableEq Γ] {M : CoxeterMatrix Γ}
    {p : ℕ} (D : fr_Rad M p) (g : M.Group) (x : Γ → ZMod p) :
    fr_lam D g x = fr_rhoP D g x D.i₀ - x D.i₀ := by
  simp [fr_lam]

private theorem fr_shape_eq {Γ : Type} [Fintype Γ] [DecidableEq Γ] {M : CoxeterMatrix Γ}
    {p : ℕ} {D : fr_Rad M p} {g : M.Group} (hg : fr_Shape D g) (x : Γ → ZMod p) :
    fr_rhoP D g x = x + fr_lam D g x • D.r := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hg x)
  have h0 : fr_lam D g x = c := by
    rw [fr_lam_apply]
    have := congrFun hc D.i₀
    simp only [Pi.smul_apply, smul_eq_mul, D.hr₀, mul_one, Pi.sub_apply] at this
    exact this.symm
  rw [h0, hc]
  abel

private theorem fr_shape_one {Γ : Type} [Fintype Γ] [DecidableEq Γ] {M : CoxeterMatrix Γ}
    {p : ℕ} (D : fr_Rad M p) : fr_Shape D 1 := fun x => by simp

private theorem fr_lam_one {Γ : Type} [Fintype Γ] [DecidableEq Γ] {M : CoxeterMatrix Γ}
    {p : ℕ} (D : fr_Rad M p) : fr_lam D 1 = 0 := by
  ext x
  simp [fr_lam_apply]

private theorem fr_shape_mul {Γ : Type} [Fintype Γ] [DecidableEq Γ] {M : CoxeterMatrix Γ}
    {p : ℕ} {D : fr_Rad M p} {g g' : M.Group} (hg : fr_Shape D g) (hg' : fr_Shape D g') :
    fr_Shape D (g * g') ∧ fr_lam D (g * g') = fr_lam D g + fr_lam D g' := by
  have key : ∀ x, fr_rhoP D (g * g') x = x + (fr_lam D g x + fr_lam D g' x) • D.r := fun x => by
    rw [map_mul, LinearEquiv.mul_apply, fr_shape_eq hg', map_add, map_smul, fr_rhoP_rv,
      fr_shape_eq hg, add_smul]
    abel
  refine ⟨fun x => ?_, ?_⟩
  · rw [key]
    simpa using Submodule.smul_mem _ (fr_lam D g x + fr_lam D g' x)
      (Submodule.mem_span_singleton_self D.r)
  · refine LinearMap.ext fun x => ?_
    have h1 := congrFun (key x) D.i₀
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, D.hr₀, mul_one] at h1
    rw [LinearMap.add_apply, fr_lam_apply, h1]
    ring

private theorem fr_shape_conj {Γ : Type} [Fintype Γ] [DecidableEq Γ] {M : CoxeterMatrix Γ}
    {p : ℕ} {D : fr_Rad M p} {g : M.Group} (hg : fr_Shape D g) (w : M.Group) :
    fr_Shape D (w * g * w⁻¹) ∧
      fr_lam D (w * g * w⁻¹) =
        fr_lam D g ∘ₗ (fr_rhoP D w⁻¹ : (Γ → ZMod p) →ₗ[ZMod p] (Γ → ZMod p)) := by
  have key : ∀ x, fr_rhoP D (w * g * w⁻¹) x = x + fr_lam D g (fr_rhoP D w⁻¹ x) • D.r := fun x => by
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, fr_shape_eq hg, map_add,
      map_smul, fr_rhoP_rv]
    have : fr_rhoP D w (fr_rhoP D w⁻¹ x) = x := by
      rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
    rw [this]
  refine ⟨fun x => ?_, ?_⟩
  · rw [key]
    simpa using Submodule.smul_mem _ (fr_lam D g (fr_rhoP D w⁻¹ x))
      (Submodule.mem_span_singleton_self D.r)
  · refine LinearMap.ext fun x => ?_
    have h1 := congrFun (key x) D.i₀
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, D.hr₀, mul_one] at h1
    rw [LinearMap.comp_apply, fr_lam_apply, h1, add_sub_cancel_left]
    rfl

private theorem fr_lam_inj {Γ : Type} [Fintype Γ] [DecidableEq Γ] {M : CoxeterMatrix Γ}
    {p : ℕ} [Fact p.Prime] {D : fr_Rad M p} {g g' : M.Group} (hg : fr_Shape D g)
    (hg' : fr_Shape D g') (h : fr_lam D g = fr_lam D g') : g = g' := by
  apply fr_rhoP_injective D
  ext x : 1
  rw [fr_shape_eq hg, fr_shape_eq hg', h]

private def fr_Lam {Γ : Type} [Fintype Γ] [DecidableEq Γ] {M : CoxeterMatrix Γ} {p : ℕ}
    (D : fr_Rad M p) : Set (Module.Dual (ZMod p) (Γ → ZMod p)) :=
  {μ | ∃ g, fr_Shape D g ∧ fr_lam D g = μ}

private theorem fr_Lam_zero {Γ : Type} [Fintype Γ] [DecidableEq Γ] {M : CoxeterMatrix Γ}
    {p : ℕ} (D : fr_Rad M p) : (0 : Module.Dual (ZMod p) (Γ → ZMod p)) ∈ fr_Lam D :=
  ⟨1, fr_shape_one D, fr_lam_one D⟩

private theorem fr_Lam_add {Γ : Type} [Fintype Γ] [DecidableEq Γ] {M : CoxeterMatrix Γ}
    {p : ℕ} {D : fr_Rad M p} {μ ν : Module.Dual (ZMod p) (Γ → ZMod p)} (hμ : μ ∈ fr_Lam D)
    (hν : ν ∈ fr_Lam D) : μ + ν ∈ fr_Lam D := by
  obtain ⟨g, hg, rfl⟩ := hμ
  obtain ⟨g', hg', rfl⟩ := hν
  exact ⟨g * g', (fr_shape_mul hg hg').1, (fr_shape_mul hg hg').2⟩

private theorem fr_Lam_comp {Γ : Type} [Fintype Γ] [DecidableEq Γ] {M : CoxeterMatrix Γ}
    {p : ℕ} {D : fr_Rad M p} {μ : Module.Dual (ZMod p) (Γ → ZMod p)} (hμ : μ ∈ fr_Lam D)
    (w : M.Group) :
    μ ∘ₗ (fr_rhoP D w : (Γ → ZMod p) →ₗ[ZMod p] (Γ → ZMod p)) ∈ fr_Lam D := by
  obtain ⟨g, hg, rfl⟩ := hμ
  obtain ⟨h1, h2⟩ := fr_shape_conj hg w⁻¹
  refine ⟨w⁻¹ * g * w⁻¹⁻¹, h1, ?_⟩
  rw [h2, inv_inv]

private theorem fr_Lam_smul {Γ : Type} [Fintype Γ] [DecidableEq Γ] {M : CoxeterMatrix Γ}
    {p : ℕ} [Fact p.Prime] {D : fr_Rad M p} {μ : Module.Dual (ZMod p) (Γ → ZMod p)}
    (hμ : μ ∈ fr_Lam D) (c : ZMod p) : c • μ ∈ fr_Lam D := by
  rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul]
  generalize c.val = n
  induction n with
  | zero => simpa using fr_Lam_zero D
  | succ n ih => rw [succ_nsmul]; exact fr_Lam_add ih hμ

private theorem fr_Lam_sub {Γ : Type} [Fintype Γ] [DecidableEq Γ] {M : CoxeterMatrix Γ}
    {p : ℕ} [Fact p.Prime] {D : fr_Rad M p} {μ ν : Module.Dual (ZMod p) (Γ → ZMod p)}
    (hμ : μ ∈ fr_Lam D) (hν : ν ∈ fr_Lam D) : μ - ν ∈ fr_Lam D := by
  have : μ - ν = μ + (-1 : ZMod p) • ν := LinearMap.ext fun x => by
    simp [sub_eq_add_neg]
  rw [this]
  exact fr_Lam_add hμ (fr_Lam_smul hν _)

private theorem fr_refl_comp {Γ : Type} [Fintype Γ] [DecidableEq Γ] {M : CoxeterMatrix Γ}
    {p : ℕ} (D : fr_Rad M p) (μ : Module.Dual (ZMod p) (Γ → ZMod p)) (i : Γ) :
    μ ∘ₗ (fr_rhoP D (M.simple i) : (Γ → ZMod p) →ₗ[ZMod p] (Γ → ZMod p)) =
      μ - μ (Pi.single i 1) • fr_phi D i := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, fr_rhoP_simple, fr_refl_apply, map_sub, map_smul]
  simp [mul_comm]

private theorem fr_phi_mem_start {Γ : Type} [Fintype Γ] [DecidableEq Γ] {M : CoxeterMatrix Γ}
    {p : ℕ} [Fact p.Prime] {D : fr_Rad M p} {μ : Module.Dual (ZMod p) (Γ → ZMod p)}
    (hμ : μ ∈ fr_Lam D) (i : Γ) (hi : μ (Pi.single i 1) ≠ 0) : fr_phi D i ∈ fr_Lam D := by
  have h1 := fr_Lam_sub hμ (fr_Lam_comp hμ (M.simple i))
  rw [fr_refl_comp, sub_sub_cancel] at h1
  have := fr_Lam_smul h1 (μ (Pi.single i 1))⁻¹
  rwa [smul_smul, inv_mul_cancel₀ hi, one_smul] at this

private theorem fr_phi_mem_adj {Γ : Type} [Fintype Γ] [DecidableEq Γ] {M : CoxeterMatrix Γ}
    {p : ℕ} [Fact p.Prime] {D : fr_Rad M p} {i j : Γ} (hi : fr_phi D i ∈ fr_Lam D)
    (hij : ((D.C i j : ℤ) : ZMod p) ≠ 0) : fr_phi D j ∈ fr_Lam D := by
  have h1 := fr_Lam_sub hi (fr_Lam_comp hi (M.simple j))
  rw [fr_refl_comp, sub_sub_cancel] at h1
  have hc : fr_phi D i (Pi.single j 1) ≠ 0 := by
    rw [fr_phi_single]
    exact hij
  have := fr_Lam_smul h1 (fr_phi D i (Pi.single j 1))⁻¹
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

private theorem fr_phi_mem_all {Γ : Type} [Fintype Γ] [DecidableEq Γ] {M : CoxeterMatrix Γ}
    {p : ℕ} [Fact p.Prime] {D : fr_Rad M p} {g₀ : M.Group} (hg₀ : fr_Shape D g₀) (hne : g₀ ≠ 1)
    (k : Γ) : fr_phi D k ∈ fr_Lam D := by
  have hlam : fr_lam D g₀ ≠ 0 := fun h0 =>
    hne (fr_lam_inj hg₀ (fr_shape_one D) (by rw [h0, fr_lam_one]))
  obtain ⟨i, hi⟩ : ∃ i, fr_lam D g₀ (Pi.single i 1) ≠ 0 := by
    by_contra hcon
    exact hlam ((Pi.basisFun (ZMod p) Γ).ext fun i => by
      simpa using not_not.mp (fun hne => hcon ⟨i, hne⟩))
  have h0 : fr_phi D i ∈ fr_Lam D := fr_phi_mem_start ⟨g₀, hg₀, rfl⟩ i hi
  induction D.hconn i k with
  | refl => exact h0
  | tail _ hbc ih => exact fr_phi_mem_adj ih hbc

private theorem fr_shape_trivial {Γ : Type} [Fintype Γ] [DecidableEq Γ] {M : CoxeterMatrix Γ}
    {p : ℕ} [Fact p.Prime] (D : fr_Rad M p) (g₀ : M.Group) (hg₀ : fr_Shape D g₀) : g₀ = 1 := by
  by_contra hne
  have hall := fr_phi_mem_all hg₀ hne
  choose ψ hψS hψ using fun c : Fin D.k → ZMod p =>
    (show (∑ a, c a • fr_phi D (D.ι a)) ∈ fr_Lam D from
      Finset.sum_induction _ (· ∈ fr_Lam D) (fun a b => fr_Lam_add) (fr_Lam_zero D)
        (fun a _ => fr_Lam_smul (hall _) _))
  have hmul : ∀ c c', ψ (c + c') = ψ c * ψ c' := fun c c' => by
    refine fr_lam_inj (hψS _) (fr_shape_mul (hψS c) (hψS c')).1 ?_
    rw [hψ, (fr_shape_mul (hψS c) (hψS c')).2, hψ, hψ]
    simp [add_smul, Finset.sum_add_distrib]
  have h0 : ψ 0 = 1 := fr_lam_inj (hψS 0) (fr_shape_one D) (by rw [hψ, fr_lam_one]; simp)
  have hψinj : Function.Injective ψ := by
    intro c c' hcc
    have h1 : ∑ a, c a • fr_phi D (D.ι a) = ∑ a, c' a • fr_phi D (D.ι a) := by
      rw [← hψ, ← hψ, hcc]
    have h2 : ∀ j, ∑ a, (c a - c' a) * ((D.C (D.ι a) j : ℤ) : ZMod p) = 0 := fun j => by
      have := congrArg (fun μ : Module.Dual (ZMod p) (Γ → ZMod p) => μ (Pi.single j 1)) h1
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, fr_phi_single, smul_eq_mul] at this
      simp only [sub_mul, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr this
    have h3 := D.hι (fun a => c a - c' a) h2
    ext a
    exact sub_eq_zero.mp (congrFun h3 a)
  let f : Multiplicative (Fin D.k → ZMod p) →* M.Group :=
    { toFun := fun c => ψ (Multiplicative.toAdd c)
      map_one' := by simpa using h0
      map_mul' := fun a b => by
        simpa using hmul (Multiplicative.toAdd a) (Multiplicative.toAdd b) }
  have hf : Function.Injective f := fun a b hab => Multiplicative.toAdd.injective (hψinj hab)
  have hdvd := Subgroup.card_dvd_of_injective f hf
  have hcardE : Nat.card (Multiplicative (Fin D.k → ZMod p)) = p ^ D.k := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative]
    simp [ZMod.card]
  rw [hcardE] at hdvd
  exact D.hcard hdvd

private theorem fr_faithful_core {Γ : Type} [Fintype Γ] [DecidableEq Γ] {M : CoxeterMatrix Γ}
    {p : ℕ} [Fact p.Prime] (D : fr_Rad M p) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (h : Γ → V) (α : Γ → Module.Dual (ZMod p) V) (hα : ∀ i, α i (h i) = 2)
    (hP : ∀ i j, α i (h j) = ((D.C i j : ℤ) : ZMod p)) :
    Function.Injective (fr_rho D.hC h α hα hP) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply fr_shape_trivial D g
  intro x
  let π : (Γ → ZMod p) →ₗ[ZMod p] V := ∑ j, (LinearMap.proj j).smulRight (h j)
  have hπ : ∀ x, π x = ∑ j, x j • h j := fun x => by simp [π]
  have hαπ : ∀ i x, α i (π x) = fr_phi D i x := fun i x => by
    rw [hπ, map_sum, fr_phi_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hP, smul_eq_mul, mul_comm]
  have hπe : ∀ i, π (Pi.single i 1) = h i := fun i => by
    rw [hπ]
    simp [Pi.single_apply]
  have hπr : ∀ i x, π (Module.reflection (fr_phi_self D i) x) =
      Module.reflection (hα i) (π x) := by
    intro i x
    rw [fr_refl_apply, Module.reflection_apply, map_sub, map_smul, hαπ, hπe]
  have hint := fr_rho_intertwine D.hC (fun j => Pi.single j 1) (fr_phi D) (fr_phi_self D)
    (fr_phi_single D) h α hα hP π hπr g x
  have h1 : π (fr_rhoP D g x - x) = 0 := by
    rw [map_sub]
    change π (fr_rho _ _ _ _ _ g x) - π x = 0
    rw [hint, hg]
    simp
  have h2 : ∀ i, ∑ j, ((D.C i j : ℤ) : ZMod p) * (fr_rhoP D g x - x) j = 0 := fun i => by
    have := hαπ i (fr_rhoP D g x - x)
    rw [h1, map_zero, fr_phi_apply] at this
    exact this.symm
  have h3 := D.hker _ h2
  rw [Submodule.mem_span_singleton]
  exact ⟨(fr_rhoP D g x - x) D.i₀, h3.symm⟩

theorem ggCoxeterIso_of_injective_lift {Γ : Type} {M : CoxeterMatrix Γ} {R : Type} [CommRing R]
    {V : Type} [AddCommGroup V] [Module R V] {C : Matrix Γ Γ ℤ} (hC : GGIntCartan M C)
    (h : Γ → V) (α : Γ → Module.Dual R V) (hα : ∀ i, α i (h i) = 2)
    (hP : ∀ i j, α i (h j) = (C i j : R))
    (hinj : Function.Injective (M.toCoxeterSystem.lift
      ⟨fun i => Module.reflection (hα i), isLiftable_reflection_of_intCartan hC h α hα hP⟩))
    (s : Γ → V ≃ₗ[R] V) (hs : ∀ i v, s i v = v - α i v • h i) :
    ∃ f : M.Group ≃* ↥(Subgroup.closure (Set.range s)),
      ∀ i, (f (M.simple i) : V ≃ₗ[R] V) = s i := by
  have hsr : ∀ i, s i = Module.reflection (hα i) := fun i =>
    LinearEquiv.ext fun v => by rw [hs, Module.reflection_apply]
  set F := M.toCoxeterSystem.lift
    ⟨fun i => Module.reflection (hα i), isLiftable_reflection_of_intCartan hC h α hα hP⟩ with hF
  have hsimple : ∀ i, F (M.simple i) = s i := fun i => by
    rw [← CoxeterMatrix.toCoxeterSystem_simple, hF, CoxeterSystem.lift_apply_simple, hsr]
  have hcomp : (⇑F ∘ M.toCoxeterSystem.simple) = s := funext fun i => by
    rw [Function.comp_apply, CoxeterMatrix.toCoxeterSystem_simple, hsimple]
  have hrange : F.range = Subgroup.closure (Set.range s) := by
    rw [MonoidHom.range_eq_map, ← M.toCoxeterSystem.subgroup_closure_range_simple,
      MonoidHom.map_closure, ← Set.range_comp, hcomp]
  refine ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange), fun i => ?_⟩
  rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply, hsimple]

theorem ggCoxeterFaithful_of_radical {Γ : Type} {M : CoxeterMatrix Γ} [Fintype Γ] [DecidableEq Γ]
    {C : Matrix Γ Γ ℤ} (hC : GGIntCartan M C) (hM : GGIsWeylMatrixFixed M) {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (r : Γ → ZMod p) (i₀ : Γ) (hr₀ : r i₀ = 1)
    (hr : ∀ i, ∑ j, (C i j : ZMod p) * r j = 0)
    (hker : ∀ x : Γ → ZMod p, (∀ i, ∑ j, (C i j : ZMod p) * x j = 0) → x = x i₀ • r)
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => (C a b : ZMod p) ≠ 0) i j)
    {k : ℕ} (ι : Fin k → Γ)
    (hι : ∀ c : Fin k → ZMod p, (∀ j, ∑ a, c a * (C (ι a) j : ZMod p) = 0) → c = 0)
    (hcard : ¬ p ^ k ∣ Nat.card M.Group) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (h : Γ → V) (α : Γ → Module.Dual (ZMod p) V) (hα : ∀ i, α i (h i) = 2)
    (hP : ∀ i j, α i (h j) = (C i j : ZMod p)) :
    Function.Injective (M.toCoxeterSystem.lift
      ⟨fun i => Module.reflection (hα i), isLiftable_reflection_of_intCartan hC h α hα hP⟩) :=
  fr_faithful_core ⟨C, hC, hM, hp, r, i₀, hr₀, hr, hker, hconn, k, ι, hι, hcard⟩ h α hα hP

end CFSG.StandardType

end
