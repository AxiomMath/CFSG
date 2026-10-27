module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesDensity
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.QuasithinUnique.Setup.SL2Modules

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

def invBilin {K M : Type*} [Group K] [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : Representation (ZMod 2) K M) :
    Submodule (ZMod 2) (LinearMap.BilinForm (ZMod 2) M) where
  carrier := {β | ∀ k x y, β (ρ k x) (ρ k y) = β x y}
  zero_mem' := by intro k x y; simp
  add_mem' := by
    intro β γ hβ hγ k x y
    simp only [LinearMap.add_apply, hβ k x y, hγ k x y]
  smul_mem' := by
    intro a β hβ k x y
    simp only [LinearMap.smul_apply, hβ k x y]

@[expose] def dualToForms {K M Z : Type*} [Group K] [AddCommGroup M] [Module (ZMod 2) M]
    [AddCommGroup Z] [Module (ZMod 2) Z] (ρ : Representation (ZMod 2) K M)
    (c : M →ₗ[ZMod 2] M →ₗ[ZMod 2] Z) (hc : ∀ k x y, c (ρ k x) (ρ k y) = c x y) :
    Module.Dual (ZMod 2) Z →ₗ[ZMod 2] invBilin ρ where
  toFun l := ⟨{ toFun := fun x => l.comp (c x)
                map_add' := by
                  intro x y
                  refine LinearMap.ext fun z => ?_
                  simp [map_add]
                map_smul' := by
                  intro a x
                  refine LinearMap.ext fun z => ?_
                  simp [map_smul] }, by
    intro k x y
    show (l.comp (c (ρ k x))) (ρ k y) = (l.comp (c x)) y
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hc k x y]⟩
  map_add' l m := by
    refine Subtype.ext ?_
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    simp
  map_smul' a l := by
    refine Subtype.ext ?_
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    simp

theorem dualToForms_apply {K M Z : Type*} [Group K] [AddCommGroup M] [Module (ZMod 2) M]
    [AddCommGroup Z] [Module (ZMod 2) Z] (ρ : Representation (ZMod 2) K M)
    (c : M →ₗ[ZMod 2] M →ₗ[ZMod 2] Z) (hc : ∀ k x y, c (ρ k x) (ρ k y) = c x y)
    (l : Module.Dual (ZMod 2) Z) (x y : M) :
    (dualToForms ρ c hc l : LinearMap.BilinForm (ZMod 2) M) x y = l (c x y) := rfl

theorem dualToForms_injective {K M Z : Type*} [Group K] [AddCommGroup M] [Module (ZMod 2) M]
    [AddCommGroup Z] [Module (ZMod 2) Z] (ρ : Representation (ZMod 2) K M)
    (c : M →ₗ[ZMod 2] M →ₗ[ZMod 2] Z) (hc : ∀ k x y, c (ρ k x) (ρ k y) = c x y)
    (hspan : Submodule.span (ZMod 2) (Set.range fun p : M × M => c p.1 p.2) = ⊤) :
    Function.Injective (dualToForms ρ c hc) := by
  intro l m h
  have h' : ∀ p : M × M, l (c p.1 p.2) = m (c p.1 p.2) := by
    intro p
    have h2 := congrArg (fun β : invBilin ρ =>
      (β : LinearMap.BilinForm (ZMod 2) M) p.1 p.2) h
    simpa [dualToForms_apply] using h2
  exact LinearMap.ext_on_range hspan h'

theorem natCard_dual_eq {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] :
    Nat.card (Module.Dual (ZMod 2) V) = Nat.card V := by
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  haveI : Finite (Module.Dual (ZMod 2) V) := Module.finite_of_finite (ZMod 2)
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Module.Dual (ZMod 2) V),
    Subspace.dual_finrank_eq]
  exact (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)).symm

theorem card_invBilin_le {K M : Type*} [Group K] [AddCommGroup M] [Module (ZMod 2) M]
    [Finite M] (ρ : Representation (ZMod 2) K M) [Fact ρ.IsIrreducible] :
    Nat.card (invBilin ρ) ≤ Nat.card (EndRing ρ) := by
  classical
  haveI : Module.Finite (ZMod 2) M := Module.Finite.of_finite
  haveI hfinForms : Finite (LinearMap.BilinForm (ZMod 2) M) := Module.finite_of_finite (ZMod 2)
  haveI hfinEnd : Finite (EndRing ρ) := finite_endRing ρ
  by_cases h : ∃ β₀ : LinearMap.BilinForm (ZMod 2) M,
      (∀ k x y, β₀ (ρ k x) (ρ k y) = β₀ x y) ∧ β₀ ≠ 0
  · obtain ⟨β₀, hβ₀, hβ₀ne⟩ := h
    have hker : LinearMap.ker β₀ = ⊥ := by
      obtain ⟨-, hirr⟩ := (isIrreducible_iff ρ).mp Fact.out
      rcases hirr (LinearMap.ker β₀) (by
        intro k x hx
        rw [LinearMap.mem_ker] at hx ⊢
        refine LinearMap.ext fun y => ?_
        have hy : ρ k (ρ k⁻¹ y) = y := by simp
        rw [← hy, hβ₀ k x (ρ k⁻¹ y)]
        simp [hx]) with hbot | htop
      · exact hbot
      · exfalso
        refine hβ₀ne (LinearMap.ext fun x => ?_)
        have hx : x ∈ LinearMap.ker β₀ := by rw [htop]; exact Submodule.mem_top
        rwa [LinearMap.mem_ker] at hx
    have hinj : Function.Injective β₀ := by
      intro x y hxy
      have hmem : x - y ∈ LinearMap.ker β₀ := by
        rw [LinearMap.mem_ker, map_sub, hxy, sub_self]
      rw [hker, Submodule.mem_bot] at hmem
      exact sub_eq_zero.mp hmem
    let e : M ≃ₗ[ZMod 2] Module.Dual (ZMod 2) M :=
      LinearEquiv.ofInjectiveOfFinrankEq β₀ hinj (Subspace.dual_finrank_eq).symm
    have he : ∀ x, e x = β₀ x := fun x => LinearMap.congr_fun
      (LinearEquiv.coe_ofInjectiveOfFinrankEq β₀ hinj (Subspace.dual_finrank_eq).symm) x
    let F : EndRing ρ → invBilin ρ := fun ψ =>
      ⟨LinearMap.comp β₀ (ψ.restrictScalars (ZMod 2)), by
        intro k x y
        have hψ : (ψ : M → M) (ρ k x) = ρ k ((ψ : M → M) x) :=
          ψ.map_smul (⟨ρ k, Algebra.subset_adjoin ⟨k, rfl⟩⟩ : spanAlg ρ) x
        show β₀ ((ψ : M → M) (ρ k x)) (ρ k y) = β₀ ((ψ : M → M) x) y
        rw [hψ, hβ₀ k ((ψ : M → M) x) y]⟩
    have hsurj : Function.Surjective F := by
      intro β
      have hBinv : ∀ k x y,
          (β : LinearMap.BilinForm (ZMod 2) M) (ρ k x) (ρ k y) =
            (β : LinearMap.BilinForm (ZMod 2) M) x y := β.2
      set φ : M →ₗ[ZMod 2] M :=
        e.symm.toLinearMap.comp (β : M →ₗ[ZMod 2] Module.Dual (ZMod 2) M) with hφ
      have hβφ : ∀ x, β₀ (φ x) = (β : LinearMap.BilinForm (ZMod 2) M) x := by
        intro x
        have h1 : e (φ x) = (β : LinearMap.BilinForm (ZMod 2) M) x := by
          rw [hφ]
          simp
        rw [← he (φ x)]
        exact h1
      have hcomm : ∀ k x, φ (ρ k x) = ρ k (φ x) := by
        intro k x
        refine e.injective ?_
        rw [he, he, hβφ (ρ k x)]
        ext y
        have hy : ρ k (ρ k⁻¹ y) = y := by simp
        calc (β : LinearMap.BilinForm (ZMod 2) M) (ρ k x) y
            = (β : LinearMap.BilinForm (ZMod 2) M) (ρ k x) (ρ k (ρ k⁻¹ y)) := by rw [hy]
          _ = (β : LinearMap.BilinForm (ZMod 2) M) x (ρ k⁻¹ y) := hBinv k x (ρ k⁻¹ y)
          _ = β₀ (φ x) (ρ k⁻¹ y) := by rw [hβφ x]
          _ = β₀ (ρ k (φ x)) (ρ k (ρ k⁻¹ y)) := (hβ₀ k (φ x) (ρ k⁻¹ y)).symm
          _ = β₀ (ρ k (φ x)) y := by rw [hy]
      obtain ⟨ψ, hψ⟩ := (mem_endRing_iff ρ φ).mpr hcomm
      refine ⟨ψ, ?_⟩
      refine Subtype.ext ?_
      show LinearMap.comp β₀ (ψ.restrictScalars (ZMod 2)) =
        (β : LinearMap.BilinForm (ZMod 2) M)
      ext x y
      show β₀ ((ψ : M → M) x) y = (β : LinearMap.BilinForm (ZMod 2) M) x y
      rw [congrFun hψ x, hβφ x]
    exact Nat.card_le_card_of_surjective F hsurj
  ·
    have hzero : ∀ β : invBilin ρ, β = 0 := by
      intro β
      by_contra hne
      exact h ⟨β.1, β.2, fun hb => hne (Subtype.ext hb)⟩
    have hsub : Subsingleton (invBilin ρ) := ⟨fun a b => by rw [hzero a, hzero b]⟩
    have h1 : Nat.card (invBilin ρ) ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr hsub
    have h2 : 1 ≤ Nat.card (EndRing ρ) :=
      Finite.card_pos (α := EndRing ρ)
    exact le_trans h1 h2

theorem exists_linearEquiv_comp_eq_of_invariant {K M Z Z' : Type*} [Group K]
    [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    [AddCommGroup Z] [Module (ZMod 2) Z] [Finite Z]
    [AddCommGroup Z'] [Module (ZMod 2) Z'] [Finite Z']
    (ρ : Representation (ZMod 2) K M) [Fact ρ.IsIrreducible]
    (hE : Nat.card (EndRing ρ) ≤ Nat.card Z)
    (hZZ' : Nat.card Z = Nat.card Z')
    (c : M →ₗ[ZMod 2] M →ₗ[ZMod 2] Z) (c' : M →ₗ[ZMod 2] M →ₗ[ZMod 2] Z')
    (hc : ∀ k x y, c (ρ k x) (ρ k y) = c x y) (hc' : ∀ k x y, c' (ρ k x) (ρ k y) = c' x y)
    (hspan : Submodule.span (ZMod 2) (Set.range fun p : M × M => c p.1 p.2) = ⊤)
    (hspan' : Submodule.span (ZMod 2) (Set.range fun p : M × M => c' p.1 p.2) = ⊤) :
    ∃ g : Z ≃ₗ[ZMod 2] Z', ∀ x y, g (c x y) = c' x y := by
  classical
  haveI : Module.Finite (ZMod 2) M := Module.Finite.of_finite
  haveI : Module.Finite (ZMod 2) Z := Module.Finite.of_finite
  haveI : Module.Finite (ZMod 2) Z' := Module.Finite.of_finite
  haveI hfinB : Finite (LinearMap.BilinForm (ZMod 2) M) := Module.finite_of_finite (ZMod 2)
  haveI hfinForms : Finite (invBilin ρ) := Subtype.finite
  haveI hfinDualZ : Finite (Module.Dual (ZMod 2) Z) := Module.finite_of_finite (ZMod 2)
  haveI hfinDualZ' : Finite (Module.Dual (ZMod 2) Z') := Module.finite_of_finite (ZMod 2)
  let Φ : Module.Dual (ZMod 2) Z →ₗ[ZMod 2] invBilin ρ := dualToForms ρ c hc
  let Φ' : Module.Dual (ZMod 2) Z' →ₗ[ZMod 2] invBilin ρ := dualToForms ρ c' hc'
  have hΦinj : Function.Injective Φ := dualToForms_injective ρ c hc hspan
  have hΦ'inj : Function.Injective Φ' := dualToForms_injective ρ c' hc' hspan'
  have hle : Nat.card (Module.Dual (ZMod 2) Z) ≤ Nat.card (invBilin ρ) :=
    Nat.card_le_card_of_injective Φ hΦinj
  have hge : Nat.card (invBilin ρ) ≤ Nat.card (Module.Dual (ZMod 2) Z) := by
    rw [natCard_dual_eq (V := Z)]
    exact le_trans (card_invBilin_le ρ) hE
  have hcard : Nat.card (invBilin ρ) = Nat.card (Module.Dual (ZMod 2) Z) := le_antisymm hge hle
  have hle' : Nat.card (Module.Dual (ZMod 2) Z') ≤ Nat.card (invBilin ρ) :=
    Nat.card_le_card_of_injective Φ' hΦ'inj
  have hge' : Nat.card (invBilin ρ) ≤ Nat.card (Module.Dual (ZMod 2) Z') := by
    rw [natCard_dual_eq (V := Z')]
    exact le_trans (card_invBilin_le ρ) (hZZ' ▸ hE)
  have hcard' : Nat.card (invBilin ρ) = Nat.card (Module.Dual (ZMod 2) Z') := le_antisymm hge' hle'
  have hΦbij : Function.Bijective Φ := by
    haveI : Fintype (Module.Dual (ZMod 2) Z) := Fintype.ofFinite _
    haveI : Fintype (invBilin ρ) := Fintype.ofFinite _
    refine (Fintype.bijective_iff_injective_and_card Φ).mpr ⟨hΦinj, ?_⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hcard.symm
  have hΦ'bij : Function.Bijective Φ' := by
    haveI : Fintype (Module.Dual (ZMod 2) Z') := Fintype.ofFinite _
    haveI : Fintype (invBilin ρ) := Fintype.ofFinite _
    refine (Fintype.bijective_iff_injective_and_card Φ').mpr ⟨hΦ'inj, ?_⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hcard'.symm
  let Ψ : Module.Dual (ZMod 2) Z ≃ₗ[ZMod 2] invBilin ρ := LinearEquiv.ofBijective Φ hΦbij
  let Ψ' : Module.Dual (ZMod 2) Z' ≃ₗ[ZMod 2] invBilin ρ := LinearEquiv.ofBijective Φ' hΦ'bij
  let e : Module.Dual (ZMod 2) Z' ≃ₗ[ZMod 2] Module.Dual (ZMod 2) Z := Ψ'.trans Ψ.symm
  let g : Z ≃ₗ[ZMod 2] Z' :=
    (Module.evalEquiv (ZMod 2) Z).trans (e.dualMap.trans (Module.evalEquiv (ZMod 2) Z').symm)
  have he : ∀ l' : Module.Dual (ZMod 2) Z', Φ (e l') = Φ' l' := by
    intro l'
    have h1 : Ψ (e l') = Ψ' l' := by
      simp only [e, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    change Ψ (e l') = Ψ' l'
    exact h1
  have hsep : ∀ u v : Z', (∀ l' : Module.Dual (ZMod 2) Z', l' u = l' v) → u = v := by
    intro u v huv
    refine (Module.evalEquiv (ZMod 2) Z').injective ?_
    ext l'
    simpa using huv l'
  refine ⟨g, fun x y => hsep _ _ fun l' => ?_⟩
  have h1 : l' (g (c x y)) = (e l') (c x y) := by
    have hg : g (c x y) = (Module.evalEquiv (ZMod 2) Z').symm
        (e.dualMap (Module.evalEquiv (ZMod 2) Z (c x y))) := by
      simp only [g, LinearEquiv.trans_apply]
    rw [hg, Module.apply_evalEquiv_symm_apply, LinearEquiv.dualMap_apply, Module.evalEquiv_apply]
    simp
  have h2 : (e l') (c x y) = l' (c' x y) := by
    rw [← dualToForms_apply ρ c hc (e l') x y, he l', dualToForms_apply ρ c' hc' l' x y]
  rw [h1, h2]

theorem eq_zero_of_invariant_linearMap {K M Z : Type*} [Group K] [AddCommGroup M]
    [Module (ZMod 2) M] [AddCommGroup Z] [Module (ZMod 2) Z] (ρ : Representation (ZMod 2) K M)
    [Fact ρ.IsIrreducible] (hnt : ∃ k, ρ k ≠ 1) (δ : M →ₗ[ZMod 2] Z)
    (hδ : ∀ k x, δ (ρ k x) = δ x) : δ = 0 := by
  obtain ⟨-, hirr⟩ := (isIrreducible_iff ρ).mp Fact.out
  have hinv : ∀ k, ∀ x ∈ LinearMap.ker δ, ρ k x ∈ LinearMap.ker δ := by
    intro k x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hδ, hx]
  rcases hirr (LinearMap.ker δ) hinv with hbot | htop
  · exfalso
    obtain ⟨k, hk⟩ := hnt
    apply hk
    ext x
    have hx : ρ k x - x = 0 := by
      have hmem : ρ k x - x ∈ LinearMap.ker δ := by
        rw [LinearMap.mem_ker, map_sub, hδ, sub_self]
      rw [hbot, Submodule.mem_bot] at hmem
      exact hmem
    exact sub_eq_zero.mp hx
  · ext x
    have hx : x ∈ LinearMap.ker δ := by rw [htop]; exact Submodule.mem_top
    rwa [LinearMap.mem_ker] at hx

end CFSG.Quasithin.F112R.St84
