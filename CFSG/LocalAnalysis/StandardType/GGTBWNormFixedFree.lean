module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormCenterless
public import CFSG.LocalAnalysis.StandardType.GGResCentBoundLin
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofLinPerm
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofRefl
public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14SymAut
public import CFSG.Mathlib.GroupTheory.PermCenter

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggWeylDatum_commutant_eq_smul {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ}
    (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hfix : ∀ v : V, (∀ i, α i v = 0) → v = 0)
    (T : V →ₗ[ZMod p] V)
    (hT : ∀ i v, T (v - α i v • h i) = T v - α i (T v) • h i) :
    ∃ c : ZMod p, ∀ v, T v = c • v := by
  obtain ⟨c, hc⟩ := ggWeylDatum_commutant_scalar hp2 hM hC h α hpair T hT
  refine ⟨c, fun v => sub_eq_zero.mp (hfix (T v - c • v) ?_)⟩
  intro i
  rw [map_sub, map_smul, hc i v, smul_eq_mul]
  exact sub_self _

theorem normInducesInner_of_symmetric_reflections {p d : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hd : 5 ≤ d) {G : Type} [Group G] {A : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ι : Additive ↥A ≃+ V) (ρ : Equiv.Perm (Fin d) →* MulAut ↥A)
    (hρ : Function.Injective ρ)
    (hsw : ∀ i j, i ≠ j → GGIsReflection p (ρ (Equiv.swap i j))) :
    NormInducesInner ρ.range := by
  intro s hs
  let W := ρ.range
  let ρW : Equiv.Perm (Fin d) →* W := ρ.codRestrict W fun σ => ⟨σ, rfl⟩
  have hρW : Function.Bijective ρW := by
    constructor
    · intro σ τ hστ
      exact hρ (congrArg Subtype.val hστ)
    · rintro ⟨w, σ, rfl⟩
      exact ⟨σ, rfl⟩
  let e : Equiv.Perm (Fin d) ≃* W := MulEquiv.ofBijective ρW hρW
  let β : MulAut (Equiv.Perm (Fin d)) :=
    MulAut.congr e.symm (W.normalizerMonoidHom ⟨s, hs⟩)
  have hβ (σ : Equiv.Perm (Fin d)) : ρ (β σ) = s * ρ σ * s⁻¹ := by
    change (e (e.symm ((W.normalizerMonoidHom ⟨s, hs⟩) (e σ))) : MulAut ↥A) = _
    rw [e.apply_symm_apply, Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  have hβsw : ∀ i j : Fin d, i ≠ j → (β (Equiv.swap i j)).IsSwap := by
    intro i j hij
    have hr : IsLinRefl (ggLin (p := p) ι (s * ρ (Equiv.swap i j) * s⁻¹)) :=
      exists_of_ggIsReflection (p := p) ι (GGIsReflection.conj (hsw i j hij) s)
    rw [← hβ] at hr
    exact isSwap_of_isLinRefl hp2 ((ggLin (p := p) ι).comp ρ)
      ((ggLin_injective (p := p) ι).comp hρ)
      (fun a b hab => exists_of_ggIsReflection (p := p) ι (hsw a b hab)) hr
  obtain ⟨π, hπ⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.perm_aut_preserving_swaps_inner hd β
      (fun i j hij => hβsw i j hij)
  refine ⟨ρ π, ⟨π, rfl⟩, ?_⟩
  rintro w ⟨σ, rfl⟩
  rw [← hβ, hπ, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem ggWNormConcl_of_symmetric_fixedFree {p d : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hd : 5 ≤ d) {G : Type} [Group G] {A : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V] [Nontrivial V]
    {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (ι : Additive ↥A ≃+ V) (φ : Λ → MulAut ↥A)
    (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    {M : CoxeterMatrix Λ} (hM : GGIsWeylMatrix M)
    {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hlin : ∀ i v, ggLin (p := p) ι (φ i) v = v - α i v • h i)
    (ρ : Equiv.Perm (Fin d) →* MulAut ↥A) (hρ : Function.Injective ρ)
    (hsw : ∀ i j, i ≠ j → GGIsReflection p (ρ (Equiv.swap i j)))
    (hfixed : ∀ a : ↥A, (∀ σ, ρ σ a = a) → a = 1)
    (hgen : ρ.range = Subgroup.closure (Set.range φ))
    {s : MulAut ↥A} (hs : s ∈ Subgroup.normalizer (ρ.range : Set (MulAut ↥A))) :
    GGWNormConcl ι φ h α s := by
  let ρW : Equiv.Perm (Fin d) →* ρ.range :=
    ρ.codRestrict ρ.range fun σ => ⟨σ, rfl⟩
  have hρW : Function.Bijective ρW := by
    constructor
    · intro σ τ hστ
      exact hρ (congrArg Subtype.val hστ)
    · rintro ⟨w, σ, rfl⟩
      exact ⟨σ, rfl⟩
  have hZ : Subgroup.center ↥ρ.range = ⊥ := by
    let e : Equiv.Perm (Fin d) ≃* ρ.range := MulEquiv.ofBijective ρW hρW
    have hz := center_perm_eq_bot_of_three_le_card (α := Fin d)
      (by simpa using (show 3 ≤ d by omega))
    rw [← Subgroup.map_center_eq e, hz, Subgroup.map_bot]
  have hrootfix : ∀ v : V, (∀ i, α i v = 0) → v = 0 := by
    intro v hv
    have hWfix : ∀ w ∈ ρ.range, ggLin (p := p) ι w v = v := by
      intro w hw
      rw [hgen] at hw
      induction hw using Subgroup.closure_induction with
      | mem w hw =>
        obtain ⟨i, rfl⟩ := hw
        rw [hlin, hv, zero_smul, sub_zero]
      | one => simp
      | mul a b _ _ ha hb => rw [map_mul, LinearEquiv.mul_apply, hb, ha]
      | inv a _ ha =>
        apply (ggLin (p := p) ι a).injective
        rw [map_inv]
        change ggLin (p := p) ι a ((ggLin (p := p) ι a).symm v) = ggLin (p := p) ι a v
        rw [LinearEquiv.apply_symm_apply, ha]
    obtain ⟨a, rfl⟩ := (Additive.ofMul.trans ι.toEquiv).surjective v
    have ha : a = 1 := hfixed a fun σ => by
      apply (Additive.ofMul.trans ι.toEquiv).injective
      change ι (Additive.ofMul (ρ σ a)) = ι (Additive.ofMul a)
      rw [← ggLin_apply_ofMul (p := p)]
      exact hWfix _ ⟨σ, rfl⟩
    rw [ha]
    change ι (0 : Additive ↥A) = 0
    exact ι.map_zero
  have hscalar : ∀ f : MulAut ↥A, (∀ w ∈ ρ.range, f * w = w * f) →
      ∃ c : ZMod p, ∀ v, ggLin (p := p) ι f v = c • v := by
    intro f hf
    apply ggWeylDatum_commutant_eq_smul hp2 hM hC h α hpair hrootfix
      (ggLin (p := p) ι f).toLinearMap
    intro i v
    change ggLin (p := p) ι f (v - α i v • h i) =
      ggLin (p := p) ι f v - α i (ggLin (p := p) ι f v) • h i
    have hi : φ i ∈ ρ.range := by rw [hgen]; exact Subgroup.subset_closure ⟨i, rfl⟩
    have he := congrArg (fun g : MulAut ↥A => ggLin (p := p) ι g v) (hf _ hi)
    simpa only [map_mul, LinearEquiv.mul_apply, hlin] using he
  exact ggWNormConcl_of_centerless ι φ h α hgen hZ
    (normInducesInner_of_symmetric_reflections hp2 hd ι ρ hρ hsw) hscalar hs

end CFSG.StandardType
