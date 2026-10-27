module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabel
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLFaithful
public import CFSG.LocalAnalysis.StandardType.GGReflModule
public import CFSG.LocalAnalysis.StandardType.GGWeylReflection

public section

namespace CFSG.StandardType

open CFSG.LieType.RootSystem

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def ggReflConj {Λ : Type*} {Y : Type*} [Group Y] (s : Λ → Y) : Set Y :=
  {r | ∃ u ∈ Subgroup.closure (Set.range s), ∃ i, r = u * s i * u⁻¹}

@[expose] def GGReflClosed {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {Λ : Type}
    (s : Λ → V ≃ₗ[ZMod p] V) : Prop :=
  ∀ r ∈ Subgroup.closure (Set.range s), r ^ 2 = 1 → r ≠ 1 →
    (∃ (v : V) (f : Module.Dual (ZMod p) V), ∀ w, r w = w - f w • v) → r ∈ ggReflConj s

theorem ggReflClosed_of_indep {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Finite V] {Λ : Type} [Fintype Λ] [DecidableEq Λ] (hp : p ≠ 2)
    {C : Matrix Λ Λ ℤ} (hFT : TauCeti.IsFiniteType C) {M : CoxeterMatrix Λ}
    (hC : GGIntCartan M C) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p)) (hind : LinearIndependent (ZMod p) h)
    (s : Λ → V ≃ₗ[ZMod p] V) (hs : ∀ i v, s i v = v - α i v • h i) :
    GGReflClosed s := by
  classical
  have hM := coxeterMatrix_eq_of_ggIntCartan hFT hC
  subst hM
  have hα : ∀ i, α i (h i) = 2 := fun i => by rw [hpair, hC.1 i]; norm_num
  set cs := (coxeterMatrix hFT).toCoxeterSystem
  let ρ : (coxeterMatrix hFT).Group →* (V ≃ₗ[ZMod p] V) :=
    cs.lift ⟨fun i => Module.reflection (hα i), isLiftable_reflection_of_intCartan hC h α hα hpair⟩
  have hρ : ∀ i v, ρ (cs.simple i) v = v - α i v • h i := by
    intro i v
    simp only [ρ, CoxeterSystem.lift_apply_simple, Module.reflection_apply]
  have hρs : ∀ i, ρ (cs.simple i) = s i := fun i => LinearEquiv.ext fun v => by rw [hρ, hs]
  have hinj : Function.Injective ρ := ggCartanFaithful_of_isFiniteType hα hpair hp hFT hC hind
  have hmemW : ∀ g, ρ g ∈ Subgroup.closure (Set.range s) := by
    intro g
    induction g using cs.simple_induction_left with
    | one => simp
    | mul_simple_left w i ih =>
      rw [map_mul, hρs]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨i, rfl⟩) ih
  have hle : Subgroup.closure (Set.range s) ≤ ρ.range := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨cs.simple i, hρs i⟩
  intro r hr hr2 hr1 ⟨v, f, hvf⟩
  obtain ⟨t, rfl⟩ := hle hr
  have ht2 : t * t = 1 := hinj (by rw [map_mul, map_one, ← pow_two, hr2])
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hr1 (LinearEquiv.ext fun w => by rw [hvf]; simp)
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hr1 (LinearEquiv.ext fun w => by rw [hvf]; simp)
  obtain ⟨w₀, hw₀⟩ : ∃ w, f w ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hf0 (LinearMap.ext hcon)
  have hfv : f v = 2 := by
    have h1 : ρ t (ρ t w₀) = w₀ := by
      rw [← LinearEquiv.mul_apply, ← map_mul, ht2, map_one]; rfl
    rw [hvf (ρ t w₀), hvf w₀, map_sub, map_smul, smul_eq_mul] at h1
    have h3 : (f w₀ * (f v - 2)) • v = 0 := by linear_combination (norm := module) h1
    have h4 := (smul_eq_zero.mp h3).resolve_right hv0
    exact sub_eq_zero.mp ((mul_eq_zero.mp h4).resolve_left hw₀)
  have hker : LinearMap.ker ((ρ t).toLinearMap + 1) = Submodule.span (ZMod p) {v} := by
    apply le_antisymm
    · intro w hw
      have hw' : ρ t w + w = 0 := by simpa using LinearMap.mem_ker.mp hw
      rw [hvf] at hw'
      have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero (p := p) hp
      have : w = ((2 : ZMod p)⁻¹ * f w) • v := by
        have h5 : (2 : ZMod p) • w = f w • v := by linear_combination (norm := module) hw'
        rw [mul_smul, ← h5, smul_smul, inv_mul_cancel₀ h2, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
    · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker]
      change ρ t v + v = 0
      rw [hvf, hfv]
      module
  have hvH : v ∈ Submodule.span (ZMod p) (Set.range h) := by
    have hm := ggRefl_sub_mem hFT h α ρ hρ t v
    rw [hvf, hfv] at hm
    have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero (p := p) hp
    have h7 : (2 : ZMod p) • v ∈ Submodule.span (ZMod p) (Set.range h) := by
      have := Submodule.neg_mem _ hm
      convert this using 1
      module
    have h8 : v = (2 : ZMod p)⁻¹ • ((2 : ZMod p) • v) := by
      rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
    rw [h8]
    exact Submodule.smul_mem _ _ h7
  have hfr : Module.finrank (ZMod p)
      ↥(LinearMap.ker ((ρ t).toLinearMap + 1) ⊓ Submodule.span (ZMod p) (Set.range h)) = 1 := by
    rw [hker, inf_eq_left.mpr ((Submodule.span_singleton_le_iff_mem _ _).mpr hvH)]
    exact finrank_span_singleton hv0
  have hrat : Module.finrank ℚ
      (LinearMap.ker (Matrix.toLin' ((ggWeylMat hFT t).map (Int.castRingHom ℚ) + 1))) = 1 := by
    rw [← ggRefl_minus_finrank hFT hp h α hpair ρ hρ t ht2]
    exact hfr
  obtain ⟨g, i, htg⟩ := ggWeyl_isReflection_of_finrank hFT t ht2 hrat
  exact ⟨ρ g, hmemW g, i, by rw [htg, map_mul, map_mul, map_inv, hρs]⟩

end CFSG.StandardType
