module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Reflection

public section

namespace CFSG.StandardType

variable {p : ℕ} [Fact p.Prime] {E : Type*} [Group E] {V : Type*} [AddCommGroup V]
  [Module (ZMod p) V]

theorem sub_mem_radical_of_mem_closure (hp2 : p ≠ 2) (ι : Additive E ≃+ V) {Λ : Type*}
    (φ : Λ → MulAut E) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hdiag : ∀ i, α i (h i) = 2)
    (hlin : ∀ i v, ggLin (p := p) ι (φ i) v = v - α i v • h i)
    (ω : LinearMap.BilinForm (ZMod p) V) (halt : ∀ v, ω v v = 0)
    (hφω : ∀ i u v, ω (ggLin (p := p) ι (φ i) u) (ggLin (p := p) ι (φ i) v) = ω u v)
    {f : MulAut E} (hf : f ∈ Subgroup.closure (Set.range φ)) (v u : V) :
    ω (ggLin (p := p) ι f v - v) u = 0 := by
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h0
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h')
  have hrad : ∀ i u, ω (h i) u = 0 := by
    intro i u
    have hzero : ω (h i) = 0 :=
      @LinearMap.BilinMap.apply_left_eq_zero_of_preReflection
        (ZMod p) V (ZMod p) _ _ _
        (inferInstance : Field (ZMod p)).toAddCommGroup Semiring.toModule ω halt htwo
        (h i) (α i) (hdiag i)
        (fun v w => by simpa only [hlin] using hφω i v w)
    exact congrArg (fun f : Module.Dual (ZMod p) V => f u) hzero
  induction hf using Subgroup.closure_induction generalizing v u with
  | mem f hf =>
    obtain ⟨i, rfl⟩ := hf
    rw [hlin, sub_sub_cancel_left, LinearMap.BilinForm.neg_left,
      LinearMap.BilinForm.smul_left, hrad, mul_zero]
    simp
  | one => simp
  | mul f g _ _ hf hg =>
    rw [map_mul, LinearEquiv.mul_apply,
      show (ggLin (p := p) ι f) ((ggLin (p := p) ι g) v) - v =
        ((ggLin (p := p) ι f) ((ggLin (p := p) ι g) v) - (ggLin (p := p) ι g) v) +
          ((ggLin (p := p) ι g) v - v) by abel,
      LinearMap.BilinForm.add_left, hf, hg, add_zero]
  | inv f _ hf =>
    have e := hf ((ggLin (p := p) ι f⁻¹) v) u
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, LinearEquiv.coe_one,
      id] at e
    rw [show (ggLin (p := p) ι f⁻¹) v - v = -(v - (ggLin (p := p) ι f⁻¹) v) by abel,
      LinearMap.BilinForm.neg_left, e]
    simp

theorem false_of_pairing_of_moves (hp2 : p ≠ 2) (ι : Additive E ≃+ V) {Λ : Type*}
    (φ : Λ → MulAut E) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hdiag : ∀ i, α i (h i) = 2)
    (hlin : ∀ i v, ggLin (p := p) ι (φ i) v = v - α i v • h i)
    (ω : LinearMap.BilinForm (ZMod p) V) (halt : ∀ v, ω v v = 0)
    {W : Subgroup (MulAut E)}
    (hW : ∀ f ∈ W, ∀ u v, ω (ggLin (p := p) ι f u) (ggLin (p := p) ι f v) = ω u v)
    (hgen : W = Subgroup.closure (Set.range φ)) {t : MulAut E} (ht : t ∈ W) {v u : V}
    (hmove : ω (ggLin (p := p) ι t v - v) u ≠ 0) : False := by
  have hφ : ∀ i, φ i ∈ W := fun i => hgen ▸ Subgroup.subset_closure ⟨i, rfl⟩
  exact hmove (sub_mem_radical_of_mem_closure hp2 ι φ h α hdiag hlin ω halt
    (fun i => hW (φ i) (hφ i)) (hgen ▸ ht) v u)

end CFSG.StandardType
