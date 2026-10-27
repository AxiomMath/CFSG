module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormCenterless
public import CFSG.LinearAlgebra.Reflection.ScalarIsometry
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcWeylTorusAut
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Algebra.Module.Pi

public noncomputable section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y]
  {A : Subgroup Y} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  {Λ : Type}

theorem ggWNormConcl_of_scalar_isometry
    (ι : Additive ↥A ≃+ V) (φ : Λ → MulAut ↥A)
    (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (B : LinearMap.BilinForm (ZMod p) V) (hB : B.Nondegenerate)
    (hdim : 3 ≤ Module.finrank (ZMod p) V)
    {W : Subgroup (MulAut ↥A)} (hW : W = Subgroup.closure (Set.range φ))
    {s w : MulAut ↥A} (hw : w ∈ W) (c : (ZMod p)ˣ)
    (hs : ∀ v, ggLin (p := p) ι s v = (c : ZMod p) • ggLin (p := p) ι w v)
    (hiso : ∀ v u, B (ggLin (p := p) ι w v) (ggLin (p := p) ι w u) = B v u) :
    GGWNormConcl ι φ h α s := by
  let : Finite V := Finite.of_equiv ↥A (Additive.ofMul.trans ι.toEquiv)
  have hwm : ggLin (p := p) ι w ∈ ggHL ι φ h α :=
    ggLin_mem_ggHL_of_closure ι φ h α hW hw
  refine ⟨⟨c, ggLin (p := p) ι w, hwm, hs⟩, ?_⟩
  intro href
  have hcard := ((ggIsReflection_iff (p := p) ι s).mp href).2
  let T : Module.End (ZMod p) V := (ggLin (p := p) ι s).toLinearMap
  have hker : LinearMap.ker (LinearMap.id - T) = LinearMap.ker (T - 1) := by
    change LinearMap.ker (1 - T) = LinearMap.ker (T - 1)
    rw [show 1 - T = -(T - 1) by abel, LinearMap.ker_neg]
  have hcardker : Nat.card (LinearMap.ker (T - 1)) * p = Nat.card V := by
    rw [← hker, ← card_fixed_eq_card_ker]
    exact hcard
  have hfix : Module.finrank (ZMod p) (LinearMap.ker (T - 1)) + 1 =
      Module.finrank (ZMod p) V := by
    rw [← FiniteField.pow_finrank_eq_natCard p (LinearMap.ker (T - 1)),
      ← FiniteField.pow_finrank_eq_natCard p V, ← pow_succ] at hcardker
    exact Nat.pow_right_injective (Fact.out : p.Prime).two_le hcardker
  have hpm : (c : ZMod p) = 1 ∨ (c : ZMod p) = -1 :=
    CFSG.LinearAlgebra.Reflection.eq_one_or_eq_neg_one_of_smul_of_preserves
      B hB (w := (ggLin (p := p) ι w).toLinearMap) (s := T) hiso hs hfix hdim
  rcases hpm with hc | hc
  · have heq : ggLin (p := p) ι s = ggLin (p := p) ι w := by
      ext v
      rw [hs, hc, one_smul]
    rw [heq]
    exact hwm
  · have heq : ggLin (p := p) ι s =
        LinearEquiv.neg (ZMod p) * ggLin (p := p) ι w := by
      ext v
      rw [hs, hc, LinearEquiv.mul_apply]
      exact _root_.neg_one_smul (R := ZMod p) (ggLin (p := p) ι w v)
    rw [heq]
    exact Subgroup.mul_mem _
      (Subgroup.subset_closure (Or.inl (Or.inr (Set.mem_singleton _)))) hwm

theorem ggWNormConcl_of_scalar_weyl_coordinates
    {τ : CFSG.Blueprint.Chevalley.Tag} [NeZero p]
    (ι : Additive ↥A ≃+ V) (φ : Λ → MulAut ↥A)
    (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (κ : Multiplicative (Fin τ.rank → ZMod p) ≃* ↥A)
    (hrank : 3 ≤ τ.rank)
    (hdet : IsUnit ((τ.symmetrizedCartan.det : ℤ) : ZMod p))
    {W : Subgroup (MulAut ↥A)} (hW : W = Subgroup.closure (Set.range φ))
    (hρ : (ExcWeylOuter.torusMulAut τ p).range.map (MulAut.congr κ).toMonoidHom = W)
    {s : MulAut ↥A} (c : (ZMod p)ˣ) (u : WeylGroup τ)
    (hs : ∀ v : Fin τ.rank → ZMod p,
      s (κ (Multiplicative.ofAdd v)) =
        κ (Multiplicative.ofAdd ((c : ZMod p) • TableBExc.torusAct τ p u v))) :
    GGWNormConcl ι φ h α s := by
  let j : (Fin τ.rank → ZMod p) ≃+ V := κ.toAdditive.trans ι
  let e : (Fin τ.rank → ZMod p) ≃ₗ[ZMod p] V :=
    LinearEquiv.ofBijective (j.toAddMonoidHom.toZModLinearMap p) j.bijective
  have he : ∀ v, e v = ι (Additive.ofMul (κ (Multiplicative.ofAdd v))) := fun _ => rfl
  let w : MulAut ↥A := MulAut.congr κ (ExcWeylOuter.torusMulAut τ p u)
  have hw : w ∈ W := hρ ▸ Subgroup.mem_map_of_mem _ ⟨u, rfl⟩
  have hwact : ∀ v, ggLin (p := p) ι w (e v) = e (TableBExc.torusAct τ p u v) := by
    intro v
    rw [he, ggLin_apply_ofMul]
    change ι (Additive.ofMul
      (κ (ExcWeylOuter.torusMulAut τ p u (κ.symm (κ (Multiplicative.ofAdd v)))))) = _
    rw [κ.symm_apply_apply, ExcWeylOuter.torusMulAut_apply]
    rfl
  have hsact : ∀ v, ggLin (p := p) ι s v = (c : ZMod p) • ggLin (p := p) ι w v := by
    intro v
    obtain ⟨a, rfl⟩ := e.surjective v
    rw [he, ggLin_apply_ofMul, hs]
    rw [← he, e.map_smul, ← hwact]
    rfl
  let B0 : LinearMap.BilinForm (ZMod p) (Fin τ.rank → ZMod p) :=
    Matrix.toBilin' (NoTvAut.cartanMod τ p)
  have hB0 : B0.Nondegenerate := by
    apply LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero'
    rw [NoTvAut.det_cartanMod]
    exact hdet.ne_zero
  let B : LinearMap.BilinForm (ZMod p) V := LinearMap.BilinForm.congr e B0
  have hB : B.Nondegenerate := hB0.congr e
  have hiso : ∀ v v', B (ggLin (p := p) ι w v) (ggLin (p := p) ι w v') = B v v' := by
    intro v v'
    obtain ⟨a, rfl⟩ := e.surjective v
    obtain ⟨a', rfl⟩ := e.surjective v'
    rw [hwact, hwact]
    simp only [B, LinearMap.BilinForm.congr_apply, e.symm_apply_apply]
    simp only [B0, Matrix.toBilin'_apply']
    exact NoTvAut.torusAct_form u a a'
  have hdim : 3 ≤ Module.finrank (ZMod p) V := by
    rw [← e.finrank_eq, Module.finrank_fin_fun]
    exact hrank
  exact ggWNormConcl_of_scalar_isometry ι φ h α B hB hdim hW hw c hsact hiso

end CFSG.StandardType
