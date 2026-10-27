module

import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusOuterCurtis
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusOuterClass
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusOuterChecks
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusMinor
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusCoeff
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bDiagram
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyDisplacement
import CFSG.LocalAnalysis.SectionRank.QTK.EvenMinus8
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusOuter

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.QuasithinUnique.Setup.X7b (repLinEquiv repLinEquiv_apply)
open scoped Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
  (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

include hirrQ in
theorem omMinus_two_outer_four_le (hK : Nat.card K = 2) {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V]
    {ρ : Representation (ZMod 2) (spinGroup (quadMinus 4 K b c)) V} (hρ : IsSimpleRep ρ)
    (hρ1 : ∃ g, ρ g ≠ 1)
    (hE : Nat.card (Module.End (MonoidAlgebra (ZMod 2) (spinGroup (quadMinus 4 K b c)))
      ρ.asModule) = 2)
    (hnat : ¬ ∃ f : V →+ (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K), f ≠ 0 ∧ ∀ g v, f (ρ g v) = mat 4 g *ᵥ f v)
    (s : V ≃ₗ[ZMod 2] V) (α : MulAut (spinGroup (quadMinus 4 K b c)))
    (hα : ∀ g v, s (ρ g (s.symm v)) = ρ (α g) v) (hα2 : α * α = 1)
    (houter : ∀ g₀ : spinGroup (quadMinus 4 K b c), α ≠ MulAut.conj g₀) :
    4 ≤ Module.finrank (ZMod 2) (LinearMap.range (s.toLinearMap - 1)) := by
  classical
  obtain ⟨rfl, rfl⟩ := CFSG.SectionRank.QTK.eq_one_of_irreducible_of_card_two hK hirrQ
  have : Module.Finite (ZMod 2) V := Module.finite_iff_finite.mpr inferInstance
  let : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Fintype.card (ZMod 2) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card]
    exact hK
  let φ : K →+* ZMod 2 := (FiniteField.ringEquivOfCardEq hcard).toRingHom
  let D := o8mDatum hirrQ
  have hρmul : ∀ g h v, ρ g (ρ h v) = ρ (g * h) v := fun g h v => by rw [map_mul]; rfl
  have hsymm : ∀ g v, (repLinEquiv ρ g).symm v = ρ g⁻¹ v := fun _ _ => rfl
  obtain ⟨y, χ, μ, ht, hχ⟩ := omMinus_two_exists_isCurtisType_of_card_end hirrQ hρ hE
  have hμ0 := omMinus_two_mu_ne_zero hirrQ hρ hρ1 ht hχ
  have hμ1 := omMinus_two_mu_ne_natural hirrQ hK hρ hnat ht hχ
  let J : Finset (Fin 3) := Finset.univ.filter fun i => μ i = 1
  have hμJ : ∀ i, μ i = if i ∈ J then 1 else 0 := by
    intro i
    by_cases h : μ i = 1
    · simp [J, h]
    · have h0 : μ i = 0 := by
        generalize μ i = a at h ⊢
        fin_cases a
        · rfl
        · exact absurd rfl h
      simp [J, h0]
  obtain ⟨f, hf, hfy⟩ := D.exists_form hρ ht.1 ht.2.1
  have hfg : ∀ g, f (ρ g y) = φ (o8mMinorProd J (mat 4 g)) := fun g =>
    o8mDatum_form_eq_minorProd hirrQ hK φ ht hχ hμJ hf hfy g
  obtain ⟨x, u, hu, hα'⟩ := omMinus_two_outer_reduction hirrQ hK α hα2 houter
  let j : V ≃ₗ[ZMod 2] V :=
    (repLinEquiv ρ x).trans (s.trans (repLinEquiv ρ (x * u)⁻¹))
  have hj : ∀ g v, j (ρ g (j.symm v)) = ρ (o8mOuterAut hirrQ g) v := by
    intro g v
    simp only [j, LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply, repLinEquiv_apply, hsymm,
      inv_inv]
    have e1 : ρ x (ρ g (ρ x⁻¹ (s.symm (ρ (x * u) v)))) =
        ρ (x * g * x⁻¹) (s.symm (ρ (x * u) v)) := by
      rw [hρmul g, hρmul x, mul_assoc]
    rw [e1, hα, hρmul, hρmul]
    have e2 : (x * u)⁻¹ * α (x * g * x⁻¹) * (x * u) = o8mOuterAut hirrQ g := by
      calc (x * u)⁻¹ * α (x * g * x⁻¹) * (x * u)
          = u⁻¹ * (x⁻¹ * α (x * g * x⁻¹) * x) * u := by group
        _ = o8mOuterAut hirrQ g := by rw [hα' g]; group
    rw [e2]
  have hjy : j y = y := omMinus_two_intertwiner_fix hirrQ hρ ht
    (o8mOuterAut hirrQ).toMonoidHom (o8mOuterAut_apply_apply (hirrQ := hirrQ))
    (fun v hv => (mem_o8mDatum_U_iff_o8mOuterAut_mem (hirrQ := hirrQ) v).mp hv) j hj
  let T : V →ₗ[ZMod 2] V := (repLinEquiv ρ x).symm.toLinearMap ∘ₗ
    (s.toLinearMap - 1) ∘ₗ (repLinEquiv ρ x).toLinearMap
  have hj' : ∀ v, ρ x⁻¹ (s (ρ x v)) = ρ u (j v) := by
    intro v
    simp only [j, LinearEquiv.trans_apply, repLinEquiv_apply]
    rw [hρmul, mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]
  have hT : ∀ h, T (ρ h y) = ρ (u * o8mOuterAut hirrQ h) y - ρ h y := by
    intro h
    have hjh : j (ρ h y) = ρ (o8mOuterAut hirrQ h) y := by
      have := hj h (j y)
      rwa [LinearEquiv.symm_apply_apply, hjy] at this
    simp only [T, LinearMap.comp_apply, LinearMap.sub_apply, Module.End.one_apply,
      LinearEquiv.coe_coe, repLinEquiv_apply, hsymm, map_sub]
    rw [hj', hjh, hρmul, ρ.inv_self_apply]
  have hcoef : ∀ a h, f (ρ a (T (ρ h y))) =
      φ (o8mMinorProd J (mat 4 (a * (u * o8mOuterAut hirrQ h)))) +
        φ (o8mMinorProd J (mat 4 (a * h))) := by
    intro a h
    calc f (ρ a (T (ρ h y)))
        = f (ρ (a * (u * o8mOuterAut hirrQ h)) y) - f (ρ (a * h) y) := by
          rw [hT, map_sub, map_sub, hρmul, hρmul]
          rfl
      _ = _ := by rw [hfg, hfg, CharTwo.sub_eq_add]
  obtain ⟨a, h, hdet⟩ := omMinus_two_outer_checks hirrQ hμ0 hμ1 hu φ
  have h4 : 4 ≤ Module.finrank (ZMod 2) (LinearMap.range T) := by
    refine o8m_card_le_finrank_range_of_det_ne_zero T (fun j => ρ (h j) y)
      (fun i => f ∘ₗ ρ (a i)) ?_
    convert hdet using 2
    ext i j
    simp only [Matrix.of_apply, LinearMap.comp_apply]
    exact hcoef (a i) (h j)
  exact h4.trans_eq
    (CFSG.QuasithinUnique.Setup.Family.finrank_range_conj (repLinEquiv ρ x).symm _)

end CFSG.LocalAnalysis.WeakClosure81
