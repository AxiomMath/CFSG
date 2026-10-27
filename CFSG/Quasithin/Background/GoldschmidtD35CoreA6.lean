module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSmallFactsA6
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSmallFacts

public section

namespace CFSG.Quasithin.D35Core

open Equiv Equiv.Perm CFSG.ComponentClassification.RankTwoAlt CFSG.Quasithin.SteinbergCB

@[expose] def FixTwo (a b : Fin 6) (x : alternatingGroup (Fin 6)) : Prop :=
  (x : Perm (Fin 6)) a = a ∧ (x : Perm (Fin 6)) b = b ∧ x * x = 1

instance (a b : Fin 6) : DecidablePred (FixTwo a b) := fun x => by
  unfold FixTwo
  infer_instance

theorem card_fixTwo : ∀ a b : Fin 6, a ≠ b →
    (Finset.univ.filter fun x : alternatingGroup (Fin 6) => FixTwo a b x).card = 4 := by
  decide +kernel

theorem card_fixedPoints_involution : ∀ x : alternatingGroup (Fin 6), x * x = 1 → x ≠ 1 →
    (Finset.univ.filter fun p : Fin 6 => (x : Perm (Fin 6)) p = p).card = 2 := by
  decide +kernel

theorem exists_fixTwo_ne_one : ∀ c d : Fin 6, c ≠ d → ∃ v : alternatingGroup (Fin 6),
    FixTwo c d v ∧ v ≠ 1 ∧ ∀ p : Fin 6, (v : Perm (Fin 6)) p = p → p = c ∨ p = d := by
  decide +kernel

theorem exists_three_cycle_fixing : ∀ a b : Fin 6, a ≠ b → ∃ x : alternatingGroup (Fin 6),
    (x : Perm (Fin 6)).support.card = 3 ∧ (x : Perm (Fin 6)) a = a ∧ (x : Perm (Fin 6)) b = b := by
  decide +kernel

set_option synthInstance.maxSize 1024 in
theorem card_support_of_order_three : ∀ c d : Fin 6, c ≠ d → ∀ x : alternatingGroup (Fin 6),
    x * x * x = 1 → x ≠ 1 → ((x⁻¹ : alternatingGroup (Fin 6)) : Perm (Fin 6)) c = c ∨
      ((x⁻¹ : alternatingGroup (Fin 6)) : Perm (Fin 6)) c = d →
    ((x⁻¹ : alternatingGroup (Fin 6)) : Perm (Fin 6)) d = c ∨
      ((x⁻¹ : alternatingGroup (Fin 6)) : Perm (Fin 6)) d = d →
    (x : Perm (Fin 6)).support.card = 3 := by
  decide +kernel

theorem fixTwo_conj {a b : Fin 6} {x v : alternatingGroup (Fin 6)}
    (hxa : (x : Perm (Fin 6)) a = a) (hxb : (x : Perm (Fin 6)) b = b) (hv : FixTwo a b v) :
    FixTwo a b (x * v * x⁻¹) := by
  obtain ⟨hva, hvb, hv2⟩ := hv
  have hia : ((x⁻¹ : alternatingGroup (Fin 6)) : Perm (Fin 6)) a = a := by
    rw [Subgroup.coe_inv, Perm.inv_eq_iff_eq, hxa]
  have hib : ((x⁻¹ : alternatingGroup (Fin 6)) : Perm (Fin 6)) b = b := by
    rw [Subgroup.coe_inv, Perm.inv_eq_iff_eq, hxb]
  refine ⟨?_, ?_, ?_⟩
  · simp only [Subgroup.coe_mul, Perm.mul_apply, hia, hva, hxa]
  · simp only [Subgroup.coe_mul, Perm.mul_apply, hib, hvb, hxb]
  · calc x * v * x⁻¹ * (x * v * x⁻¹) = x * (v * v) * x⁻¹ := by group
      _ = 1 := by rw [hv2]; group

theorem isThreeCycle_of_normalizes {c d : Fin 6} (hcd : c ≠ d) {x : alternatingGroup (Fin 6)}
    (hx3 : x * x * x = 1) (hx1 : x ≠ 1)
    (hN : ∀ v, FixTwo c d v → FixTwo c d (x * v * x⁻¹)) : (x : Perm (Fin 6)).IsThreeCycle := by
  obtain ⟨v, hv, -, hvfix⟩ := exists_fixTwo_ne_one c d hcd
  have h := hN v hv
  have hmoves : ∀ p, ((x * v * x⁻¹ : alternatingGroup (Fin 6)) : Perm (Fin 6)) p = p →
      p = c ∨ p = d → ((x⁻¹ : alternatingGroup (Fin 6)) : Perm (Fin 6)) p = c ∨
        ((x⁻¹ : alternatingGroup (Fin 6)) : Perm (Fin 6)) p = d := by
    intro p hp _
    apply hvfix
    have := congrArg (fun q => (x : Perm (Fin 6))⁻¹ q) hp
    simpa using this
  have hc := hmoves c h.1 (Or.inl rfl)
  have hd := hmoves d h.2.1 (Or.inr rfl)
  exact card_support_eq_three_iff.mp
    (card_support_of_order_three c d hcd x hx3 hx1 hc (by simpa using hd))

theorem exists_perm_of_fixTwo (α : MulAut (alternatingGroup (Fin 6))) {a b c d : Fin 6}
    (hab : a ≠ b) (hcd : c ≠ d) (h : ∀ x, FixTwo a b x ↔ FixTwo c d (α x)) :
    ∃ σ : Perm (Fin 6), ∀ g : alternatingGroup (Fin 6),
      ((α g : alternatingGroup (Fin 6)) : Perm (Fin 6)) = σ * g * σ⁻¹ := by
  obtain ⟨x₀, hs, hxa, hxb⟩ := exists_three_cycle_fixing a b hab
  have h3 : (x₀ : Perm (Fin 6)).IsThreeCycle := card_support_eq_three_iff.mp hs
  have hx3 : x₀ * x₀ * x₀ = 1 := by
    apply Subtype.ext
    have := pow_orderOf_eq_one (x₀ : Perm (Fin 6))
    rw [h3.orderOf] at this
    simpa [pow_succ] using this
  have hx1 : x₀ ≠ 1 := by
    rintro rfl
    simp at hs
  have hαx3 : α x₀ * α x₀ * α x₀ = 1 := by rw [← map_mul, ← map_mul, hx3, map_one]
  have hαx1 : α x₀ ≠ 1 := fun he => hx1 (α.injective (he.trans (map_one α).symm))
  have hN : ∀ v, FixTwo c d v → FixTwo c d (α x₀ * v * (α x₀)⁻¹) := by
    intro v hv
    have hw : FixTwo c d (α (α.symm v)) := by rwa [MulEquiv.apply_symm_apply]
    have := fixTwo_conj hxa hxb ((h _).2 hw)
    have h2 := (h _).1 this
    rwa [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at h2
  have hα3 := isThreeCycle_of_normalizes hcd hαx3 hαx1 hN
  obtain ⟨g, hg⟩ : ∃ g : Perm (Fin 6), g * (a6c012 : Perm (Fin 6)) * g⁻¹ = x₀ :=
    isConj_iff.mp (isConj_iff_cycleType_eq.mpr
      (by rw [h3.cycleType, isThreeCycle_a6c012.cycleType]))
  set θ : MulAut (alternatingGroup (Fin 6)) := (conjPerm 6 g).trans α with hθ
  have hθ012 : θ a6c012 = α x₀ := by
    rw [hθ, MulEquiv.trans_apply]
    congr 1
    exact Subtype.ext (by rw [conjPerm_apply, hg])
  obtain ⟨σ, hσ⟩ := exists_perm_of_isThreeCycle θ (by rw [hθ012]; exact hα3)
  refine ⟨σ * g⁻¹, fun z => ?_⟩
  have hz : z = conjPerm 6 g (conjPerm 6 g⁻¹ z) := by
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  have h1 : α z = θ (conjPerm 6 g⁻¹ z) := by
    rw [hθ, MulEquiv.trans_apply, ← hz]
  rw [h1, hσ, conjPerm_apply]
  group

end CFSG.Quasithin.D35Core
