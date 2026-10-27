module

public import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Blueprint.Chevalley CFSG.HardMathSupport.C14Exc

private theorem kgLangS1EBridgeFixAux_stab {p : ℕ} {τ : Tag} {L : Type} [Field L]
    {F₀ : ModGL τ L →* ModGL τ L}
    (hstab : ∀ g ∈ adjointGroup τ L, F₀ g ∈ adjointGroup τ L) :
    ∀ g ∈ ratPts τ L (endPow F₀ p), F₀ g ∈ ratPts τ L (endPow F₀ p) := by
  intro g hg
  rw [ratPts, Subgroup.mem_inf] at hg ⊢
  exact ⟨hstab g hg.1, eqLocus_endPow_stab F₀ p g hg.2⟩

private theorem kgLangS1EBridgeFixAux_central {p : ℕ} {R : Type} [Group R] {τ : Tag}
    {L : Type} [Field L] {F₀ : ModGL τ L →* ModGL τ L} {ρ : R →* ModGL τ L}
    {Θ : ratPts τ L (endPow F₀ p) →* MulAut R}
    (hρ : Function.Injective ρ) (hΘ : Function.Injective Θ)
    (hconjΘ : ∀ g r, ρ (Θ g r) = (g : ModGL τ L) * ρ r * (g : ModGL τ L)⁻¹)
    {c : ratPts τ L (endPow F₀ p)}
    (hc : ∀ r, (c : ModGL τ L) * ρ r = ρ r * (c : ModGL τ L)) :
    c = 1 := by
  have hTheta : Θ c = 1 := by
    apply MulEquiv.ext
    intro r
    apply hρ
    have hcomm : ρ (Θ c r) = ρ r := by
      rw [hconjΘ c r, hc r]
      group
    simpa using hcomm
  exact hΘ (by rw [hTheta, map_one])

theorem kgLangS1E_bridge_fixed_inndiag {p : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {I F : Set (MulAut R)}
    {τ : Tag} {L : Type} [Field L] {F₀ : ModGL τ L →* ModGL τ L}
    (hstab : ∀ g ∈ adjointGroup τ L, F₀ g ∈ adjointGroup τ L)
    (ρ : R →* ModGL τ L) (Θ : ratPts τ L (endPow F₀ p) →* MulAut R)
    (hρ : Function.Injective ρ) (hρG : ∀ r, ρ r ∈ ratPts τ L (endPow F₀ p))
    (hΘ : Function.Injective Θ) (hI : ∀ φ, φ ∈ I ↔ ∃ g, Θ g = φ)
    (hconjΘ : ∀ g r, ρ (Θ g r) = (g : ModGL τ L) * ρ r * (g : ModGL τ L)⁻¹)
    (hFj : ∀ f ∈ F, orderOf f = p → ∃ j : ℕ, ¬ p ∣ j ∧ ∀ r, ρ (f r) = (endPow F₀ j) (ρ r))
    {u f : MulAut R} (hu : u ∈ I) (hf : f ∈ F) (hfo : orderOf f = p) :
    ∃ g : ratPts τ L (endPow F₀ p), Θ g = u ∧
      (∀ r, (u * f * u⁻¹) r = r ↔
        (g : ModGL τ L)⁻¹ * ρ r * (g : ModGL τ L) ∈ ratPts τ L F₀) ∧
      ∀ x : ratPts τ L (endPow F₀ p), Θ x * (u * f * u⁻¹) = (u * f * u⁻¹) * Θ x →
        (g : ModGL τ L)⁻¹ * (x : ModGL τ L) * (g : ModGL τ L) ∈ ratPts τ L F₀ := by
  obtain ⟨j, hj, hfj⟩ := hFj f hf hfo
  obtain ⟨g, hg⟩ := (hI u).1 hu
  have hρφ_all : ∀ s : R, ρ ((u * f * u⁻¹) s) =
      (g : ModGL τ L) * (endPow F₀ j) ((g : ModGL τ L)⁻¹ * ρ s * (g : ModGL τ L)) *
        (g : ModGL τ L)⁻¹ := by
    intro s
    have hstep : (u * f * u⁻¹) s = Θ g (f ((Θ g)⁻¹ s)) := by rw [← hg]; rfl
    rw [hstep, hconjΘ g (f ((Θ g)⁻¹ s))]
    congr 1
    rw [hfj]
    congr 1
    rw [show (Θ g)⁻¹ = Θ g⁻¹ from (map_inv Θ g).symm, hconjΘ g⁻¹ s]
    simp only [Subgroup.coe_inv, inv_inv]
  have hconj1 : ∀ r, (u * f * u⁻¹) r = r ↔
      (g : ModGL τ L)⁻¹ * ρ r * (g : ModGL τ L) ∈ ratPts τ L F₀ := by
    intro r
    set z : ModGL τ L := (g : ModGL τ L)⁻¹ * ρ r * (g : ModGL τ L) with hzdef
    have hzG : z ∈ ratPts τ L (endPow F₀ p) := by
      rw [hzdef]
      exact mul_mem (mul_mem (inv_mem g.2) (hρG r)) g.2
    have hzeq : ρ r = (g : ModGL τ L) * z * (g : ModGL τ L)⁻¹ := by
      rw [hzdef]; group
    have hiff : (u * f * u⁻¹) r = r ↔
        (g : ModGL τ L) * (endPow F₀ j) z * (g : ModGL τ L)⁻¹ = ρ r := by
      constructor
      · intro h
        have hthis := hρφ_all r
        rw [h] at hthis
        exact hthis.symm
      · intro h; exact hρ ((hρφ_all r).trans h)
    have hcancel : ((g : ModGL τ L) * (endPow F₀ j) z * (g : ModGL τ L)⁻¹ = ρ r) ↔
        (endPow F₀ j) z = z := by
      rw [hzeq, mul_right_cancel_iff, mul_left_cancel_iff]
    rw [hiff, hcancel]
    have hfixp : endPow F₀ p z = z := ratPts_fix hzG
    rw [endPow_fixed_iff hp hfixp hj]
    rw [ratPts, Subgroup.mem_inf]
    constructor
    · intro h; exact ⟨hzG.1, by simpa using h⟩
    · intro h; exact h.2
  have hstabG : ∀ y ∈ ratPts τ L (endPow F₀ p),
      F₀ y ∈ ratPts τ L (endPow F₀ p) := kgLangS1EBridgeFixAux_stab hstab
  have honto : ∀ r' : R, ∃ r : R,
      (endPow F₀ j) ((g : ModGL τ L)⁻¹ * ρ r * (g : ModGL τ L)) = ρ r' := by
    intro r'
    refine ⟨Θ g (f⁻¹ r'), ?_⟩
    have e : (g : ModGL τ L)⁻¹ * ρ (Θ g (f⁻¹ r')) * (g : ModGL τ L) = ρ (f⁻¹ r') := by
      rw [hconjΘ g (f⁻¹ r')]
      group
    rw [e, ← hfj, MulAut.apply_inv_self]
  have hconj3 : ∀ x : ratPts τ L (endPow F₀ p),
      Θ x * (u * f * u⁻¹) = (u * f * u⁻¹) * Θ x →
      (g : ModGL τ L)⁻¹ * (x : ModGL τ L) * (g : ModGL τ L) ∈ ratPts τ L F₀ := by
    intro x hcomm
    set z : ModGL τ L := (g : ModGL τ L)⁻¹ * (x : ModGL τ L) * (g : ModGL τ L) with hzdef
    have hzG : z ∈ ratPts τ L (endPow F₀ p) := by
      rw [hzdef]
      exact mul_mem (mul_mem (inv_mem g.2) x.2) g.2
    have hcommF : ∀ r : R,
        (z⁻¹ * (endPow F₀ j) z) * (endPow F₀ j) ((g : ModGL τ L)⁻¹ * ρ r * (g : ModGL τ L)) =
          (endPow F₀ j) ((g : ModGL τ L)⁻¹ * ρ r * (g : ModGL τ L)) *
            (z⁻¹ * (endPow F₀ j) z) := by
      intro r
      set wr : ModGL τ L := (g : ModGL τ L)⁻¹ * ρ r * (g : ModGL τ L) with hwrdef
      have happ : Θ x ((u * f * u⁻¹) r) = (u * f * u⁻¹) (Θ x r) := by
        have h := congrArg (fun m : MulAut R => m r) hcomm
        simpa only [MulAut.mul_apply] using h
      have hL : ρ (Θ x ((u * f * u⁻¹) r)) =
          (x : ModGL τ L) * ((g : ModGL τ L) * (endPow F₀ j) wr * (g : ModGL τ L)⁻¹) *
            (x : ModGL τ L)⁻¹ := by
        rw [hconjΘ x ((u * f * u⁻¹) r), hρφ_all r, hwrdef]
      have hR : ρ ((u * f * u⁻¹) (Θ x r)) =
          (g : ModGL τ L) * (endPow F₀ j) z * (endPow F₀ j) wr * ((endPow F₀ j) z)⁻¹ *
            (g : ModGL τ L)⁻¹ := by
        rw [hρφ_all (Θ x r), hconjΘ x r]
        have harg : (g : ModGL τ L)⁻¹ * ((x : ModGL τ L) * ρ r * (x : ModGL τ L)⁻¹) *
              (g : ModGL τ L) = z * wr * z⁻¹ := by rw [hzdef, hwrdef]; group
        rw [harg, map_mul, map_mul, map_inv]
        group
      have hzwr : z * (endPow F₀ j) wr * z⁻¹ =
          (endPow F₀ j) z * (endPow F₀ j) wr * ((endPow F₀ j) z)⁻¹ := by
        have h1 := hL.symm.trans ((congrArg ρ happ).trans hR)
        have h2 := congrArg (fun t => (g : ModGL τ L)⁻¹ * t * (g : ModGL τ L)) h1
        have hLHS : (g : ModGL τ L)⁻¹ *
              ((x : ModGL τ L) * ((g : ModGL τ L) * (endPow F₀ j) wr * (g : ModGL τ L)⁻¹) *
                (x : ModGL τ L)⁻¹) * (g : ModGL τ L) =
              z * (endPow F₀ j) wr * z⁻¹ := by
          rw [hzdef]; group
        have hRHS : (g : ModGL τ L)⁻¹ *
              ((g : ModGL τ L) * (endPow F₀ j) z * (endPow F₀ j) wr * ((endPow F₀ j) z)⁻¹ *
                (g : ModGL τ L)⁻¹) * (g : ModGL τ L) =
              (endPow F₀ j) z * (endPow F₀ j) wr * ((endPow F₀ j) z)⁻¹ := by group
        rw [hLHS, hRHS] at h2
        exact h2
      have hcommr : (z⁻¹ * (endPow F₀ j) z) * (endPow F₀ j) wr =
          (endPow F₀ j) wr * (z⁻¹ * (endPow F₀ j) z) := by
        have hconj : (z⁻¹ * (endPow F₀ j) z) * (endPow F₀ j) wr *
              (z⁻¹ * (endPow F₀ j) z)⁻¹ = (endPow F₀ j) wr := by
          calc (z⁻¹ * (endPow F₀ j) z) * (endPow F₀ j) wr *
                (z⁻¹ * (endPow F₀ j) z)⁻¹
              = z⁻¹ * ((endPow F₀ j) z * (endPow F₀ j) wr * ((endPow F₀ j) z)⁻¹) * z := by
                group
            _ = z⁻¹ * (z * (endPow F₀ j) wr * z⁻¹) * z := by rw [← hzwr]
            _ = (endPow F₀ j) wr := by group
        calc (z⁻¹ * (endPow F₀ j) z) * (endPow F₀ j) wr
            = ((z⁻¹ * (endPow F₀ j) z) * (endPow F₀ j) wr *
                (z⁻¹ * (endPow F₀ j) z)⁻¹) * (z⁻¹ * (endPow F₀ j) z) := by group
          _ = (endPow F₀ j) wr * (z⁻¹ * (endPow F₀ j) z) := by rw [hconj]
      exact hcommr
    have hcG : z⁻¹ * (endPow F₀ j) z ∈ ratPts τ L (endPow F₀ p) :=
      mul_mem (inv_mem hzG) (endPow_mem hstabG j hzG)
    set c : ratPts τ L (endPow F₀ p) :=
      ⟨z⁻¹ * (endPow F₀ j) z, hcG⟩ with hcdef
    have hccomm : ∀ r : R, (c : ModGL τ L) * ρ r = ρ r * (c : ModGL τ L) := by
      intro r
      obtain ⟨r₀, hr₀⟩ := honto r
      have hthis := hcommF r₀
      rw [hr₀] at hthis
      rw [hcdef]
      exact hthis
    have hc_one : c = 1 := kgLangS1EBridgeFixAux_central hρ hΘ hconjΘ hccomm
    have hCz : (endPow F₀ j) z = z := by
      have h1 : z⁻¹ * (endPow F₀ j) z = 1 := by
        have h2 := congrArg (fun t : ratPts τ L (endPow F₀ p) => (t : ModGL τ L)) hc_one
        rw [hcdef] at h2
        simpa using h2
      calc (endPow F₀ j) z = z * (z⁻¹ * (endPow F₀ j) z) := by group
        _ = z * 1 := by rw [h1]
        _ = z := mul_one z
    have hF0z : F₀ z = z := (endPow_fixed_iff hp (ratPts_fix hzG) hj).1 hCz
    rw [ratPts, Subgroup.mem_inf]
    exact ⟨hzG.1, by simpa using hF0z⟩
  exact ⟨g, hg, hconj1, hconj3⟩

theorem kgLangS1E_bridge_fixed {p : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {I F : Set (MulAut R)}
    (hinn : I ⊆ (MulAut.conj : R →* MulAut R).range)
    {τ : Tag} {L : Type} [Field L] {F₀ : ModGL τ L →* ModGL τ L}
    (hstab : ∀ g ∈ adjointGroup τ L, F₀ g ∈ adjointGroup τ L)
    (ρ : R →* ModGL τ L) (Θ : ratPts τ L (endPow F₀ p) →* MulAut R)
    (hρ : Function.Injective ρ) (hρG : ∀ r, ρ r ∈ ratPts τ L (endPow F₀ p))
    (hΘ : Function.Injective Θ) (hI : ∀ φ, φ ∈ I ↔ ∃ g, Θ g = φ)
    (hconjΘ : ∀ g r, ρ (Θ g r) = (g : ModGL τ L) * ρ r * (g : ModGL τ L)⁻¹)
    (hFj : ∀ f ∈ F, orderOf f = p → ∃ j : ℕ, ¬ p ∣ j ∧ ∀ r, ρ (f r) = (endPow F₀ j) (ρ r))
    {u f : MulAut R} (hu : u ∈ I) (hf : f ∈ F) (hfo : orderOf f = p) :
    ∃ g : ratPts τ L (endPow F₀ p), Θ g = u ∧
      (∀ r, (u * f * u⁻¹) r = r ↔
        (g : ModGL τ L)⁻¹ * ρ r * (g : ModGL τ L) ∈ ratPts τ L F₀) ∧
      (∀ y ∈ ratPts τ L F₀, ∃ r, (u * f * u⁻¹) r = r ∧
        (g : ModGL τ L)⁻¹ * ρ r * (g : ModGL τ L) = y) ∧
      ∀ x : ratPts τ L (endPow F₀ p), Θ x * (u * f * u⁻¹) = (u * f * u⁻¹) * Θ x →
        (g : ModGL τ L)⁻¹ * (x : ModGL τ L) * (g : ModGL τ L) ∈ ratPts τ L F₀ := by
  obtain ⟨g, hg, hconj1, hconj3⟩ :=
    kgLangS1E_bridge_fixed_inndiag hp hstab ρ Θ hρ hρG hΘ hI hconjΘ hFj hu hf hfo
  have hsurj : ∀ x : ratPts τ L (endPow F₀ p), ∃ r : R, ρ r = (x : ModGL τ L) := by
    intro x
    have hxI : Θ x ∈ I := (hI (Θ x)).2 ⟨x, rfl⟩
    obtain ⟨r, hr⟩ := hinn hxI
    refine ⟨r, ?_⟩
    have htheta := absBridge_theta_rho hρ hρG hconjΘ r
    have heq : (⟨ρ r, hρG r⟩ : ratPts τ L (endPow F₀ p)) = x := by
      apply hΘ
      rw [htheta]
      exact hr
    exact congrArg Subtype.val heq
  have hconj2 : ∀ y ∈ ratPts τ L F₀, ∃ r, (u * f * u⁻¹) r = r ∧
      (g : ModGL τ L)⁻¹ * ρ r * (g : ModGL τ L) = y := by
    intro y hy
    set y' : ModGL τ L := (y : ModGL τ L) with hy'def
    set x0 : ModGL τ L := (g : ModGL τ L) * y' * (g : ModGL τ L)⁻¹ with hx0def
    have hx0G : x0 ∈ ratPts τ L (endPow F₀ p) := by
      rw [ratPts, Subgroup.mem_inf]
      refine ⟨?_, ?_⟩
      · exact mul_mem (mul_mem g.2.1 hy.1) (inv_mem g.2.1)
      · show endPow F₀ p x0 = x0
        have hyp : endPow F₀ p (y : ModGL τ L) = (y : ModGL τ L) := by
          rw [endPow_apply]; exact Function.iterate_fixed hy.2 p
        rw [hx0def, hy'def, map_mul, map_mul, map_inv, ratPts_fix g.2, hyp]
    obtain ⟨r, hr⟩ := hsurj ⟨x0, hx0G⟩
    have hr' : ρ r = x0 := hr
    have hz : (g : ModGL τ L)⁻¹ * ρ r * (g : ModGL τ L) = (y : ModGL τ L) := by
      rw [hr', hx0def, hy'def]; group
    exact ⟨r, (hconj1 r).2 (by rw [hz]; exact hy), hz⟩
  exact ⟨g, hg, hconj1, hconj2, hconj3⟩

end CFSG.StandardType
