module

public import CFSG.RankThree.PartOne.KC.OrthogonalKernelSectorRigidityPaired
public import CFSG.RankThree.PartOne.KC.OrthogonalSelfDualBlock

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.LocalAnalysis.ComponentInitial

section SelfDual

variable {K : Type*} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem exists_selfdual_mixing (hx : OddOrderIsometry Q p x) (hp2 : Odd p) {r : K[X]}
    (hr : r ∈ primaryFactors x.toLinearMap) (hne1 : r ≠ X - 1)
    (hself : r = reciprocalPolynomial r) (h2 : (2 : K) ≠ 0) {S₁ S₂ : Submodule K V}
    (hS₁ : ∀ v ∈ S₁, x v ∈ S₁) (hS₂ : ∀ v ∈ S₂, x v ∈ S₂) (hdisj : Disjoint S₁ S₂)
    (hperp : ∀ u ∈ S₁, ∀ w ∈ S₂, QuadraticMap.polar Q u w = 0)
    (hv : ∃ v ∈ S₁ ⊓ primaryComponent x.toLinearMap r, Q v ≠ 0)
    (hw : ∃ w ∈ S₂ ⊓ primaryComponent x.toLinearMap r, Q w ≠ 0) :
    2 ≤ primaryMultiplicity x.toLinearMap r ∧
      ∃ g ∈ specialBlock Q x r, ∃ v ∈ S₁, ∃ s ∈ S₁, ∃ t ∈ S₂, t ≠ 0 ∧ g v = s + t := by
  have : Fact (Irreducible r) := ⟨irreducible_of_mem_primaryFactors hr⟩
  obtain ⟨d, H, hdeg, -, htr, hadd₁, hadd₂, hsm₁, hsm₂, hsymm⟩ :=
    hx.exists_selfDual_hermitian hp2 hr hne1 hself
  have hfin : finrank K (AdjoinRoot r) = 2 * d := by
    rw [(AdjoinRoot.powerBasis (Fact.out : Irreducible r).ne_zero).finrank,
      AdjoinRoot.powerBasis_dim, hdeg]
  obtain ⟨ℓ, f, hU, -, hbar⟩ := exists_unitaryFieldData K (AdjoinRoot r) hfin
  have hfb : ∀ z, frobPow K (AdjoinRoot r) d z = hU.bar z := fun z => by
    rw [frobPow_apply, hbar]
  have hsm₁' : ∀ (c : AdjoinRoot r) u w, H (c • u) w = hU.bar c * H u w := fun c u w => by
    rw [hsm₁, hfb]
  have hsymm' : ∀ u w, H w u = hU.bar (H u w) := fun u w => by rw [hsymm, hfb]
  obtain ⟨v, hv1, hvQ⟩ := hv
  obtain ⟨w, hw1, hwQ⟩ := hw
  let u : primaryComponent x.toLinearMap r := ⟨v, hv1.2⟩
  let w' : primaryComponent x.toLinearMap r := ⟨w, hw1.2⟩
  have hu0 : u ≠ 0 := fun h => hvQ (by
    have : v = 0 := congrArg Subtype.val h
    rw [this, QuadraticMap.map_zero])
  have hw0 : w' ≠ 0 := fun h => hwQ (by
    have : w = 0 := congrArg Subtype.val h
    rw [this, QuadraticMap.map_zero])
  have hind := pair_linearIndependent hS₁ hS₂ hdisj hv1.1 hw1.1 hu0 hw0
  refine ⟨by simpa using hind.fintype_card_le_finrank, ?_⟩
  have hHuw : H u w' = 0 := by
    refine eq_zero_of_trace_mul_eq_zero K (AdjoinRoot r) fun c => ?_
    rw [htr u w' c]
    exact hperp _ hv1.1 _ (smul_mem_of_stable hS₂ c w' hw1.1)
  have hHwu : H w' u = 0 := by rw [hsymm' u w', hHuw, map_zero]
  have hanis : ∀ y : primaryComponent x.toLinearMap r, Q (y : V) ≠ 0 → H y y ≠ 0 := by
    intro y hy h0
    have h1 := htr y y 1
    rw [h0, zero_mul, map_zero, one_smul, QuadraticMap.polar_self, two_nsmul] at h1
    have h3 : (2 : K) * Q (y : V) = 0 := by rw [two_mul]; exact h1.symm
    exact hy ((mul_eq_zero.mp h3).resolve_left h2)
  have hHuu : H u u ≠ 0 := hanis u hvQ
  have hHww : H w' w' ≠ 0 := hanis w' hwQ
  have hHuu_fix : hU.bar (H u u) = H u u := (hsymm' u u).symm
  have hHww_fix : hU.bar (H w' w') = H w' w' := (hsymm' w' w').symm
  set f₀ : AdjoinRoot r := -(H u u) / H w' w' with hf₀
  have hf₀0 : f₀ ≠ 0 := div_ne_zero (neg_ne_zero.mpr hHuu) hHww
  have hf₀fix : hU.bar f₀ = f₀ := by
    rw [hf₀, map_div₀, map_neg, hHuu_fix, hHww_fix]
  obtain ⟨c, hc⟩ := hU.normHom_surjective ⟨f₀, hU.mem_fixedField.mpr hf₀fix⟩
  have hcn : c * hU.bar c = f₀ := congrArg Subtype.val hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hf₀0 (by rw [← hcn, zero_mul])
  have he : H (u + c • w') (u + c • w') = 0 := by
    simp only [hadd₁, hadd₂, hsm₁', hsm₂, hHuw, hHwu, mul_zero, add_zero, zero_add]
    have : hU.bar c * (c * H w' w') = f₀ * H w' w' := by rw [← hcn]; ring
    rw [this, hf₀, div_mul_cancel₀ _ hHww, add_neg_cancel]
  obtain ⟨z, hz⟩ := hU.exists_bar_ne
  set a : AdjoinRoot r := z - hU.bar z with ha
  have ha0 : a ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have haσ : hU.bar a = -a := by rw [ha, map_sub, hU.bar_bar]; ring
  have hpres : ∀ y y' : primaryComponent x.toLinearMap r,
      H (((unitaryTransvection H hadd₂ hsm₂ he a : BlockGL x r) :
          Module.End (AdjoinRoot r) (primaryComponent x.toLinearMap r)) y)
        (((unitaryTransvection H hadd₂ hsm₂ he a : BlockGL x r) :
          Module.End (AdjoinRoot r) (primaryComponent x.toLinearMap r)) y') = H y y' := by
    intro y y'
    rw [unitaryTransvection_apply, unitaryTransvection_apply]
    exact hermitian_transvection_preserves hU.bar H hadd₁ hadd₂ hsm₁' hsm₂ hsymm' he haσ y y'
  obtain ⟨g, hg⟩ := (hx.mem_range_blockGL_selfDual_iff hr hne1 hself H htr
    (unitaryTransvection H hadd₂ hsm₂ he a)).mpr hpres
  have hHeu : H (u + c • w') u = H u u := by
    rw [hadd₁, hsm₁', hHwu, mul_zero, add_zero]
  have hcoef : ((1 + a * H u u) • u + (a * H u u * c) • w' : primaryComponent x.toLinearMap r) =
      u + (a * H (u + c • w') u) • (u + c • w') := by
    rw [hHeu, smul_add, smul_smul, add_smul, one_smul]
    abel
  refine ⟨g.1, mem_specialBlock.mpr ⟨g.2, ?_⟩, v, hv1.1,
    (((1 + a * H u u) • u : primaryComponent x.toLinearMap r) : V),
    smul_mem_of_stable hS₁ _ u hv1.1,
    (((a * H u u * c) • w' : primaryComponent x.toLinearMap r) : V),
    smul_mem_of_stable hS₂ _ w' hw1.1, ?_, ?_⟩
  · rw [blockDet_apply, hg]
    exact det_unitaryTransvection H hadd₂ hsm₂ he a
  · intro h0
    exact smul_ne_zero (mul_ne_zero (mul_ne_zero ha0 hHuu) hc0) hw0 (Subtype.ext h0)
  · have h1 := coe_blockGL (Q := Q) (x := x) r g u
    rw [hg, unitaryTransvection_apply, ← hcoef, Submodule.coe_add] at h1
    exact h1.symm

end SelfDual

end CFSG.RankThree.PartOne.KCOrthogonal
