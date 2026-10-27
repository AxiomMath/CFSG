module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4L2FixFree.Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.LineMinus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.FixedSpan

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4FF

open Matrix

theorem fixed_eq_span_of_sylow {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (S : Sylow 2 ↥(Omega6 F b c)) {v : Idx → F}
    (hv0 : v ≠ 0)
    (hv : ∀ g ∈ (S : Subgroup ↥(Omega6 F b c)), ((g : GL Idx F) : Matrix Idx Idx F) *ᵥ v = v) :
    ∀ x : Idx → F,
      (∀ g ∈ (S : Subgroup ↥(Omega6 F b c)), ((g : GL Idx F) : Matrix Idx Idx F) *ᵥ x = x) →
        x ∈ Submodule.span F {v} := by
  obtain ⟨U, e, hU, hfixU⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.KTabA.exists_fixedLine_statedOmega_minus
      (K := F) (m := 3) (b := b) (c := c) (by norm_num) hirr
  obtain ⟨g₀, hg₀⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.KTabA.exists_fixed_sylow_eq_span
      (ι := Idx) (K := F) (Γ := Omega6 F b c) 2 U hU e hfixU S
  intro x hx
  let w : Idx → F := ((g₀ : GL Idx F) : Matrix Idx Idx F) *ᵥ e
  have hv_mem : v ∈ Submodule.span F {w} := (hg₀ v).mp hv
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hv_mem
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha
    exact hv0 ha.symm
  have hx_mem : x ∈ Submodule.span F {w} := (hg₀ x).mp hx
  obtain ⟨a', ha'⟩ := Submodule.mem_span_singleton.mp hx_mem
  have hw : w = a⁻¹ • v := by rw [← inv_smul_smul₀ ha0 w, ha]
  refine Submodule.mem_span_singleton.mpr ⟨a' * a⁻¹, ?_⟩
  rw [mul_smul, ← hw, ha']

private lemma prime_dvd_card_of_ne_bot_F03 {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [Finite V] (p : ℕ) [Fact p.Prime] [CharP K p] {W : Submodule K V} (hW : W ≠ ⊥) :
    p ∣ Nat.card ↥W := by
  have hgroup : IsPGroup p (Multiplicative ↥W) := by
    rw [IsPGroup.iff_orderOf]
    intro g
    obtain ⟨w, rfl⟩ : ∃ w : ↥W, Multiplicative.ofAdd w = g :=
      ⟨Multiplicative.toAdd g, rfl⟩
    rw [orderOf_ofAdd_eq_addOrderOf]
    have hw : p • w = 0 := by
      apply Subtype.ext
      show p • (w : V) = 0
      rw [← Nat.cast_smul_eq_nsmul K p (w : V)]
      simp
    obtain h1 | hp := (Nat.dvd_prime (Fact.out (p := Nat.Prime p))).mp
      (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hw)
    · exact ⟨0, by rw [h1, pow_zero]⟩
    · exact ⟨1, by rw [hp, pow_one]⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hgroup
  have hcard : Nat.card ↥W = p ^ n :=
    (Nat.card_congr (Multiplicative.ofAdd : ↥W ≃ Multiplicative ↥W)).trans hn
  haveI : Nontrivial ↥W := Submodule.nontrivial_iff_ne_bot.mpr hW
  have hn0 : n ≠ 0 := by
    intro h0
    have h1 : Nat.card ↥W = 1 := by rw [hcard, h0, pow_zero]
    have h2 : 1 < Nat.card ↥W := Finite.one_lt_card
    omega
  rw [hcard]
  exact dvd_pow_self p hn0

theorem mem_of_fixed_of_stable {K V H : Type} [Field K] [AddCommGroup V] [Module K V] [Finite V]
    [Group H] (p : ℕ) [Fact p.Prime] [CharP K p] (ρ : H →* Module.End K V) {S : Subgroup H}
    (hS : IsPGroup p ↥S) {W : Submodule K V} (hW : W ≠ ⊥) (hWS : ∀ g ∈ S, ∀ w ∈ W, ρ g w ∈ W)
    {v : V} (hfix : ∀ x : V, (∀ g ∈ S, ρ g x = x) → x ∈ Submodule.span K {v}) : v ∈ W := by
  letI : MulAction ↥S ↥W :=
    { smul := fun g w => ⟨ρ (g : H) (w : V), hWS (g : H) g.2 (w : V) w.2⟩
      one_smul := fun w => Subtype.ext (by
        show ρ (1 : H) (w : V) = (w : V)
        rw [map_one, Module.End.one_apply])
      mul_smul := fun g h w => Subtype.ext (by
        show ρ ((g : H) * (h : H)) (w : V) = ρ (g : H) (ρ (h : H) (w : V))
        rw [map_mul, Module.End.mul_apply]) }
  have hdvd : p ∣ Nat.card ↥W := prime_dvd_card_of_ne_bot_F03 p hW
  have h0fix : (0 : ↥W) ∈ MulAction.fixedPoints ↥S ↥W := by
    rw [MulAction.mem_fixedPoints]
    intro g
    exact Subtype.ext (by
      show ρ (g : H) (0 : V) = (0 : V)
      simp)
  obtain ⟨b, hbfix, hbne⟩ :=
    hS.exists_fixed_point_of_prime_dvd_card_of_fixed_point ↥W hdvd h0fix
  have hb0 : (b : V) ≠ 0 := by
    intro h0
    exact hbne (Subtype.ext h0).symm
  have hbf : ∀ g ∈ S, ρ g (b : V) = (b : V) := by
    intro g hg
    exact Subtype.ext_iff.mp ((MulAction.mem_fixedPoints.mp hbfix) ⟨g, hg⟩)
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (hfix (b : V) hbf)
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ht
    exact hb0 ht.symm
  have hmem : t⁻¹ • (b : V) ∈ W := W.smul_mem t⁻¹ b.2
  rw [← ht, inv_smul_smul₀ ht0 v] at hmem
  exact hmem

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4FF
