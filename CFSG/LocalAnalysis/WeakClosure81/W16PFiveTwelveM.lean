module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveTwelveMA
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveTwelveO
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveElevenF

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11
open Subgroup
open scoped CFSG.Goldschmidt.G2

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G} {g : G} {X T : Subgroup G}

theorem Hyp167.inf_eSub_ne_bot_of_mSub_le_one
    (hI : NamedInputs15 G) (hS : Std15 G) (h152 : Thm152 G) (h1 : W16One G)
    (hX : Hyp167 M V₀ V U S H g X T) (hVO : V ≤ pCoreOf 2 H) (hm : mSub V₀ ≤ 1) :
    conjSubgroup V₀ g ⊓ eSub V₀ X T ≠ ⊥ := by
  intro hBE
  have hV₀O : V₀ ≤ pCoreOf 2 H := hX.cex.hyp.h6.le.trans hVO
  have hV₀el : IsElemAbelian 2 V₀ := hX.cex.hyp.elemAbelian₀
  haveI : Fact (IsElemAbelian 2 (eSub V₀ X T)) :=
    ⟨Hyp167.isElemAbelian_eSub h1 hS hV₀O hX⟩
  have hA : IsElemAbelian 2 (conjSubgroup V g) :=
    E3.isElemAbelian_conjSubgroup hX.cex.hyp.h6.elemAbelian g
  have hpair : IsPairAt M X (conjSubgroup V g) := hX.mem.2.2
  have hKc : kerMOf M X ≤ centralizer (eSub V₀ X T : Set G) :=
    Hyp167.kerMOf_le_centralizer_of_inf_eq_bot hI hS h152 h1 hV₀O hX hBE
  obtain ⟨ρ, hρ⟩ := exists_eRepBar M V₀ X T hKc
  obtain ⟨D, hDA, hD2, hD⟩ := Hyp167.exists_index_two_fixed h1 hS h152 hV₀O hX hBE hρ
  have hXU : X ≤ centralizer (U : Set G) := hX.mem.1.trans hX.min.1.2.1
  have hKX : CFSG.Open.IsKGroup ↥X :=
    (hS.localsK _ ⟨U, hX.cex.ne_bot, hX.cex.hyp.isPGroup.to_le hX.cex.le, rfl⟩).of_le
      (hXU.trans (Subgroup.centralizer_le_normalizer (U : Set G)))
  have hbig := Hyp167.two_lt_relIndex_of_inf_eq_bot h1 hS h152 hV₀O hX hBE
  obtain ⟨⟨n, hn⟩, hB⟩ := five_nine_borel hI.thmB hpair hA hKX hbig
  have hAB : kerQuotImg M X (conjSubgroup V g) ≤ kerQuotImg M X M :=
    kerQuotImg_mono hpair.A_le_M
  have hAe : IsElemAbelian 2 (kerQuotImg M X (conjSubgroup V g)) :=
    isElemAbelian_kerQuotImg hA
  have hfree : ∀ q : KerQuot M X, q ∉ kerQuotImg M X M →
      ∀ a ∈ kerQuotImg M X (conjSubgroup V g),
        q⁻¹ * a * q ∈ kerQuotImg M X M → a = 1 :=
    fun q hq a ha hqa => rankOne_free_off_borel hn hB hAB hAe hq ha hqa
  obtain ⟨v₀s, hv₀s1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hX.cex.hyp.ne_bot
  let v₀ : G := (v₀s : G)
  have hv₀V₀ : v₀ ∈ V₀ := v₀s.2
  have hv₀ne : v₀ ≠ 1 := fun h => hv₀s1 (Subtype.ext h)
  have hcardV₀ : Nat.card V₀ = 2 := by
    rw [card_eq_two_pow_mSub hV₀el.isPGroup]
    have hne0 : mSub V₀ ≠ 0 := by
      intro h0
      exact hX.cex.hyp.ne_bot ((rk_eq_zero_iff_of_isPGroup hV₀el.isPGroup).1 h0)
    have h1' : mSub V₀ = 1 := by omega
    rw [h1', pow_one]
  have huniq : ∃! y : ↥V₀, y ≠ 1 := (Nat.card_eq_two_iff' (1 : ↥V₀)).1 hcardV₀
  have hv1 : (⟨v₀, hv₀V₀⟩ : ↥V₀) ≠ 1 := fun hc => hv₀ne (congrArg Subtype.val hc)
  have hMfix : ∀ m ∈ M, m * v₀ * m⁻¹ = v₀ := by
    intro m hm
    have hconjmem : m * v₀ * m⁻¹ ∈ V₀ := by
      have hN : m ∈ normalizer (V₀ : Set G) := by
        rw [hX.cex.hyp.normalizer₀]; exact hm
      exact (Subgroup.mem_normalizer_iff.1 hN v₀).1 hv₀V₀
    have hw1 : (⟨m * v₀ * m⁻¹, hconjmem⟩ : ↥V₀) ≠ 1 := by
      intro hc
      apply hv₀ne
      have h1'' : m * v₀ * m⁻¹ = 1 := by simpa using congrArg Subtype.val hc
      calc v₀ = m⁻¹ * (m * v₀ * m⁻¹) * m := by group
        _ = m⁻¹ * 1 * m := by rw [h1'']
        _ = 1 := by group
    exact congrArg Subtype.val (huniq.unique hw1 hv1)
  have hv₀C : v₀ ∈ centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact (mul_inv_eq_iff_eq_mul).1 (hMfix t (hX.sylow.le.trans inf_le_right ht))
  have hv₀E : v₀ ∈ eSub V₀ X T :=
    le_conjClosure (V₀ ⊓ centralizer (T : Set G)) X
      (Subgroup.mem_inf.2 ⟨hv₀V₀, hv₀C⟩)
  let z : Additive ↥(eSub V₀ X T) := Additive.ofMul ⟨v₀, hv₀E⟩
  have hz : ∀ b ∈ kerQuotImg M X M, ρ b z = z := by
    intro b hb
    obtain ⟨m, rfl⟩ := kerQuotMk_surjective M X b
    have hmM : (m : G) ∈ M := (kerQuotMk_mem_kerQuotImg_iff m).1 hb
    rw [hρ m]
    apply Additive.ext
    apply Subtype.ext
    rw [eRep_apply V₀ X T m z]
    simpa only [z, toMul_ofMul] using hMfix m hmM
  have hfixed : ∀ q : KerQuot M X, ρ q z = z :=
    permMod_fixed_of_index_two ρ hAB hAe hDA hD2 hD hfree hz
  have hXM : X ≤ M := by
    intro x hx
    have h1x := hfixed (kerQuotMk M X ⟨x, hx⟩)
    rw [hρ ⟨x, hx⟩] at h1x
    have hxfix : x * v₀ * x⁻¹ = v₀ := by
      have h2 := congrArg (fun w : Additive ↥(eSub V₀ X T) =>
        ((Additive.toMul w : ↥(eSub V₀ X T)) : G)) h1x
      rw [eRep_apply V₀ X T ⟨x, hx⟩ z] at h2
      simpa only [z, toMul_ofMul] using h2
    have hxcomm : ∀ h ∈ V₀, x * h = h * x := by
      intro h hh
      rcases eq_or_ne h 1 with rfl | hh1
      · rw [mul_one, one_mul]
      · have hh' : (⟨h, hh⟩ : ↥V₀) ≠ 1 := fun hc => hh1 (congrArg Subtype.val hc)
        have heq : h = v₀ := congrArg Subtype.val (huniq.unique hh' hv1)
        rw [heq]
        exact (mul_inv_eq_iff_eq_mul).1 hxfix
    have hxinvcomm : ∀ w ∈ V₀, x⁻¹ * w = w * x⁻¹ := by
      intro w hw
      calc x⁻¹ * w = x⁻¹ * (w * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * w) * x⁻¹ := by rw [← hxcomm w hw]
        _ = w * x⁻¹ := by group
    rw [← hX.cex.hyp.normalizer₀, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [hxcomm h hh, mul_assoc, mul_inv_cancel, mul_one]
      exact hh
    · intro hh
      have hcomm := hxinvcomm (x * h * x⁻¹) hh
      have heq : h = x * h * x⁻¹ := by
        calc h = x⁻¹ * (x * h * x⁻¹) * x := by group
          _ = (x * h * x⁻¹) * x⁻¹ * x := by rw [hcomm]
          _ = x * h * x⁻¹ := by group
      rw [heq]
      exact hh
  have hker_eq : kerMOf M X = X := by
    refine le_antisymm (kerMOf_le_group M X) ?_
    exact le_kerMOf_of_normal le_rfl
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_rfl).2 Subgroup.le_normalizer) hXM
  exact hpair.not_le_ker (by rw [hker_eq]; exact hpair.A_le)

end CFSG.LocalAnalysis.WeakClosure81

end
