module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveTwelveFB
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveElevenA
import CFSG.LocalAnalysis.WeakClosure81.ElevenSevenAlt
import CFSG.CGT.PushingUpLit.BHS.Offender
import CFSG.GH74.Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11
open Subgroup
open scoped CFSG.Goldschmidt.G2

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G} {g : G} {X T : Subgroup G}

theorem Hyp167.exists_index_two_fixed [Fact (IsElemAbelian 2 (eSub V₀ X T))] (h1 : W16One G)
    (hS : Std15 G) (h152 : Thm152 G) (hV₀ : V₀ ≤ pCoreOf 2 H)
    (hX : Hyp167 M V₀ V U S H g X T) (hBE : conjSubgroup V₀ g ⊓ eSub V₀ X T = ⊥)
    {ρ : KerQuot M X →* LGL 2 (Additive ↥(eSub V₀ X T))}
    (hρ : ∀ x : ↥X, ρ (kerQuotMk M X x) = eRep V₀ X T x) :
    ∃ D : Subgroup (KerQuot M X), D ≤ kerQuotImg M X (conjSubgroup V g) ∧
      D.relIndex (kerQuotImg M X (conjSubgroup V g)) = 2 ∧
      ∀ w : Additive ↥(eSub V₀ X T), (∀ d ∈ D, ρ d w = w) →
        ∀ a ∈ kerQuotImg M X (conjSubgroup V g), ρ a w = w := by
  have hIn := Hyp167.inCalAMod_kerQuotImg h1 hS hV₀ hX hBE hρ
  have h1n : 1 ≤ E3.mQuot V (U ⊔ V₀) := Cex16.one_le_n h152 hX.cex
  have h1m : 1 ≤ mSub V₀ := by
    change 1 ≤ rk V₀
    by_contra h0
    have hz : rk V₀ = 0 := by omega
    exact hX.cex.hyp.ne_bot
      ((CFSG.Quasithin.rk_eq_zero_iff_of_isPGroup hX.cex.hyp.elemAbelian₀.isPGroup).1 hz)
  have h2bar : 2 ≤ mBar M V₀ V hX.cex.hyp.h6.elemAbelian := by
    have := hX.cex.mbar
    omega
  have hm2 : 2 ≤ Min.min (E3.mQuot V (U ⊔ V₀) + mSub V₀)
      (mBar M V₀ V hX.cex.hyp.h6.elemAbelian) := le_min (by omega) h2bar
  obtain ⟨D, -, hDle, hDrel⟩ :=
    exists_relIndex_two_of_lt (N := ⊥) (CFSG.Open.IsElemAbelian.isPGroup hIn.2.1) bot_le
      (Ne.symm hIn.1)
  refine ⟨D, hDle, hDrel, ?_⟩
  have hlt : D.relIndex (kerQuotImg M X (conjSubgroup V g)) <
      2 ^ Min.min (E3.mQuot V (U ⊔ V₀) + mSub V₀)
        (mBar M V₀ V hX.cex.hyp.h6.elemAbelian) := by
    rw [hDrel]
    calc (2 : ℕ) < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ Min.min (E3.mQuot V (U ⊔ V₀) + mSub V₀)
          (mBar M V₀ V hX.cex.hyp.h6.elemAbelian) :=
        Nat.pow_le_pow_right (by norm_num) hm2
  have hfix := hIn.2.2 D hDle hlt
  intro w hw
  have hwD : w ∈ fixSub (D.map ρ) := by
    rw [mem_fixSub]
    intro a ha
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 ha
    exact hw d hd
  have hwA : w ∈ fixSub ((kerQuotImg M X (conjSubgroup V g)).map ρ) := by
    rw [hfix]
    exact hwD
  rw [mem_fixSub] at hwA
  intro a ha
  exact hwA (ρ a) (Subgroup.mem_map_of_mem ρ ha)

end CFSG.LocalAnalysis.WeakClosure81

end
