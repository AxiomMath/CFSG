module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91Defs
import CFSG.HardMathSupport.Solomon.Proving.AutSixBalance
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xKAutL34Outer
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.Sporadic.Schreier.SteinbergBIONOuterFour
import CFSG.Sporadic.ON
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarTargetTwoData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open CFSG.Blueprint Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

private theorem card_mulAut_dvd_bound_of_three_rows
    {Y : Type} [Group Y] [Finite Y]
    (hY : IsAlt Y 6 ∨ LieModel Y .PSL 3 2 2 ∨ IsSpor Y .ONan) :
    Nat.card (MulAut Y) ∣ 4 * 460815505920 := by
  have hbound : Nat.card (MulAut Y) ∣ 1440 ∨
      Nat.card (MulAut Y) ∣ 12 * 20160 ∨
      Nat.card (MulAut Y) ∣ 4 * 460815505920 := by
    rcases hY with hA | hL | hON
    · obtain ⟨e⟩ := hA
      left
      rw [Nat.card_congr (MulAut.congr e).toEquiv,
        CFSG.HardMathSupport.Solomon.Proving.AutSixBalance.card_mulAut_alt6]
    · right; left
      have hc : Nat.card Y = 20160 :=
        CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four
          (hL.statedClassicalModel (by decide))
      simpa only [card_outer_psl_three_four hL, hc] using
        CFSG.AGLEmbedding.KFactProofs.TargetTwo.card_mulAut_dvd (L := Y)
    · right; right
      obtain ⟨e⟩ := hON
      have he : Y ≃* NativeSporadic.ON := e
      have hOut : Nat.card (Outer Y) ∣ 4 :=
        CFSG.Sporadic.SteinbergBI.cti_on_outer_order_divides_four ⟨he⟩
      have hc : Nat.card Y = 460815505920 := by
        rw [Nat.card_congr he.toEquiv, CFSG.Sporadic.ON.card_ON]
      exact (CFSG.AGLEmbedding.KFactProofs.TargetTwo.card_mulAut_dvd (L := Y)).trans
        (by simpa only [hc] using Nat.mul_dvd_mul hOut (dvd_refl (Nat.card Y)))
  rcases hbound with h | h | h
  · exact h.trans (by norm_num)
  · exact h.trans (by norm_num)
  · exact h

private theorem not_dvd_bound_of_prime_ne {p : ℕ} (hp : p.Prime)
    (h2 : p ≠ 2) (h3 : p ≠ 3) (h5 : p ≠ 5) (h7 : p ≠ 7)
    (h11 : p ≠ 11) (h19 : p ≠ 19) (h31 : p ≠ 31) :
    ¬ p ∣ 4 * 460815505920 := by
  have hc : ∀ q : ℕ, q.Prime → p ≠ q → p.Coprime q := by
    intro q hq hne
    rw [hp.coprime_iff_not_dvd]
    exact fun hd => hne ((Nat.prime_dvd_prime_iff_eq hp hq).mp hd)
  have c2 : p.Coprime (2 ^ 11) := (hc 2 Nat.prime_two h2).pow_right 11
  have c3 : p.Coprime (3 ^ 4) := (hc 3 Nat.prime_three h3).pow_right 4
  have c7 : p.Coprime (7 ^ 3) := (hc 7 (by norm_num) h7).pow_right 3
  have hcop := c2.mul_right c3
  have hcop := hcop.mul_right (hc 5 (by norm_num) h5)
  have hcop := hcop.mul_right c7
  have hcop := hcop.mul_right (hc 11 (by norm_num) h11)
  have hcop := hcop.mul_right (hc 19 (by norm_num) h19)
  have hcop := hcop.mul_right (hc 31 (by norm_num) h31)
  apply hp.coprime_iff_not_dvd.mp
  convert hcop using 1

theorem mulAut_eq_one_of_list897_of_prime_ne
    {Y : Type} [Group Y] [Finite Y] (hY : R891List897 Y)
    {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) (h5 : p ≠ 5) (h7 : p ≠ 7)
    (h11 : p ≠ 11) (h19 : p ≠ 19) (h31 : p ≠ 31)
    (α : MulAut (Y ⧸ center Y)) (hα : α ^ p = 1) : α = 1 := by
  have hmodel : IsAlt (Y ⧸ center Y) 6 ∨ LieModel (Y ⧸ center Y) .PSL 3 2 2 ∨
      IsSpor (Y ⧸ center Y) .ONan := by
    rcases hY with h | h | h
    · exact Or.inl h.2.2
    · exact Or.inr (Or.inl h.2.2)
    · exact Or.inr (Or.inr h.2.2)
  have hnd : ¬ p ∣ Nat.card (MulAut (Y ⧸ center Y)) := fun hd =>
    not_dvd_bound_of_prime_ne hp h2 h3 h5 h7 h11 h19 h31
      (hd.trans (card_mulAut_dvd_bound_of_three_rows hmodel))
  have hcop := hp.coprime_iff_not_dvd.mpr hnd
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_of_pow_eq_one hα) (orderOf_dvd_natCard α))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
