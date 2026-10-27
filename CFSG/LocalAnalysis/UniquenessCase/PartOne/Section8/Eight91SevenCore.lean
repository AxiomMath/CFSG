module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91Defs
import all CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP
import CFSG.HardMathSupport.Solomon.Proving.AutSixBalance
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xKAutL34Outer
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xKAutL34Cent
import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.ONAut
import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.KF148ONA7.SevenCent

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups (IsExtraspecialExpP)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.KF148ONA7
  (card_centralizer_seven_ON)

private theorem sevenCore_exists_orderOf_three {Y : Type} [Group Y] [Finite Y]
    {R : Subgroup Y} (hR : IsExtraspecialExpP 3 1 ↥R) (hZ3 : Nat.card (center Y) = 3) :
    ∃ x ∈ (R.map (QuotientGroup.mk' (center Y)) : Subgroup (Y ⧸ center Y)), orderOf x = 3 := by
  have hR' := hR
  unfold IsExtraspecialExpP at hR'
  obtain ⟨hcard, hexp, -, -⟩ := hR'
  have hnle : ¬ R ≤ center Y := by
    intro hle
    have h1 := Subgroup.card_le_of_le hle
    rw [hcard, hZ3] at h1
    norm_num at h1
  obtain ⟨r, hrR, hrZ⟩ := SetLike.not_le_iff_exists.mp hnle
  refine ⟨QuotientGroup.mk' (center Y) r, Subgroup.mem_map_of_mem _ hrR, ?_⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : (⟨r, hrR⟩ : R) ^ 3 = 1 := by
    have h := Monoid.pow_exponent_eq_one (⟨r, hrR⟩ : R)
    rwa [hexp] at h
  have hr3 : r ^ 3 = 1 := congrArg Subtype.val h3
  apply orderOf_eq_prime
  · rw [← map_pow, hr3, map_one]
  · rw [QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
    exact hrZ

private theorem sevenCore_exists_conj {Q : Type} [Group Q] {m : ℕ}
    (hm : Nat.card (Outer Q) ∣ m) (hm7 : Nat.Coprime 7 m) {φ : MulAut Q}
    (h7 : orderOf φ = 7) : ∃ g : Q, MulAut.conj g = φ := by
  have h1 : orderOf (QuotientGroup.mk' (inner Q) φ) ∣ 7 := h7 ▸ orderOf_map_dvd _ φ
  have h2 : orderOf (QuotientGroup.mk' (inner Q) φ) ∣ m := (_root_.orderOf_dvd_natCard _).trans hm
  have h3 := Nat.dvd_gcd h1 h2
  rw [Nat.Coprime.gcd_eq_one hm7, Nat.dvd_one, orderOf_eq_one_iff, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at h3
  exact MonoidHom.mem_range.mp h3

private theorem sevenCore_conj_facts {Q : Type} [Group Q] {g x : Q}
    (h7 : orderOf (MulAut.conj g) = 7) (hx : MulAut.conj g x = x) :
    g ∈ centralizer ({x} : Set Q) ∧ 7 ∣ orderOf g := by
  refine ⟨mem_centralizer_singleton_iff.mpr ?_, h7 ▸ orderOf_map_dvd MulAut.conj g⟩
  rw [MulAut.conj_apply] at hx
  exact mul_inv_eq_iff_eq_mul.mp hx

theorem r891SevenCore_holds :
    R891SevenCore := by
  intro Y _ _ hY R hR _ φ hφ h7
  rcases hY with ⟨-, -, ⟨e⟩⟩ | ⟨-, hZ3, hL⟩ | ⟨-, hZ3, hON⟩
  · have hcard : Nat.card (MulAut (Y ⧸ center Y)) = 1440 := by
      rw [Nat.card_congr (MulAut.congr e).toEquiv]
      exact CFSG.HardMathSupport.Solomon.Proving.AutSixBalance.card_mulAut_alt6
    have h := orderOf_dvd_natCard φ
    rw [h7, hcard] at h
    norm_num at h
  · obtain ⟨x, hxR, hx3⟩ := sevenCore_exists_orderOf_three hR hZ3
    obtain ⟨g, rfl⟩ := sevenCore_exists_conj (card_outer_psl_three_four hL).dvd
      (by norm_num) h7
    obtain ⟨hgx, h7g⟩ := sevenCore_conj_facts h7 (hφ x hxR)
    have h9 := Subgroup.orderOf_dvd_natCard _ hgx
    rw [card_centralizer_of_orderOf_three_psl_three_four hL hx3] at h9
    have h79 := h7g.trans h9
    norm_num at h79
  · obtain ⟨x, hxR, hx3⟩ := sevenCore_exists_orderOf_three hR hZ3
    obtain ⟨ePv⟩ := CFSG.EvenSporadicStandard.Solomon78.on_equiv_Pv hON
    have hout : Nat.card (Outer (Y ⧸ center Y)) ∣ 4 := by
      rw [Nat.card_congr (equivalence ePv).toEquiv]
      exact CFSG.EvenSporadicStandard.Solomon78.card_outer_Pv_dvd_four
    obtain ⟨g, rfl⟩ := sevenCore_exists_conj hout (by norm_num) h7
    obtain ⟨hgx, h7g⟩ := sevenCore_conj_facts h7 (hφ x hxR)
    have hh7 : orderOf (g ^ (orderOf g / 7)) = 7 :=
      orderOf_pow_orderOf_div (orderOf_pos g).ne' h7g
    have hxh : x ∈ centralizer ({g ^ (orderOf g / 7)} : Set (Y ⧸ center Y)) :=
      mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp (pow_mem hgx _)).symm
    obtain ⟨e₀⟩ := hON
    have h3 := Subgroup.orderOf_dvd_natCard _ hxh
    rw [hx3] at h3
    rcases card_centralizer_seven_ON (e₀ : (Y ⧸ center Y) ≃* CFSG.Blueprint.NativeSporadic.ON)
      hh7 with hc | hc <;> rw [hc] at h3 <;> norm_num at h3

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
