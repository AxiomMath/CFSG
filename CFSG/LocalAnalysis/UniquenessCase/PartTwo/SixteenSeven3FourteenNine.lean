module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3FourteenFstar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3FourteenZSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16c1614_not_five_dvd_case168_9 (D : Data G) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (h : Case168_9 D V₀ V hV L) :
    ¬ 5 ∣ Nat.card ↥(Mbar D.M V₀ V hV) := by
  classical
  obtain ⟨⟨e⟩, hL3, -⟩ := h
  haveI : Finite (MulAut (Vtil V₀ V hV)) := MulEquiv.finite_left
  haveI : IsSimpleGroup ↥(lBar V₀ V hV L) := isSimpleGroup_of_isL3 hL3
  have hdvd : Nat.card ↥(Mbar D.M V₀ V hV) ∣
      Nat.card ↥(fstarBar D.M V₀ V hV) * Nat.card (MulAut ↥(fstarBar D.M V₀ V hV)) :=
    s16c1614_card_dvd_fstar_subgroup _
  have hcard : Nat.card ↥(lBar V₀ V hV L) = 168 := card_eq_of_isL3 hL3
  have hnab : ∃ a b : ↥(lBar V₀ V hV L), a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hc : Subgroup.center ↥(lBar V₀ V hV L) = ⊤ := by
      refine eq_top_iff.2 fun x _ => Subgroup.mem_center_iff.2 fun g => hcon g x
    rw [center_eq_bot_of_isL3 hL3] at hc
    have h1 : Nat.card ↥(lBar V₀ V hV L) = 1 := by
      rw [← Subgroup.card_top (G := ↥(lBar V₀ V hV L)), ← hc, Subgroup.card_bot]
    omega
  have h5S : ¬ 5 ∣ Nat.card (MulAut ↥(lBar V₀ V hV L)) := fun h5 =>
    (by norm_num : ¬ 5 ∣ 336) (h5.trans (card_mulAut_dvd_of_isL3 hL3))
  have hAut : ¬ 5 ∣ Nat.card (MulAut ↥(fstarBar D.M V₀ V hV)) := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv]
    exact s16c1614_not_five_dvd_card_mulAut_z7_prod hnab h5S
  have hF : Nat.card ↥(fstarBar D.M V₀ V hV) = 7 * (168 * 168) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_prod, hcard, Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, ZMod.card]
  intro h5
  rcases (Nat.Prime.dvd_mul Nat.prime_five).1 (h5.trans hdvd) with h | h
  · rw [hF] at h
    omega
  · exact hAut h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
