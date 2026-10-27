module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycThreeCentAAA
public import CFSG.LocalAnalysis.WeakClosure81.FourteenNine

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16h_e3_CycThreeCentAA_barSub_ne_bot
    (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (h : Setting16 D V₀ V L)
    (hct : ¬ 3 ∣ Nat.card ↥(F11.CTilde D.M V₀ V))
    {E : Subgroup G} (hEM : E ≤ D.M) (hEcard : Nat.card ↥E = 3 ^ 3) :
    barSub V₀ V hV E ≠ ⊥ := by
  intro hbot
  have hp := h.hyp151.hyp125.pairFacts
  have hle : E ≤ F11.CTilde D.M V₀ V :=
    (CFSG.LocalAnalysis.WeakClosure81.barSub_eq_bot_iff hV hp.le_normalizer
      hp.le_normalizer₀ hEM).1 hbot
  have hdvd : Nat.card ↥E ∣ Nat.card ↥(F11.CTilde D.M V₀ V) :=
    Subgroup.card_dvd_of_le hle
  have h3 : 3 ∣ Nat.card ↥E := by rw [hEcard]; norm_num
  exact hct (h3.trans hdvd)

theorem s16h_e3_CycThreeCentAA_exists_bar_fix
    (D : Data G) (S : s16h_Std D) (hr3 : CFSG.Open.evenRank G = 3) (hσ : D.sig = D.sig1)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (h : Setting16 D V₀ V L)
    (hc : Conc4_136 D V₀ V hV L)
    {p : ℕ} (hp : p.Prime) (hLp : IsCyclicOrd ↥(lBar V₀ V hV L) p)
    (hχ : ¬ ∀ n ∈ Mbar D.M V₀ V hV,
      n ∈ normalizer ((lBar V₀ V hV L : Subgroup _) : Set _) →
        ∀ l ∈ lBar V₀ V hV L, n * l = l * n)
    (hs3 : s15 D.M V₀ V hV L = 3)
    (hpσ : p ∉ D.sig) (h3 : D.sig = {3})
    (hn76 : ¬ (p = 7 ∧ rk ↥(wTil V₀ V hV L) = 6))
    (hct : ¬ 3 ∣ Nat.card ↥(F11.CTilde D.M V₀ V))
    {E : Subgroup G} (hEM : E ≤ D.M) (hEab : IsElemAbelian 3 E)
    (hEcard : Nat.card ↥E = 3 ^ 3) :
    ∀ X ∈ wConj D.M V₀ V hV L, ∀ Y ∈ wConj D.M V₀ V hV L, X ≠ Y →
      ∀ u ∈ X ⊔ Y, ∃ φ ∈ barSub V₀ V hV E, φ ≠ 1 ∧
        ∀ (huV : u ∈ V), φ (mkTil V₀ V hV (IntMod.mk hV ⟨u, huV⟩)) =
          mkTil V₀ V hV (IntMod.mk hV ⟨u, huV⟩) := by
  have hne := s16h_e3_CycThreeCentAA_barSub_ne_bot D hV h hct hEM hEcard
  obtain ⟨φ₀, hφ₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  intro X hX Y hY hXY u hu
  by_cases hu0 : u ∈ V₀
  · refine ⟨(φ₀ : MulAut (Vtil V₀ V hV)), φ₀.2, fun h1 => hφ₀1 (Subtype.ext h1),
      fun huV => ?_⟩
    have h1 : mkTil V₀ V hV (IntMod.mk hV ⟨u, huV⟩) = 1 := by
      rw [← map_one (mkTil V₀ V hV)]
      exact (QuotientGroup.eq_one_iff (N := modNull V₀ V hV) _).2
        ((mem_modNull V₀ V hV _).2 hu0)
    rw [h1, map_one]
  · exact s16h_e3_CycThreeCentAAA_exists_bar_fix_not_mem_v0 D S hr3 hσ hV h hc hp hLp hχ
      hs3 hpσ h3 hn76 hct hEM hEab hEcard X hX Y hY hXY u hu hu0

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
