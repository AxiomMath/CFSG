module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycThreeCentA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16h_e3_CycThreeCent_three_dvd_of_ctilde
    (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (h : Setting16 D V₀ V L)
    (hct : 3 ∣ Nat.card ↥(F11.CTilde D.M V₀ V)) :
    ∀ X ∈ wConj D.M V₀ V hV L, ∀ Y ∈ wConj D.M V₀ V hV L, X ≠ Y →
      ∀ u ∈ X ⊔ Y, 3 ∣ Nat.card ↥(F11.CElt D.M V₀ u) := by
  intro X hX Y hY _ u hu
  have hXV : X ≤ V := by
    rcases hX with ⟨m, hm, rfl⟩
    exact s15_Tools_conj_wSub_le D h.hyp151.hyp125 hV hm
  have hYV : Y ≤ V := by
    rcases hY with ⟨m, hm, rfl⟩
    exact s15_Tools_conj_wSub_le D h.hyp151.hyp125 hV hm
  have huV : u ∈ V := (sup_le hXV hYV) hu
  have hle : F11.CTilde D.M V₀ V ≤ F11.CElt D.M V₀ u := by
    intro a ha
    exact Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 ha u) huV
  exact dvd_trans hct (Subgroup.card_dvd_of_le hle)

private theorem s16h_e3_CycThreeCent_three_dvd_of_mbar_fix
    (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (h : Setting16 D V₀ V L)
    (hfix : ∀ X ∈ wConj D.M V₀ V hV L, ∀ Y ∈ wConj D.M V₀ V hV L, X ≠ Y →
      ∀ u ∈ X ⊔ Y, ∃ φ ∈ Mbar D.M V₀ V hV, orderOf φ = 3 ∧
        ∀ (huV : u ∈ V), φ (mkTil V₀ V hV (IntMod.mk hV ⟨u, huV⟩)) =
          mkTil V₀ V hV (IntMod.mk hV ⟨u, huV⟩)) :
    ∀ X ∈ wConj D.M V₀ V hV L, ∀ Y ∈ wConj D.M V₀ V hV L, X ≠ Y →
      ∀ u ∈ X ⊔ Y, 3 ∣ Nat.card ↥(F11.CElt D.M V₀ u) := by
  intro X hX Y hY hXY u hu
  have hXV : X ≤ V := by
    rcases hX with ⟨m, hm, rfl⟩
    exact s15_Tools_conj_wSub_le D h.hyp151.hyp125 hV hm
  have hYV : Y ≤ V := by
    rcases hY with ⟨m, hm, rfl⟩
    exact s15_Tools_conj_wSub_le D h.hyp151.hyp125 hV hm
  have huV : u ∈ V := (sup_le hXV hYV) hu
  obtain ⟨φ, hφ, hord, hfixu⟩ := hfix X hX Y hY hXY u hu
  exact Sixteen21.dvd_card_cElt_of_mem_mbar hV hφ hord huV (hfixu huV)

theorem s16h_e3_CycThreeCent_three_dvd_of_not_dvd_ctilde
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
    (hct : ¬ 3 ∣ Nat.card ↥(F11.CTilde D.M V₀ V)) :
    ∀ X ∈ wConj D.M V₀ V hV L, ∀ Y ∈ wConj D.M V₀ V hV L, X ≠ Y →
      ∀ u ∈ X ⊔ Y, 3 ∣ Nat.card ↥(F11.CElt D.M V₀ u) :=
  s16h_e3_CycThreeCent_three_dvd_of_mbar_fix D hV h
    (s16h_e3_CycThreeCent_exists_three_fix D S hr3 hσ hV h hc hp hLp hχ hs3 hpσ h3 hn76 hct)

theorem s16h_e3_cyclic_three_cent
    (D : Data G) (S : s16h_Std D) (hr3 : CFSG.Open.evenRank G = 3) (hσ : D.sig = D.sig1)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (h : Setting16 D V₀ V L)
    (hc : Conc4_136 D V₀ V hV L)
    {p : ℕ} (hp : p.Prime) (hLp : IsCyclicOrd ↥(lBar V₀ V hV L) p)
    (hχ : ¬ ∀ n ∈ Mbar D.M V₀ V hV,
      n ∈ normalizer ((lBar V₀ V hV L : Subgroup _) : Set _) →
        ∀ l ∈ lBar V₀ V hV L, n * l = l * n)
    (hs3 : s15 D.M V₀ V hV L = 3)
    (hpσ : p ∉ D.sig) (h3 : D.sig = {3})
    (hn76 : ¬ (p = 7 ∧ rk ↥(wTil V₀ V hV L) = 6)) :
    ∀ X ∈ wConj D.M V₀ V hV L, ∀ Y ∈ wConj D.M V₀ V hV L, X ≠ Y →
      ∀ u ∈ X ⊔ Y, 3 ∣ Nat.card ↥(F11.CElt D.M V₀ u) := by
  by_cases hct : 3 ∣ Nat.card ↥(F11.CTilde D.M V₀ V)
  · exact s16h_e3_CycThreeCent_three_dvd_of_ctilde D hV h hct
  · exact s16h_e3_CycThreeCent_three_dvd_of_not_dvd_ctilde D S hr3 hσ hV h hc hp hLp hχ
      hs3 hpσ h3 hn76 hct

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
