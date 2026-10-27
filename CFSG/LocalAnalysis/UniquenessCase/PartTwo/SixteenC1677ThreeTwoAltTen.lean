module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonFam
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeAltRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_two_alt_three_dvd_kbar {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1) {n : ℕ}
    (hn5 : 5 ≤ n) (hn6 : n ≠ 6) (hA : UC22.IsAlt ↥(lBar V₀ V hV L) n)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z n)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    3 ∣ Nat.card ↥(kBar D.M V₀ V hV L) := by
  have hF := s16e_two_fam_alt D hV hn5 hA hsum
  obtain ⟨J₀, J₁, hJ₀, hJ₁, F⟩ :=
    s16e_two_cfg2 D c.std.hx c.std.h61 c.std.h127 c.std.h1214 hV c.setting c.ne hs hF
  have hE₀ := hF.natFacts.endUnits J₀ hJ₀
  have hE₁ := hF.natFacts.endUnits J₁ hJ₁
  have hHX := s16e_two_lStar_le D c.setting.hyp151 hV
  obtain ⟨e⟩ := s16e_two_lStar_equiv D c.std.h1217 c.setting.hyp151 hV
  have hAut' : Nat.card (MulAut ↥(lStar D.M V₀ V hV L)) ≤
      2 * Nat.card ↥(lStar D.M V₀ V hV L) := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv, Nat.card_congr e.toEquiv]
    exact (s15k_six_alt hA (by omega)).2
  have hcard := s16e_two_card_le_of_aut F hAut'
  have hinv4 : ∀ h ∈ lStar D.M V₀ V hV L, h ≠ 1 → h ^ 2 = 1 →
      4 ≤ rk ↥(commSub ⊤ (Subgroup.zpowers h)) := fun h hh h1 h2 =>
    s16e_two_rk_comm_ge F hh (s16e_two_alt_comm_rk_ge hn5 hJ₀ hh h1 h2)
      (s16e_two_alt_comm_rk_ge hn5 hJ₁ hh h1 h2)
  obtain ⟨t, htX, ht2, ht1, htrk⟩ :=
    s16e_two_involution_star D c.std.hx c.std.h61 c.std.h127 c.std.h1214 hV c.setting c.conc
  obtain ⟨hsup, -⟩ := s16e_two_sup_of_outer F hHX hE₀ hE₁ (s16e_two_alt_rk_ge hn5 hJ₀)
    (s16e_two_alt_rk_ge hn5 hJ₁) hinv4 hcard htX ht2 ht1 htrk
  have hT := s16e_two_trans_star D c.std.hx c.std.h61 c.std.h127 c.std.h1214 hV c.setting
    c.ne c.conc hs hF
  have h3 : 3 ∣ Nat.card ↥(s16e_two_cent (Mbar D.M (v1Sub D.M V₀ V hV L) V hV)
      (lStar D.M V₀ V hV L)) :=
    s16e_two_three_dvd_of_trans F hE₀ hE₁ hsup hT
  obtain ⟨ρ, -, hρL⟩ := s16e_star_equiv D c.std.h1217 c.setting.hyp151 hV
  have hK := s16e_two_map_cent ρ (s16e_two_lBar_le D c.setting.hyp151 hV)
    (s16e_two_lStar_le D c.setting.hyp151 hV) hρL
  have hK' : ((kBar D.M V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV)).map ρ.toMonoidHom =
      (s16e_two_cent (Mbar D.M (v1Sub D.M V₀ V hV L) V hV)
        (lStar D.M V₀ V hV L)).subgroupOf (Mbar D.M (v1Sub D.M V₀ V hV L) V hV) := by
    simpa only [kBar, s16e_two_cent] using hK
  have hcard_eq : Nat.card ↥(kBar D.M V₀ V hV L) =
      Nat.card ↥(s16e_two_cent (Mbar D.M (v1Sub D.M V₀ V hV L) V hV)
        (lStar D.M V₀ V hV L)) := by
    calc Nat.card ↥(kBar D.M V₀ V hV L)
        = Nat.card ↥((kBar D.M V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV)) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
            (inf_le_left : kBar D.M V₀ V hV L ≤ Mbar D.M V₀ V hV)).toEquiv).symm
      _ = Nat.card ↥(((kBar D.M V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV)).map
            ρ.toMonoidHom) :=
          (Subgroup.card_map_of_injective (MulEquiv.injective ρ)).symm
      _ = Nat.card ↥((s16e_two_cent (Mbar D.M (v1Sub D.M V₀ V hV L) V hV)
            (lStar D.M V₀ V hV L)).subgroupOf (Mbar D.M (v1Sub D.M V₀ V hV L) V hV)) := by
          rw [hK']
      _ = Nat.card ↥(s16e_two_cent (Mbar D.M (v1Sub D.M V₀ V hV L) V hV)
            (lStar D.M V₀ V hV L)) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe
            (inf_le_left : s16e_two_cent (Mbar D.M (v1Sub D.M V₀ V hV L) V hV)
              (lStar D.M V₀ V hV L) ≤ Mbar D.M (v1Sub D.M V₀ V hV L) V hV)).toEquiv
  rw [hcard_eq]
  exact h3

theorem s168e3_false_of_alt_ten {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hSchur : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hs : s15 D.M V₀ V hV L = 1) {n : ℕ} (hn10 : 10 ≤ n) (hn11 : n ≤ 11)
    (hA : UC22.IsAlt ↥(lBar V₀ V hV L) n)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z n)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) : False :=
  s168e3_false_of_alt_three_centralizer c hSchur hs (by omega) hA
    (s168e3_two_alt_three_dvd_kbar c hs (by omega) (by omega) hA hsum)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
