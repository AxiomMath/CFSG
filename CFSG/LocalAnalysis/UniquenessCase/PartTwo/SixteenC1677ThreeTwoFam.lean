module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeTwoAltTen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeTwoLn
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeAlt6

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_s1_two_alt {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hSchur : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hs : s15 D.M V₀ V hV L = 1) {n : ℕ} (hn5 : 5 ≤ n) (hn11 : n ≤ 11) (hn6 : n ≠ 6)
    (hA : UC22.IsAlt ↥(lBar V₀ V hV L) n)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z n)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    Case168_2Star D V₀ V hV L := by
  have hwstar : wStar D.M V₀ V hV L = ⊤ :=
    s15_Three_wStar_eq_top D c.std.h1217 c.setting.hyp151 hV c.ne hs
  by_cases hn10 : 10 ≤ n
  · exact (s168e3_false_of_alt_ten c hSchur hs hn10 hn11 hA hsum).elim
  · have hn9 : n ≤ 9 := by omega
    have hsig : D.sig = {3} := s168e3_two_alt_sig c hs hn5 hn9 hn6 hA hsum
    obtain ⟨hK, L₀, hdir, hSym⟩ :=
      s16e_two_fam_alt_route D c.std.hx c.std.h61 c.std.h127 c.std.h1214 c.std.h638 hV
        c.setting c.ne c.conc hs (by rw [hsig]; exact Set.mem_singleton 3) hn5 hn6 hA hsum
    have hsum' : SumOfNat (fun H U Z => AlternatingNatural H U Z n)
        (lStar D.M V₀ V hV L) (⊤ : Subgroup (vStar D.M V₀ V hV L)) ⊥ 2 := by
      rw [← hwstar]
      exact hsum
    exact ⟨hK, ⟨⟨L₀, hdir, Or.inl ⟨n, hn5, hn11, hSym, hA, hsum'⟩⟩, hsig⟩⟩

theorem s168e3_s1_two_alt_six {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1)
    (hA : UC22.IsAlt ↥(lBar V₀ V hV L) 6)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z 6)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    Case168_1 D V₀ V hV L ∨ Case168_2Star D V₀ V hV L := by
  rcases s168e3_two_alt6_kbar_or_aut c hs hA hsum with hK3 | h1
  · have hsig : D.sig = {3} := s168e3_two_alt6_sig c hs hA hsum
    have h3 : 3 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 3
    have hF : s16e_two_Fam D V₀ V L hV (fun H U Z => AlternatingNatural H U Z 6) :=
      s16e_two_fam_alt D hV (by norm_num : 5 ≤ 6) hA hsum
    have hord : Nat.card ↥(lBar V₀ V hV L) = 360 := by
      rw [s15k_six_alt_card hA (by norm_num)]
      norm_num [Nat.factorial]
    obtain ⟨hSymK, L₀, hdir, hSymL0⟩ :=
      s168e3_two_route_outer_six c hs h3 hF
        (fun J hJ => s16e_two_alt_rk_ge (by norm_num) hJ)
        (fun J hJ h hh h1 h2 => s16e_two_alt_comm_rk_ge (by norm_num) hJ hh h1 h2)
        hord (fun J hJ => s16e_two_alt6_normalizer_isSym hJ) hK3
    have hwstar : wStar D.M V₀ V hV L = ⊤ :=
      s15_Three_wStar_eq_top D c.std.h1217 c.setting.hyp151 hV c.ne hs
    have hsum' : SumOfNat (fun H U Z => AlternatingNatural H U Z 6)
        (lStar D.M V₀ V hV L) (⊤ : Subgroup (vStar D.M V₀ V hV L)) ⊥ 2 := by
      rw [← hwstar]
      exact hsum
    exact Or.inr
      ⟨hSymK, ⟨⟨L₀, hdir, Or.inl ⟨6, by norm_num, by norm_num, hSymL0, hA, hsum'⟩⟩, hsig⟩⟩
  · exact Or.inl h1

theorem s168e3_s1_two_ln {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1) {m : ℕ} (hm3 : 3 ≤ m)
    (hm5 : m ≤ 5) (hLm : IsLn ↥(lBar V₀ V hV L) m 1)
    (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z m 1)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    Case168_2Star D V₀ V hV L := by
  have hsig : D.sig = {3} := s168e3_two_ln_sig c hs hm3 hm5 hLm hsum
  have h3 : 3 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 3
  have hF : s16e_two_Fam D V₀ V L hV (fun H U Z => BinaryNaturalSL H U Z m 1) :=
    s16e_two_fam_ln D hV hm3 hLm hsum
  have hK3 : 3 ∣ Nat.card ↥(s16e_two_cent (Mbar D.M (v1Sub D.M V₀ V hV L) V hV)
      (lStar D.M V₀ V hV L)) := by
    rcases (by omega : m = 3 ∨ 4 ≤ m) with hm | hm
    · have hm3' : m = 3 := hm
      subst hm3'
      have hcard : Nat.card ↥(lBar V₀ V hV L) = 168 := (s15k_pord_ln hm3 hLm).1 rfl
      have hdvd : Nat.card (MulAut ↥(lBar V₀ V hV L)) ∣ 2 * 168 := by
        have h := s16e_two_ln_card_aut_dvd hm3 hm5 hLm
        rwa [hcard] at h
      refine s168e3_two_three_dvd_of_not_sq c hs h3 hF ?_
      intro h9
      have h1 : 3 ^ 2 ∣ 2 * 168 := h9.trans hdvd
      norm_num at h1
    · exact s168e3_two_ln_three_dvd_kbar c hs h3 hm hm5 hLm hsum
  obtain ⟨hK, hdir⟩ := s168e3_two_route_autFrom c hs h3 hF
    (fun J hJ => s16e_two_ln_autFromGroup hJ) hK3
  have hwstar : wStar D.M V₀ V hV L = ⊤ :=
    s15_Three_wStar_eq_top D c.std.h1217 c.setting.hyp151 hV c.ne hs
  have hsum' : SumOfNat (fun H U Z => BinaryNaturalSL H U Z m 1)
      (lStar D.M V₀ V hV L) (⊤ : Subgroup (vStar D.M V₀ V hV L)) ⊥ 2 := by
    rw [← hwstar]
    exact hsum
  exact ⟨hK, ⟨⟨lBar V₀ V hV L, hdir,
    Or.inr (Or.inl ⟨m, hm3, hm5, hLm, hLm, hsum'⟩)⟩, hsig⟩⟩

theorem s168e3_s1_two_sp {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1)
    (hSp : IsSpn ↥(lBar V₀ V hV L) 6 1)
    (hsum : SumOfNat (fun H U Z => NatSpn H U Z 6 1)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    Case168_2Star D V₀ V hV L := by
  have hsig : D.sig = {3} := s168e3_two_sp_sig c hs hSp hsum
  have h3 : 3 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 3
  obtain ⟨hK, hdir⟩ :=
    s16e_two_fam_sp_main D c.std.hx c.std.h61 c.std.h127 c.std.h1214 c.std.h638 hV
      c.setting c.ne c.conc hs h3 hSp hsum
  have hwstar : wStar D.M V₀ V hV L = ⊤ :=
    s15_Three_wStar_eq_top D c.std.h1217 c.setting.hyp151 hV c.ne hs
  have hsumTop : SumOfNat (fun H U Z => NatSpn H U Z 6 1)
      (lStar D.M V₀ V hV L) (⊤ : Subgroup (vStar D.M V₀ V hV L)) ⊥ 2 := by
    rw [← hwstar]
    exact hsum
  exact ⟨hK, ⟨⟨lBar V₀ V hV L, hdir,
    Or.inr (Or.inr (Or.inl ⟨hSp, hSp, hsumTop⟩))⟩, hsig⟩⟩

theorem s168e3_s1_two_om_six {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1)
    (hOm : IsOmegaMinus ↥(lBar V₀ V hV L) 6 1)
    (hsum : SumOfNat (fun H U Z => NatOmegaMinus H U Z 6 1)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    Case168_2Star D V₀ V hV L := by
  have hsig : D.sig = {3} := s168e3_two_om_sig c hs (Or.inl rfl) hOm hsum
  have h3 : 3 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 3
  obtain ⟨hK, L₀, hdir, hO⟩ :=
    s16e_two_fam_om_main D c.std.hx c.std.h61 c.std.h127 c.std.h1214 c.std.h638 hV
      c.setting c.ne c.conc hs h3 (Or.inl rfl) hOm hsum
  have hwstar : wStar D.M V₀ V hV L = ⊤ :=
    s15_Three_wStar_eq_top D c.std.h1217 c.setting.hyp151 hV c.ne hs
  have hsum' : SumOfNat (fun H U Z => NatOmegaMinus H U Z 6 1)
      (lStar D.M V₀ V hV L) (⊤ : Subgroup (vStar D.M V₀ V hV L)) ⊥ 2 := by
    rw [← hwstar]
    exact hsum
  exact ⟨hK, ⟨⟨L₀, hdir,
    Or.inr (Or.inr (Or.inr (Or.inl ⟨hO, hOm, hsum'⟩)))⟩, hsig⟩⟩

theorem s168e3_s1_two_om_eight {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1)
    (hOm : IsOmegaMinus ↥(lBar V₀ V hV L) 8 1)
    (hsum : SumOfNat (fun H U Z => NatOmegaMinus H U Z 8 1)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    Case168_2Star D V₀ V hV L := by
  have hsig : D.sig = {3} := s168e3_two_om_sig c hs (Or.inr rfl) hOm hsum
  have h3 : 3 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 3
  obtain ⟨hK, L₀, hdir, hO⟩ :=
    s16e_two_fam_om_main D c.std.hx c.std.h61 c.std.h127 c.std.h1214 c.std.h638 hV
      c.setting c.ne c.conc hs h3 (Or.inr rfl) hOm hsum
  have hwstar : wStar D.M V₀ V hV L = ⊤ :=
    s15_Three_wStar_eq_top D c.std.h1217 c.setting.hyp151 hV c.ne hs
  have hsum' : SumOfNat (fun H U Z => NatOmegaMinus H U Z 8 1)
      (lStar D.M V₀ V hV L) (⊤ : Subgroup (vStar D.M V₀ V hV L)) ⊥ 2 := by
    rw [← hwstar]
    exact hsum
  exact ⟨hK, ⟨⟨L₀, hdir,
    Or.inr (Or.inr (Or.inr (Or.inr ⟨hO, hOm, hsum'⟩)))⟩, hsig⟩⟩

theorem s168e3_row162_2 {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hSchur : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (h : Case162_2 D V₀ V hV L) :
    Case168_1 D V₀ V hV L ∨ Case168_2Star D V₀ V hV L := by
  obtain ⟨hs, hcase⟩ := h
  rcases hcase with ⟨n, hn5, hn11, hA, hsum⟩ | ⟨m, hm3, hm5, hLm, hsum⟩ | ⟨hSp, hsum⟩ |
    ⟨hOm, hsum⟩ | ⟨hOm, hsum⟩
  · by_cases hn6 : n = 6
    · subst hn6
      exact s168e3_s1_two_alt_six c hs hA hsum
    · exact Or.inr (s168e3_s1_two_alt c hSchur hs hn5 hn11 hn6 hA hsum)
  · exact Or.inr (s168e3_s1_two_ln c hs hm3 hm5 hLm hsum)
  · exact Or.inr (s168e3_s1_two_sp c hs hSp hsum)
  · exact Or.inr (s168e3_s1_two_om_six c hs hOm hsum)
  · exact Or.inr (s168e3_s1_two_om_eight c hs hOm hsum)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
