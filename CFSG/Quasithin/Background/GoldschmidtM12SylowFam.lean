module

public import CFSG.Quasithin.Background.GoldschmidtM12SylowCore
public import CFSG.GH74.Orders.LieType
public import CFSG.Quasithin.Background.GoldschmidtAutM12DataJ2
public import CFSG.Quasithin.Background.GoldschmidtAutM12DataM22
public import CFSG.Quasithin.Background.GoldschmidtAutM12DataM23
public import CFSG.Quasithin.H13.ExcludedOrders
public import CFSG.Sporadic.Schreier.J1Outer
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.Timmesfeld.Orders.Exceptional

public section

namespace CFSG.Quasithin.F6

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint AutM12Recog

namespace M12Sylow

theorem excl64_of_psl_char_two {S : Type} [Group S] [Finite S] {n f : ℕ}
    (h : StatedClassicalModel S .PSL n 2 f) (hN : 7 ≤ f * ((n - 1) * (n - 1 + 1) / 2)) :
    Excl64 S := by
  obtain ⟨-, hf, hn, -, -⟩ := h.1
  have hcard := (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl
  exact excl64_of_card_two_part hcard (CFSG.Timmesfeld.Orders.profile_ordA (by omega) hf).two hN

theorem excl64_of_psu_char_two {S : Type} [Group S] [Finite S] {n f : ℕ}
    (h : StatedClassicalModel S .PSU n 2 f) (hN : 7 ≤ f * ((n - 1) * (n - 1 + 1) / 2)) :
    Excl64 S := by
  obtain ⟨-, hf, hn, -⟩ := h.1
  have hcard := (CFSG.Timmesfeld.card_statedClassicalModel_two h).2.1 rfl
  exact excl64_of_card_two_part hcard
    (CFSG.Timmesfeld.Orders.profile_ordTwistedA (by omega) hf).two hN

theorem excl64_of_psp_char_two {S : Type} [Group S] [Finite S] {n f : ℕ}
    (h : StatedClassicalModel S .PSp n 2 f) (hN : 7 ≤ f * (n * n)) : Excl64 S := by
  obtain ⟨-, hf, -⟩ := h.1
  have hcard := (CFSG.Timmesfeld.card_statedClassicalModel_two h).2.2.1 rfl
  exact excl64_of_card_two_part hcard (CFSG.Timmesfeld.Orders.profile_ordBC hf).two hN

section Exceptional


theorem excl64_of_g2 {S : Type} [Group S] [Finite S] {f : ℕ} (hf : 2 ≤ f)
    (h : ChevalleyExceptionalModel S .G2 2 f) : Excl64 S := by
  have hcard : Nat.card S = CFSG.Open.ordG2 (2 ^ f) :=
    CFSG.Timmesfeld.card_chevalleyExceptionalModel_two h
  exact excl64_of_card_two_part hcard (CFSG.Timmesfeld.Orders.profile_ordG2 (by omega)).two
    (by omega)

theorem excl64_of_trialityD4 {S : Type} [Group S] [Finite S] {f : ℕ} (hf : 1 ≤ f)
    (h : ChevalleyExceptionalModel S .trialityD4 2 f) : Excl64 S := by
  have hcard : Nat.card S = CFSG.Open.ordTrialityD4 (2 ^ f) :=
    CFSG.Timmesfeld.card_chevalleyExceptionalModel_two h
  exact excl64_of_card_two_part hcard (CFSG.Timmesfeld.Orders.profile_ordTrialityD4 hf).two
    (by omega)

theorem excl64_of_twistedF4 {S : Type} [Group S] [Finite S] {f : ℕ}
    (h : ReeTitsModel S .twistedF4 2 f) : Excl64 S := by
  obtain ⟨k, -, hcard⟩ := CFSG.Quasithin.H13.card_eq_ordTwistedF4_of_reeTitsModel h
  exact excl64_of_card_two_part hcard
    (CFSG.Timmesfeld.Orders.profile_ordTwistedF4 (by omega)).two (by omega)

end Exceptional

section Suzuki


theorem excl64_of_suzuki {S : Type} [Group S] [Finite S] {f : ℕ} (hf5 : 5 ≤ f)
    (h : SuzukiModel S 2 f) : Excl64 S := by
  obtain ⟨-, a, -, hf, hcard⟩ := CFSG.GH74.card_of_suzukiModel h
  exact excl64_of_card_two_part hcard (CFSG.Timmesfeld.Orders.profile_ordSuzuki (by omega)).two
    (by omega)

end Suzuki

section Tits


theorem excl64_of_tits {S : Type} [Group S] [Finite S] (h : ReeTitsModel S .Tits 2 1) :
    Excl64 S := by
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv S 2 1 h
  have hc : Nat.card S = 17971200 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Schreier.Tits.card_titsD
  exact excl64_of_card (a := 11) (by norm_num) ⟨8775, by decide, by rw [hc]; norm_num⟩

end Tits

section Sporadic


theorem excl64_of_sporadic_large {S : Type} [Group S] [Finite S] {s : TauCeti.SporadicName}
    (hs : s = .M24 ∨ s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru)
    (e : S ≃* NativeSporadic.Carrier s) : Excl64 S := by
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · have hc : Nat.card S = 244823040 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.Mathieu.card_M24
    exact excl64_of_card (a := 10) (by norm_num) ⟨239085, by decide, by rw [hc]; norm_num⟩
  · have hc : Nat.card S = 86775571046077562880 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.J4.card_J4
    exact excl64_of_card (a := 21) (by norm_num)
      ⟨41377816699065, by decide, by rw [hc]; norm_num⟩
  · have hc : Nat.card S = 44352000 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.HS.card_HS
    exact excl64_of_card (a := 9) (by norm_num) ⟨86625, by decide, by rw [hc]; norm_num⟩
  · have hc : Nat.card S = 4030387200 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.He.card_He
    exact excl64_of_card (a := 10) (by norm_num) ⟨3935925, by decide, by rw [hc]; norm_num⟩
  · have hc : Nat.card S = 145926144000 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.Ru.card_Ru
    exact excl64_of_card (a := 14) (by norm_num) ⟨8906625, by decide, by rw [hc]; norm_num⟩

end Sporadic

theorem excl64_alternating {n : ℕ} (h5 : 5 ≤ n) (h7 : n ≤ 7) :
    Excl64 (alternatingGroup (Fin n)) := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  have hc : Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
    rw [nat_card_alternatingGroup]
    simp [Nat.card_eq_fintype_card]
  have hout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (alternatingGroup (Fin n))) ≤ 4 := by
    rcases (by omega : n = 5 ∨ n = 6 ∨ n = 7) with rfl | rfl | rfl
    · exact (Nat.le_of_dvd (by norm_num)
        (CFSG.Quasithin.SteinbergCB.isSolvable_outer_alternatingGroup (Or.inl rfl)).2).trans
        (by norm_num)
    · exact CFSG.Sporadic.SchreierLemmas.outer_alternating_six.1
    · exact (Nat.le_of_dvd (by norm_num)
        (CFSG.Quasithin.SteinbergCB.isSolvable_outer_alternatingGroup (Or.inr le_rfl)).2).trans
        (by norm_num)
  rcases (by omega : n = 5 ∨ n = 6 ∨ n = 7) with rfl | rfl | rfl
  · exact excl64_of_outer_le (a := 2) ⟨15, by decide, by rw [hc]; decide⟩ (by norm_num)
      (by norm_num) hout
  · exact excl64_of_outer_le (a := 3) ⟨45, by decide, by rw [hc]; decide⟩ (by norm_num)
      (by norm_num) hout
  · exact excl64_of_outer_le (a := 3) ⟨315, by decide, by rw [hc]; decide⟩ (by norm_num)
      (by norm_num) hout

theorem excl64_m11
    {S : Type} [Group S] [Finite S]
    (e : S ≃* ↥NativeSporadic.M11) : Excl64 S := by
  have : Finite ↥NativeSporadic.M11 := Finite.of_equiv S e.toEquiv
  refine Excl64.of_equiv ?_ e
  refine excl64_of_outer_le (a := 4) (c := 2)
    ⟨495, by decide, by rw [CFSG.Sporadic.Mathieu.card_M11]; norm_num⟩ (by norm_num)
    (by norm_num) ?_
  exact CFSG.Sporadic.Schreier.at_m11_schreier.1

theorem excl64_j1
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.J1) : Excl64 S := by
  have : Finite NativeSporadic.J1 := Finite.of_equiv S e.toEquiv
  refine Excl64.of_equiv ?_ e
  refine excl64_of_outer_le (a := 3) (c := 1)
    ⟨21945, by decide, by rw [CFSG.Sporadic.J1.card_J1]; norm_num⟩ (by norm_num) (by norm_num) ?_
  exact CFSG.Sporadic.Schreier.at_j1_schreier.1.le

theorem excl64_m22 {S : Type} [Group S] [Finite S] (e : S ≃* ↥NativeSporadic.M22) :
    Excl64 S :=
  excl64_of_hasE16 fun Q => by
    obtain ⟨B, -, hB, -, hc, -⟩ := Tab.hasTwoE16_of_mulEquiv Tab.M22Cert.hasTwoE16_m22 Q e
    exact ⟨B, hB, hc⟩

theorem excl64_m23 {S : Type} [Group S] [Finite S] (e : S ≃* ↥NativeSporadic.M23) :
    Excl64 S :=
  excl64_of_hasE16 fun Q => by
    obtain ⟨B, -, hB, -, hc, -⟩ := Tab.hasTwoE16_of_mulEquiv Tab.M23Cert.hasTwoE16_m23 Q e
    exact ⟨B, hB, hc⟩

theorem excl64_j2 {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.J2) : Excl64 S :=
  excl64_of_hasE16 fun Q => by
    obtain ⟨B, -, hB, -, hc, -⟩ := Tab.hasTwoE16_of_mulEquiv Tab.J2Cert.hasTwoE16_j2 Q e
    exact ⟨B, hB, hc⟩

end M12Sylow

end CFSG.Quasithin.F6
