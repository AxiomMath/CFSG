module

public import CFSG.LocalAnalysis.StandardType.GGExcSplitRootGenKG
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeRootGenKG
public import CFSG.LocalAnalysis.StandardType.GGTwE6SplitRootGenKG
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenKG
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenE8Cover
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenE7Final
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenF4KG
public import CFSG.LocalAnalysis.StandardType.GGTwE6PlusRootGenKG
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenF4ThreeKG
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRootGenKG
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLift
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Three
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Torus
public import CFSG.LocalAnalysis.StandardType.GGRootGenResQFourL
public import CFSG.LocalAnalysis.StandardType.GGRootGenResQFourF4Nbr
public import CFSG.LocalAnalysis.StandardType.GGRootGenResQFourTwE6Nbr
public import CFSG.LocalAnalysis.StandardType.GGRootGenExcVacuityL
public import CFSG.LocalAnalysis.StandardType.GGRootGenExcVacuityNbr
public import CFSG.LocalAnalysis.StandardType.GGRootGenQFourRest
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGTwistedF4DiagRaw
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6Holds
public import CFSG.LocalAnalysis.StandardType.GGExclNoIso
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45ConfigIso

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley

@[expose] def GGRootGenExcSplitLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGRootGenExcTag lab ∧ 2 ≤ lab.n ∧ p ∣ 2 ^ lab.n - 1 ∧ ¬ GGRootGenResQFourLabel p lab

@[expose] def GGRootGenExcPlusLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4 ∨ lab.tag = .twE6) ∧ 2 ≤ lab.n ∧
    p ∣ 2 ^ lab.n + 1 ∧ ¬ GGRootGenResQFourLabel p lab

theorem ggRootGenKGAvoidOn_excSplit
    : GGRootGenKGAvoidOn GGRootGenExcSplitLabel := by
  rintro p ⟨t, l, n⟩ hp hp2 hlab ⟨htag, hn, hpn, hres⟩
  dsimp only at hn hpn hres htag
  rcases htag with h | h | h | h | h <;> dsimp only at h <;> subst h
  ·
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    haveI : CharP K 2 := charP_two_of_card hK
    have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
    by_cases hp3 : p = 3
    · subst hp3
      exact ⟨K, inferInstance, inferInstance, hK, hQ', 5,
        TableBF4.ggTorusLift_of_mulEquiv (TableBExc.recipeEquiv .E6 K)
          (TableBExc.ggTorusLift_adjoint_E6_three hpq),
        E6ThreeRootGen.ggTorusRootGenAvoidKG_E6Three hpq⟩
    · exact ⟨K, inferInstance, inferInstance, hK, hQ', 6,
        TableBExc.ggTorusLift_E6 hp hp2 hp3 hpq,
        ggTorusRootGenAvoidKG_excSplit (Or.inl ⟨rfl, hp3⟩) hp hp2 hpq⟩
  ·
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    haveI : CharP K 2 := charP_two_of_card hK
    have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
    exact ⟨K, inferInstance, inferInstance, hK, hQ', 7,
      TableBExc.ggTorusLift_E7 hp hp2 hpq,
      ggTorusRootGenAvoidKG_excSplit (Or.inr (Or.inl rfl)) hp hp2 hpq⟩
  ·
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    haveI : CharP K 2 := charP_two_of_card hK
    have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
    exact ⟨K, inferInstance, inferInstance, hK, hQ', 8,
      TableBExc.ggTorusLift_E8 hp hp2 hpq,
      ggTorusRootGenAvoidKG_excSplit (Or.inr (Or.inr rfl)) hp hp2 hpq⟩
  ·
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    haveI : CharP K 2 := charP_two_of_card hK
    have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
    exact ⟨K, inferInstance, inferInstance, hK, hQ', 4,
      TableBF4.ggTorusLift_F4 hp hp2 hpq,
      ggTorusRootGenAvoidKG_F4Split hp hp2 hpq⟩
  ·
    exact TwE6Delta.labelAll rfl fun K _ _ hK =>
      ⟨4, ggTorusLift_twE6Dvd (n := n) (by omega) hK hp hp2 hpn,
        ggTorusRootGenAvoidKG_twE6Split (n := n) (by omega) hK hp hp2 hpn⟩

theorem ggRootGenKGAvoidOn_excPlus_of_lss92
    (hGen : PhiTwoTwE6GenInput) : GGRootGenKGAvoidOn GGRootGenExcPlusLabel := by
  rintro p ⟨t, l, n⟩ hp hp2 hlab ⟨htag, hn, hpn, hres⟩
  dsimp only at hn hpn hres htag
  have hK4 : ∀ {K : Type}, Nat.card K = 2 ^ n → 4 ≤ Nat.card K := fun hK => by
    rw [hK]; exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
  rcases htag with h | h | h | h <;> subst h
  ·
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    haveI : CharP K 2 := charP_two_of_card hK
    have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
    exact ⟨K, inferInstance, inferInstance, hK, hQ', 6, ggTorusLift_E7Plus hp hp2 hpq,
      ggTorusRootGenAvoidKG_excPlus_of_lss92 PhiTwoRootGen.phiTwoGenAt_E7 (Or.inl rfl) hp hp2 hpq
        (hK4 hK)⟩
  ·
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    haveI : CharP K 2 := charP_two_of_card hK
    have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
    exact ⟨K, inferInstance, inferInstance, hK, hQ', 7, ggTorusLift_E8Plus hp hp2 hpq,
      ggTorusRootGenAvoidKG_excPlus_of_lss92 PhiTwoRootGen.phiTwoGenAt_E8 (Or.inr rfl) hp hp2 hpq
        (hK4 hK)⟩
  ·
    have hp3 : p ≠ 3 := fun h => hres ⟨hn, h, h ▸ hpn, Or.inr rfl⟩
    have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    haveI : CharP K 2 := charP_two_of_card hK
    have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
    exact ⟨K, inferInstance, inferInstance, hK, hQ', 3, ggTorusLift_F4Plus hp hp2 hpq,
      ggTorusRootGenAvoidKG_F4Plus hp hp5 hpq (hK4 hK)⟩
  ·
    have hp3 : p ≠ 3 := fun h => hres ⟨hn, h, h ▸ hpn, Or.inl rfl⟩
    have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
    exact TwE6Delta.labelAll rfl fun K _ _ hK =>
      ⟨TwE6Delta.liftRank p, ggTorusLift_twE6Add (n := n) (by omega) hK hp hpn,
        ggTorusRootGenAvoidKG_twE6Plus_of_lss92 hGen (n := n) hn hK hp hp5 hpn⟩

private theorem ggRootGenExcSplitLabel_of_dvd {p : ℕ} {lab : LargeEvenLabel}
    (ht : GGRootGenExcTag lab) (hn : 2 ≤ lab.n) (hpn : p ∣ 2 ^ lab.n - 1) :
    GGRootGenExcSplitLabel p lab := by
  refine ⟨ht, hn, hpn, fun ⟨_, h3, h31, _⟩ => ?_⟩
  have hpos : 1 ≤ 2 ^ lab.n := Nat.one_le_two_pow
  subst h3
  omega

private theorem ggRootGenExcPlusLabel_or_res_of_dvd {p : ℕ} {lab : LargeEvenLabel}
    (ht : lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4 ∨ lab.tag = .twE6) (hn : 2 ≤ lab.n)
    (hpn : p ∣ 2 ^ lab.n + 1) :
    GGRootGenExcPlusLabel p lab ∨ (GGF4ThreeLabel p lab ∧ 2 ≤ lab.n) ∨
      (GGTwE6BadLabel p lab ∧ 2 ≤ lab.n) := by
  by_cases hres : GGRootGenResQFourLabel p lab
  · obtain ⟨-, h3, h31, h | h⟩ := hres
    · exact Or.inr (Or.inr ⟨⟨h, h3, h31⟩, hn⟩)
    · exact Or.inr (Or.inl ⟨⟨h, h3, h31⟩, hn⟩)
  · exact Or.inl ⟨ht, hn, hpn, hres⟩

private theorem ggRootGenQFourExc_cover_L {p : ℕ} {lab : LargeEvenLabel}
    (ht : GGRootGenExcTag lab) (hn : 2 ≤ lab.n) (hs : ¬ GGRootGenExcNonSplitLabel p lab) :
    GGRootGenExcSplitLabel p lab ∨ GGRootGenExcPlusLabel p lab ∨ GGRootGenResLLabel p lab := by
  have hs' : LargeEvenSplit p lab := not_not.mp fun h => hs ⟨ht, hn, h⟩
  rcases hs' with ⟨-, hpn⟩ | ⟨hu, -, hpn⟩ | ⟨h, -⟩ | ⟨h1, -⟩
  · exact Or.inl (ggRootGenExcSplitLabel_of_dvd ht hn hpn)
  ·
    have htw : lab.tag = .twE6 := by
      rcases ht with h | h | h | h | h <;> rw [h] at hu ⊢
      all_goals exact absurd trivial hu
    rcases ggRootGenExcPlusLabel_or_res_of_dvd (Or.inr (Or.inr (Or.inr htw))) hn hpn with
      h | ⟨⟨h, -⟩, -⟩ | ⟨⟨-, h3, h31⟩, -⟩
    · exact Or.inr (Or.inl h)
    · rw [htw] at h; cases h
    · exact Or.inr (Or.inr ⟨htw, h3, hn, h31⟩)
  · exfalso
    rcases ht with h' | h' | h' | h' | h' <;> rcases h with h | h <;> rw [h'] at h <;> cases h
  · omega

private theorem ggRootGenQFourExc_cover_nbr {p : ℕ} {lab : LargeEvenLabel}
    (ht : GGRootGenExcTag lab) (hn : 2 ≤ lab.n) (hs : ¬ GGRootGenExcNonHalfSplitLabel p lab) :
    GGRootGenExcSplitLabel p lab ∨ GGRootGenExcPlusLabel p lab ∨
      (GGF4ThreeLabel p lab ∧ 2 ≤ lab.n) ∨ (GGTwE6BadLabel p lab ∧ 2 ≤ lab.n) := by
  have hs' : LargeEvenHalfSplit p lab False := not_not.mp fun h => hs ⟨ht, hn, h⟩
  rcases hs' with hs' | ⟨h, hpn⟩ | ⟨-, hpn⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h1, -⟩
  · rcases ggRootGenQFourExc_cover_L ht hn fun h => h.2.2 hs' with h | h | ⟨h, h3, -, h31⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr ⟨⟨h, h3, h31⟩, hn⟩))
  · rcases h with h | h | h | h | h
    · exfalso; rcases ht with h' | h' | h' | h' | h' <;> rw [h'] at h <;> cases h
    · exfalso; rcases ht with h' | h' | h' | h' | h' <;> rw [h'] at h <;> cases h
    · exact Or.inr (ggRootGenExcPlusLabel_or_res_of_dvd (Or.inr (Or.inr (Or.inl h))) hn hpn)
    · exact Or.inr (ggRootGenExcPlusLabel_or_res_of_dvd (Or.inl h) hn hpn)
    · exact Or.inr (ggRootGenExcPlusLabel_or_res_of_dvd (Or.inr (Or.inl h)) hn hpn)
  · exact Or.inl (ggRootGenExcSplitLabel_of_dvd ht hn hpn)
  · exfalso; rcases ht with h' | h' | h' | h' | h' <;> rw [h'] at h <;> cases h
  · exfalso; rcases ht with h' | h' | h' | h' | h' <;> rw [h'] at h <;> cases h
  · omega

theorem ggRootGenLInputOnQFour_qFourExc_of_lss92
    (hGen : PhiTwoTwE6GenInput) : GGRootGenLInputOnQFour GGRootGenQFourExcLabel := by
  have hrows := ggRootGenLInputOnQFour_of_notNonSplit ggLabelRigidInput_holds
    (X := fun _ lab => ¬ (2 ≤ lab.n ∧ GGRootGenExcTag lab))
    fun G _ _ p B Bs x L D J hHyp hq hN hL => by
      have hL' := GGInnerDiagOnLabel.mono_label
        (S := fun p lab => GGRootGenOpenLabel p lab ∧
          ¬ (¬ (2 ≤ lab.n ∧ GGRootGenExcTag lab) ∨ GGRootGenExcNonSplitLabel p lab))
        (T := fun p lab => GGRootGenExcSplitLabel p lab ∨
          (GGRootGenExcPlusLabel p lab ∨ GGRootGenResLLabel p lab))
        (fun lab hlab =>
          have hx : 2 ≤ lab.n ∧ GGRootGenExcTag lab := not_not.mp fun h => hlab.2 (Or.inl h)
          ggRootGenQFourExc_cover_L hx.2 hx.1 fun h => hlab.2 (Or.inr h)) hL
      rcases hL'.elim_or with h | h
      · exact ggRootCompGenAvoiding_L_of_avoidOn ggRootGenKGAvoidOn_excSplit hHyp h
      rcases h.elim_or with h | h
      · exact ggRootCompGenAvoiding_L_of_avoidOn (ggRootGenKGAvoidOn_excPlus_of_lss92 hGen) hHyp h
      · exact ggRootGenLInputOnQFour_resL ggTwE6ThreeBstarRankInput_holds
          (ggTwE6ThreePlusKGAvoid_of_lss92 hGen) G p B Bs x L D J hHyp hq hN h
  intro G _ _ p B Bs x L D J hHyp hq hN hL
  exact hrows G p B Bs x L D J hHyp hq hN
    (hL.mono_label fun _ hlab => ⟨hlab.1, fun h => h hlab.2⟩)

theorem ggRootGenNbrInputOnQFour_qFourExc_of_lss92
    (hGen : PhiTwoTwE6GenInput) (hF4 : GGF4ThreeNbrRankInput)
    (hTw : GGTwE6ThreeNbrRankInput) : GGRootGenNbrInputOnQFour GGRootGenQFourExcLabel := by
  have hrows := ggRootGenNbrInputOnQFour_of_notNonHalfSplit ggLabelRigidInput_holds
    ggRawInnFieldInput_holds
    (ggRawInndiagIsoInput_of_rest (ggRawInndiagIsoRestInput_of_round5 ggRawInndiagIsoRound5_holds))
    (X := fun _ lab => ¬ (2 ≤ lab.n ∧ GGRootGenExcTag lab))
    fun G _ _ p B Bs x L D J hHyp hq hN y K hnb hK => by
      have hK' := GGInnerDiagOnLabel.mono_label
        (S := fun p lab => GGRootGenOpenLabel p lab ∧
          ¬ (¬ (2 ≤ lab.n ∧ GGRootGenExcTag lab) ∨ GGRootGenExcNonHalfSplitLabel p lab))
        (T := fun p lab => GGRootGenExcSplitLabel p lab ∨ (GGRootGenExcPlusLabel p lab ∨
          ((GGF4ThreeLabel p lab ∧ 2 ≤ lab.n) ∨ (GGTwE6BadLabel p lab ∧ 2 ≤ lab.n))))
        (fun lab hlab =>
          have hx : 2 ≤ lab.n ∧ GGRootGenExcTag lab := not_not.mp fun h => hlab.2 (Or.inl h)
          ggRootGenQFourExc_cover_nbr hx.2 hx.1 fun h => hlab.2 (Or.inr h)) hK
      rcases hK'.elim_or with h | h
      · exact ggRootCompGenAvoiding_nbr_of_avoidOn ggRootGenKGAvoidOn_excSplit hHyp hnb h
      rcases h.elim_or with h | h
      · exact ggRootCompGenAvoiding_nbr_of_avoidOn (ggRootGenKGAvoidOn_excPlus_of_lss92 hGen)
          hHyp hnb h
      rcases h.elim_or with h | h
      · exact ggRootGenNbrInputOnQFour_f4ThreePlus hF4 ggF4ThreePlusKGAvoid_holds
          G p B Bs x L D J hHyp hq hN y K hnb h
      · exact ggRootGenNbrInputOnQFour_twE6ThreePlus hTw (ggTwE6ThreePlusKGAvoid_of_lss92 hGen)
          G p B Bs x L D J hHyp hq hN y K hnb h
  intro G _ _ p B Bs x L D J hHyp hq hN y K hnb hK
  exact hrows G p B Bs x L D J hHyp hq hN y K hnb
    (hK.mono_label fun _ hlab => ⟨hlab.1, fun h => h hlab.2⟩)

end CFSG.StandardType

end
