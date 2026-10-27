module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S213RestNN4
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332K33Cover
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.CoverCentre
public import CFSG.CGT.PushingUpLit.CGT6.EmbEndSmall
import CFSG.LocalAnalysis.UniquenessCase.UC22S213L3Cover
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Center
import CFSG.LocalAnalysis.UniquenessCase.UC22S213PrimeRank
import CFSG.LocalAnalysis.UniquenessCase.UC22S213Inner
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
import CFSG.LocalAnalysis.UniquenessCase.UC6K46Mult
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSylow
import CFSG.Adapters.LieModelL3U3Torus
import CFSG.GroupTheory.PGroup.PrimePartTransport
public import CFSG.CGT.Timmesfeld75.NodeAux

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)
open CFSG.Assembly.LowTwoRank (StatedLieTag)

variable {G : Type} [Group G] [Finite G]

private theorem uc22s213_dvd_three_of_odd {z : ℕ} (hodd : Odd z) (hz : z ∣ 48) : z ∣ 3 := by
  have h : z ∣ 3 * 2 ^ 4 := by simpa using hz
  exact (Nat.Coprime.pow_right 4 (Nat.coprime_two_right.2 hodd)).dvd_of_dvd_mul_right h

theorem uc22s213_card_center_bar2_dvd_three (hGA : GriessAllModelsStatement) {M L : Subgroup G}
    (hL : L ∈ calC M) {t : StatedLieTag} (ht : t = .PSL ∨ t = .PSU) {p f : ℕ}
    (hX : LieModel (BarInf L) t 3 p f) : Nat.card (center (Bar2 L)) ∣ 3 := by
  have hrow := griessRow_of_lieModel_classical hGA hX (by rcases ht with rfl | rfl <;> decide)
  have hg : (genericOrders t 3 p f).1 * (genericOrders t 3 p f).2 ∣ 3 := by
    rcases ht with rfl | rfl <;>
      simpa [genericOrders] using Nat.gcd_dvd_left 3 _
  have he : (exceptionalOrders t 3 p f).1 * (exceptionalOrders t 3 p f).2 ∣ 16 := by
    rcases ht with rfl | rfl <;> unfold exceptionalOrders <;> split <;> simp_all
  have hpos : 0 < ((genericOrders t 3 p f).1 * (genericOrders t 3 p f).2) *
      ((exceptionalOrders t 3 p f).1 * (exceptionalOrders t 3 p f).2) := by
    have h1 : 0 < (genericOrders t 3 p f).1 * (genericOrders t 3 p f).2 :=
      Nat.pos_of_ne_zero fun h0 => by rw [h0] at hg; omega
    have h2 : 0 < (exceptionalOrders t 3 p f).1 * (exceptionalOrders t 3 p f).2 :=
      Nat.pos_of_ne_zero fun h0 => by rw [h0] at he; omega
    positivity
  exact uc22s213_dvd_three_of_odd (uc22p20p_odd_center_bar2 ↥L)
    ((card_center_bar2_dvd_of_row hL hpos hrow).trans
      ((Nat.mul_dvd_mul hg he).trans (by norm_num)))

private theorem uc22s213_false_of_two_le_pRank {M L : Subgroup G} (hL : L ∈ calC M)
    (hq : ∀ q : ℕ, q.Prime → q ≠ 2 → 2 ≤ CFSG.Open.pRank q L →
      q ∣ Nat.card (center (Bar2 L)))
    (hZ : Nat.card (center (Bar2 L)) ∣ 3) {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2) (hs3 : s ≠ 3)
    (h2 : 2 ≤ CFSG.Open.pRank s (⊤ : Subgroup (BarInf L))) : False := by
  have hsZ : ¬ s ∣ Nat.card (center (Bar2 L)) := fun h =>
    hs3 ((Nat.prime_dvd_prime_iff_eq hs Nat.prime_three).1 (h.trans hZ))
  rw [uc22s213_pRank_barInf_of_prime hL.2.2 hs hs2 hsZ] at h2
  exact hsZ (hq s hs hs2 h2)

theorem uc22s213_fiveCovers_of_lieModel_three (hGA : GriessAllModelsStatement)
    {M L : Subgroup G} (hL : L ∈ calC M)
    (hq : ∀ q : ℕ, q.Prime → q ≠ 2 → 2 ≤ CFSG.Open.pRank q L →
      q ∣ Nat.card (center (Bar2 L)))
    (hZ : 3 ∣ Nat.card (center (Bar2 L))) {p f : ℕ}
    (hX : (p ^ f % 3 = 1 ∧ LieModel (BarInf L) .PSL 3 p f) ∨
      (p ^ f % 3 = 2 ∧ LieModel (BarInf L) .PSU 3 p f)) : FiveCovers (Bar2 L) := by
  obtain ⟨e0⟩ := uc22p21k_barInf_equiv_of_calC hL
  rcases hX with ⟨hc, hX⟩ | ⟨hc, hX⟩
  ·
    have hd := uc22s213_card_center_bar2_dvd_three hGA hL (Or.inl rfl) hX
    have hZ3 : Nat.card (center (Bar2 L)) = 3 := Nat.dvd_antisymm hd hZ
    obtain ⟨hp, hf, -⟩ := hX.admissible
    rcases eq_or_ne p 2 with rfl | hp2
    ·
      have hfe : Even f := by
        rcases Nat.even_or_odd f with h | ⟨k, rfl⟩
        · exact h
        · rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod] at hc
          norm_num at hc
      obtain ⟨k, hk⟩ := hfe
      rcases (by omega : f = 2 ∨ 3 ≤ f) with rfl | hf3
      ·
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨hL.2.2, LieModel.of_mulEquiv e0 hX⟩, hZ3⟩)))
      ·
        obtain ⟨r, p', f', hr, hr5, -, hX'⟩ := uc22s213_closedTorusL3_of_psl3_two hf3 hX
        refine (uc22s213_false_of_two_le_pRank hL hq hd hr (by omega) (by omega) ?_).elim
        rcases hX' with ⟨hrd, hX'⟩ | ⟨hrd, hX'⟩
        · exact LieModel.two_le_pRank_psl3_of_dvd hX' hr hrd
        · exact LieModel.two_le_pRank_psu3_of_dvd hX' hr hrd
    ·
      have hp3 : p ≠ 3 := by
        rintro rfl
        rw [Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (by omega))] at hc
        exact absurd hc (by norm_num)
      obtain ⟨-, hf1, hr⟩ := CFSG.SectionRank.classical_model_rank hp2
        (hX.statedClassicalModel_of_ne_zero (by norm_num))
      refine (uc22s213_false_of_two_le_pRank hL hq hd hp hp2 hp3 ?_).elim
      rcases hr with ⟨-, h | h | h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h
      · omega
      · omega
      · omega
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · omega
  ·
    have hd := uc22s213_card_center_bar2_dvd_three hGA hL (Or.inr rfl) hX
    have hZ3 : Nat.card (center (Bar2 L)) = 3 := Nat.dvd_antisymm hd hZ
    obtain ⟨hp, hf, hadm⟩ := hX.admissible
    rcases eq_or_ne p 2 with rfl | hp2
    ·
      have hfo : Odd f := by
        rcases Nat.even_or_odd f with ⟨k, rfl⟩ | h
        · rw [← two_mul, pow_mul, Nat.pow_mod] at hc
          norm_num at hc
        · exact h
      obtain ⟨k, hk⟩ := hfo
      have hf1 : f ≠ 1 := by
        rintro rfl
        exact hadm.2 rfl
      rcases (by omega : f = 3 ∨ 5 ≤ f) with rfl | hf5
      ·
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨hL.2.2, LieModel.of_mulEquiv e0 hX⟩, hZ3⟩)))
      ·
        obtain ⟨n, r, hXn, hr, hr3, hrd⟩ := uc22s213_closedU3_of_psu3_two (by omega) (by omega) hX
        exact (uc22s213_false_of_two_le_pRank hL hq hd hr (by omega) (by omega)
          (LieModel.two_le_pRank_psu3_of_dvd hXn hr hrd)).elim
    ·
      have hp3 : p ≠ 3 := by
        rintro rfl
        rw [Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (by omega))] at hc
        exact absurd hc (by norm_num)
      obtain ⟨-, hf1, hr⟩ := CFSG.SectionRank.classical_model_rank hp2
        (hX.statedClassicalModel_of_ne_zero (by norm_num))
      refine (uc22s213_false_of_two_le_pRank hL hq hd hp hp2 hp3 ?_).elim
      rcases hr with ⟨h, -⟩ | ⟨-, h | h⟩ | ⟨h, -⟩ | h
      · exact absurd h (by decide)
      · omega
      · omega
      · exact absurd h (by decide)
      · omega

section KS14


theorem uc22s213_center_bar2_eq_bot_of_pRank_three_le_one (hGA : GriessAllModelsStatement)
    (h32 : UCK.K32) (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M)
    (hZ : ¬ 3 ∣ Nat.card (center (Bar2 L))) (h1 : CFSG.Open.pRank 3 L ≤ 1) :
    center (Bar2 L) = ⊥ := by
  have hodd := uc22p20p_odd_center_bar2 ↥L
  obtain ⟨e0⟩ := uc22p21k_barInf_equiv_of_calC hL
  have hrank := uc22s213_pRank_three_barInf hL.2.2 hZ
  have hLtop : L ≠ ⊤ :=
    ne_top_of_le_ne_top (uc22p20a_M_ne_top D) (CFSG.Quasithin.A3.subnormal_le hL.1)
  rcases (by omega : CFSG.Open.pRank 3 L = 0 ∨ CFSG.Open.pRank 3 L = 1) with h0 | h1
  ·
    obtain ⟨hsimp, hnab⟩ := uc22p20c_barInf_simple (uc22p20e_cComp_of_calC hL)
    have := hsimp
    obtain ⟨i, ⟨f⟩⟩ := uc22p20d_inCatalog_bar2 D.standing.kProper hLtop hL.2.2
    have h3' : ¬ 3 ∣ Nat.card (BarInf L) := by
      have h := CFSG.GroupTheory.not_dvd_card_of_pRank_eq_zero Nat.prime_three
        (H := (⊤ : Subgroup (BarInf L))) (hrank.trans h0)
      rwa [Subgroup.card_top] at h
    obtain ⟨n, hn⟩ := CFSG.RankThree.PartTwo.KFacts.KS14.suzukiModel_of_inCatalog_of_not_three_dvd
      (BarInf L) hnab ⟨i, ⟨e0.trans f⟩⟩ h3'
    have : Group.IsPerfect (Bar2 L) := Group.isPerfect_def.mpr hL.2.2.1
    have h2 : IsPGroup 2 (center (Bar2 L)) :=
      CFSG.Quasithin.isPGroup_two_of_isSz (center (Bar2 L)) le_rfl
        (CFSG.CGT.Timmesfeld75.suzukiModel_of_mulEquiv e0 hn)
    have := CFSG.GH74.Generic.eq_bot_of_isPGroup_two_of_odd h2 hodd
    exact Subgroup.eq_bot_of_subsingleton _
  ·
    have hK : CFSG.Open.IsKGroup (Bar2 L ⧸ center (Bar2 L)) :=
      ((D.standing.kProper.isKGroup L hLtop).quotient (CFSG.pCore 2 ↥L)).quotient _
    have hrk : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L ⧸ center (Bar2 L))) = 1 :=
      (CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e0).symm.trans
        (hrank.trans h1)
    exact UCK.center_eq_bot_of_catalog hGA hSp (CFSG.Quasithin.A3.isQuasisimple_iff_open.2 hL.2.2)
      hodd hZ (h32 _ hK hL.2.2.2
        (CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hL.2.2)
        hrk)

end KS14

section K33


theorem uc22s213_k33Cover_quotient (hGA : GriessAllModelsStatement)
    (hAlt : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hSpor : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers)
    (hM22 : Nonempty (CFSG.Blueprint.NativeSporadic.Carrier .M22 ≃*
      (TauCeti.CFSGIndex.sporadic .M22).Group))
    {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M)
    (hZ : 3 ∣ Nat.card (center (Bar2 L))) (h3 : CFSG.Open.pRank 3 L ≤ 2) :
    UCK.K332Route.K33Cover (Bar2 L ⧸ GL83.I243.Cover.primeCentre 3 (Bar2 L)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Group.IsPerfect (Bar2 L) := Group.isPerfect_def.mpr hL.2.2.1
  have hLtop : L ≠ ⊤ :=
    ne_top_of_le_ne_top (uc22p20a_M_ne_top D) (CFSG.Quasithin.A3.subnormal_le hL.1)
  have hK : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) = CFSG.Open.pRank 3 L :=
    pRank_bar2_eq_of_odd Nat.prime_three (by norm_num)
  have h0 : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) ≠ 0 := by
    intro h0
    have h := CFSG.GroupTheory.not_dvd_card_of_pRank_eq_zero Nat.prime_three h0
    rw [Subgroup.card_top] at h
    exact h (hZ.trans (Subgroup.card_subgroup_dvd_card _))
  have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) ≠ 1 := fun h1 =>
    PartOne.Theorem82.not_dvd_card_center_of_pRank_eq_one (by norm_num) h1 hZ
  have hrk : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) = 2 := by omega
  have hN : ¬ 3 ∣ Nat.card (GL83.I243.Cover.primeCentre 3 (Bar2 L)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
      (GL83.I243.Cover.coprime_card_primeCentre (p := 3) (K := Bar2 L))
  obtain ⟨e1⟩ := GL83.I243.Cover.nonempty_equiv_center_quotient (p := 3) hL.2.2
  obtain ⟨i, ⟨f⟩⟩ := uc22p20d_inCatalog_bar2 D.standing.kProper hLtop hL.2.2
  have hZp := GL83.I243.Cover.isPGroup_center_quotient (p := 3) hL.2.2
  have hP : CFSG.pCore 3 (Bar2 L) ≠ ⊥ := by
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center (Bar2 L)) 3 hZ
    have hle : zpowers (z : Bar2 L) ≤ CFSG.pCore 3 (Bar2 L) := by
      apply le_sSup
      exact ⟨normal_of_le_center (zpowers_le.2 z.2),
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_coe, hz, pow_one])⟩
    intro hbot
    rw [hbot, le_bot_iff, zpowers_eq_bot] at hle
    rw [show z = 1 from Subtype.ext hle, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hne := GL83.I243.Cover.center_quotient_ne_bot hL.2.2 hP
  have h3Z : 3 ∣ Nat.card (center (Bar2 L ⧸ GL83.I243.Cover.primeCentre 3 (Bar2 L))) := by
    obtain ⟨k, hk⟩ := hZp.exists_card_eq
    rw [hk]
    refine dvd_pow_self 3 fun hk0 => hne ?_
    rw [hk0, pow_zero] at hk
    exact Subgroup.card_eq_one.1 hk
  have hrk' : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L ⧸ GL83.I243.Cover.primeCentre 3 (Bar2 L))) =
      2 := by
    rw [CFSG.SectionRank.pRank_quotient_eq _ hN]
    exact hrk
  exact UCK.K332Route.k33_threeCover_of_three_dvd hGA hAlt hSpor hM22 _
    (GL83.I243.Cover.isQuasisimple_quotient hL.2.2) ⟨i, ⟨e1.trans f⟩⟩ hZp h3Z hrk'

theorem uc22s213_fiveCovers_of_three_dvd (hGA : GriessAllModelsStatement)
    (hAlt : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hSpor : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers)
    (hM22 : Nonempty (CFSG.Blueprint.NativeSporadic.Carrier .M22 ≃*
      (TauCeti.CFSGIndex.sporadic .M22).Group))
    {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M)
    (hq : ∀ q : ℕ, q.Prime → q ≠ 2 → 2 ≤ CFSG.Open.pRank q L →
      q ∣ Nat.card (center (Bar2 L)))
    (hZ : 3 ∣ Nat.card (center (Bar2 L))) (h3 : CFSG.Open.pRank 3 L ≤ 2) :
    FiveCovers (Bar2 L) := by
  have hqs : CFSG.IsQuasisimple (Bar2 L) := CFSG.Quasithin.A3.isQuasisimple_iff_open.2 hL.2.2
  have hodd := uc22p20p_odd_center_bar2 ↥L
  obtain ⟨e0⟩ := uc22p21k_barInf_equiv_of_calC hL
  obtain ⟨e1⟩ := GL83.I243.Cover.nonempty_equiv_center_quotient (p := 3) hL.2.2
  rcases uc22s213_k33Cover_quotient hGA hAlt hSpor hM22 hL hZ h3 with
    ⟨-, -, ⟨eA⟩⟩ | ⟨-, -, ⟨eA⟩⟩ | ⟨-, -, ⟨eM⟩⟩ | ⟨p, f, hc, -, -, hm⟩ | ⟨p, f, hc, -, -, hm⟩
  ·
    have h6 := GL83.I243.CoverList.card_center_dvd_alternating hAlt hqs (n := 6) (by norm_num)
      (e1.symm.trans eA)
    rw [if_pos (Or.inl rfl)] at h6
    exact Or.inl ⟨hqs, Nat.dvd_antisymm (uc22s213_dvd_three_of_odd hodd (h6.trans (by norm_num)))
      hZ, ⟨e1.symm.trans eA⟩⟩
  ·
    have h7 := GL83.I243.CoverList.card_center_dvd_alternating hAlt hqs (n := 7) (by norm_num)
      (e1.symm.trans eA)
    rw [if_pos (Or.inr rfl)] at h7
    exact Or.inr (Or.inl ⟨hqs, Nat.dvd_antisymm
      (uc22s213_dvd_three_of_odd hodd (h7.trans (by norm_num))) hZ, ⟨e1.symm.trans eA⟩⟩)
  ·
    obtain ⟨b⟩ := hM22
    have h12 : Nat.card (center (Bar2 L)) ∣ 12 :=
      GL83.I243.CoverList.card_center_dvd_sporadic hSpor hqs (s := .M22)
        ((e1.symm.trans eM).trans b)
    exact Or.inr (Or.inr (Or.inl ⟨hqs, Nat.dvd_antisymm
      (uc22s213_dvd_three_of_odd hodd (h12.trans (by norm_num))) hZ, ⟨e1.symm.trans eM⟩⟩))
  ·
    exact uc22s213_fiveCovers_of_lieModel_three hGA hL hq hZ
      (Or.inl ⟨hc, LieModel.of_mulEquiv (e1.trans e0.symm) hm⟩)
  ·
    exact uc22s213_fiveCovers_of_lieModel_three hGA hL hq hZ
      (Or.inr ⟨hc, LieModel.of_mulEquiv (e1.trans e0.symm) hm⟩)

end K33

section Tables


theorem uc22s213_fiveCovers_of_calC (hGA : GriessAllModelsStatement)
    (hAlt : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hSpor : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers)
    (hM22 : Nonempty (CFSG.Blueprint.NativeSporadic.Carrier .M22 ≃*
      (TauCeti.CFSGIndex.sporadic .M22).Group))
    (h32 : UCK.K32) (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M)
    (hq : ∀ q : ℕ, q.Prime → q ≠ 2 → 2 ≤ CFSG.Open.pRank q L →
      q ∣ Nat.card (center (Bar2 L)))
    (hthin : ¬ F08.Thin8 L) (h3 : CFSG.Open.pRank 3 L ≤ 2) : FiveCovers (Bar2 L) := by
  by_cases hZ : 3 ∣ Nat.card (center (Bar2 L))
  · exact uc22s213_fiveCovers_of_three_dvd hGA hAlt hSpor hM22 hL hq hZ h3
  exfalso
  obtain ⟨r, hr, hr2, hrk⟩ : ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ 2 ≤ CFSG.Open.pRank r L := by
    by_contra h
    exact hthin fun r hr hr2 => by
      by_contra h2
      exact h ⟨r, hr, hr2, by omega⟩
  have h1 : CFSG.Open.pRank 3 L ≤ 1 := by
    by_contra h1
    exact hZ (hq 3 Nat.prime_three (by norm_num) (by omega))
  have hrZ := hq r hr hr2 hrk
  rw [uc22s213_center_bar2_eq_bot_of_pRank_three_le_one hGA h32 hSp hL hZ h1,
    Subgroup.card_bot] at hrZ
  exact hr.not_dvd_one hrZ

theorem s21_3RestNN4_of_tables (hGA : GriessAllModelsStatement)
    (hAlt : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hSpor : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers)
    (hM22 : Nonempty (CFSG.Blueprint.NativeSporadic.Carrier .M22 ≃*
      (TauCeti.CFSGIndex.sporadic .M22).Group))
    (h32 : UCK.K32) (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    {D : Data G} {Ch : Choice2011 G} : S21_3RestNN4 D Ch :=
  fun _ _ _ hL h5 _ hq hthin h3 _ _ _ _ _ =>
    (h5 (uc22s213_fiveCovers_of_calC hGA hAlt hSpor hM22 h32 hSp hL hq hthin h3)).elim

end Tables

end CFSG.LocalAnalysis.UniquenessCase.UC22
