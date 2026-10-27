module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortySix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CharTwoTorusOn
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20v
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Arith
public import CFSG.GroupTheory.NormalizerQuotientQuotient
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21k

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.QuasithinUnique (IsSylowTwoOf)

variable {G : Type} [Group G] [Finite G]

theorem pRank_normalizerQuotient_bar2_le_pRank_cartan {D : Data G} {L C : Subgroup G}
    (hL : L ∈ calC D.M) (hC : CIsCartanOf D.T L C) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    CFSG.Open.pRank r (⊤ : Subgroup (TauCeti.Subgroup.normalizerQuotient
      (((D.T ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))))) ≤
      CFSG.Open.pRank r C := by
  have hO2 : CFSG.pCore 2 ↥L ≤ (D.T ⊓ L).subgroupOf L := pCore_le_sylow_of_mem_calC hL
  have htrans : CFSG.Open.pRank r (⊤ : Subgroup
        (TauCeti.Subgroup.normalizerQuotient ((D.T ⊓ L).subgroupOf L))) =
      CFSG.Open.pRank r (⊤ : Subgroup (TauCeti.Subgroup.normalizerQuotient
        (((D.T ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))))) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt
      (CFSG.GroupTheory.normalizerQuotient_quotientEquiv (CFSG.pCore 2 ↥L)
        ((D.T ⊓ L).subgroupOf L) hO2)
  rw [← htrans]
  exact pRank_normalizerQuotient_le_pRank_cartan hL hC hr hr2

theorem cartanRank_le_pRank_cartan_on (hK4 : Inputs1719.K_CartanRankLeThree) {D : Data G}
    {L C : Subgroup G} (hL : L ∈ calC D.M) (hC : CIsCartanOf D.T L C) {t : StatedLieTag}
    {m n r : ℕ} (hrk : CS17LieRank t m ≤ 3) (hmodel : LieModel (BarInf L) t m 2 n)
    (hr : r.Prime) (hr2 : r ≠ 2) (hrdvd : r ∣ 2 ^ n - 1)
    (hPSL : t = .PSL → ¬ r ∣ m) (hE6 : t = .E6 → r ≠ 3) :
    CS17LieRank t m ≤ CFSG.Open.pRank r C := by
  let K := Bar2 L
  let S : Subgroup K := ((D.T ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
  have hq : CFSG.Open.IsQuasisimple K := hL.2.2
  have hodd : Odd (Nat.card (Subgroup.center K)) :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20p_odd_center_bar2 ↥L
  obtain ⟨e⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21k_barInf_equiv_of_calC hL
  have hmodelK : LieModel (K ⧸ Subgroup.center K) t m 2 n :=
    CFSG.Blueprint.LieModel.of_mulEquiv e hmodel
  have hS : IsSylowTwoOf S ⊤ := isSylowTwoOf_sylowBar2 hL
  have hK4app := hK4 t m n hrk K hmodelK hq hodd S hS r hr hr2 hrdvd hPSL hE6
  exact hK4app.trans (pRank_normalizerQuotient_bar2_le_pRank_cartan hL hC hr hr2)

theorem cartanRank_le_pRank_cartan (hK4 : Inputs1719.K_CartanRank) {D : Data G}
    {L C : Subgroup G} (hL : L ∈ calC D.M) (hC : CIsCartanOf D.T L C) {t : StatedLieTag}
    {m n r : ℕ} (hadm : StatedLieAdmissible t m 2 n) (hmodel : LieModel (BarInf L) t m 2 n)
    (hr : r.Prime) (hr2 : r ≠ 2) (hrdvd : r ∣ 2 ^ n - 1)
    (hPSL : t = .PSL → ¬ r ∣ m) (hE6 : t = .E6 → r ≠ 3) :
    CS17LieRank t m ≤ CFSG.Open.pRank r C := by
  let K := Bar2 L
  let S : Subgroup K := ((D.T ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
  have hq : CFSG.Open.IsQuasisimple K := hL.2.2
  have hodd : Odd (Nat.card (Subgroup.center K)) :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20p_odd_center_bar2 ↥L
  obtain ⟨e⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21k_barInf_equiv_of_calC hL
  have hmodelK : LieModel (K ⧸ Subgroup.center K) t m 2 n :=
    CFSG.Blueprint.LieModel.of_mulEquiv e hmodel
  have hS : IsSylowTwoOf S ⊤ := isSylowTwoOf_sylowBar2 hL
  have hK4app := hK4 K t m n hadm hmodelK hq hodd S hS r hr hr2 hrdvd hPSL hE6
  exact hK4app.trans (pRank_normalizerQuotient_bar2_le_pRank_cartan hL hC hr hr2)

theorem not_dvd_genericOrders_of_dvd_two_pow_sub_one {t : StatedLieTag} {m n r : ℕ}
    (ht : t ≠ .PSL) (hE6 : t ≠ .E6) (hn : 1 ≤ n) (hr : r.Prime) (hr2 : r ≠ 2)
    (hrdvd : r ∣ 2 ^ n - 1) :
    ¬ r ∣ (CFSG.Blueprint.Multiplier.genericOrders t m 2 n).1 *
      (CFSG.Blueprint.Multiplier.genericOrders t m 2 n).2 := by
  have hr3 : 3 ≤ r := by have := hr.two_le; omega
  have hpow : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
  have hqeven : Even (2 ^ n) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hnothalf : ¬ r ∣ (CFSG.Blueprint.Multiplier.genericOrders t m 2 n).2 := by
    obtain ⟨h1, h2⟩ :=
      CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.genericOrders_snd_le t m 2 n
    intro hd
    have := Nat.le_of_dvd h1 hd
    omega
  intro hd
  rcases hr.dvd_mul.mp hd with h1 | h1
  · cases t with
    | PSL => exact absurd rfl ht
    | E6 => exact absurd rfl hE6
    | PSU =>
      simp only [CFSG.Blueprint.Multiplier.genericOrders] at h1
      have hd2 : r ∣ 2 ^ n + 1 := (Nat.dvd_gcd_iff.mp h1).2
      have hsub : r ∣ 2 ^ n + 1 - (2 ^ n - 1) := Nat.dvd_sub hd2 hrdvd
      have h2 : 2 ^ n + 1 - (2 ^ n - 1) = 2 := by omega
      rw [h2] at hsub
      have := Nat.le_of_dvd (by norm_num) hsub
      omega
    | PSp =>
      simp only [CFSG.Blueprint.Multiplier.genericOrders] at h1
      have hg4 : Nat.gcd 2 (2 ^ n - 1) ≤ 2 := Nat.gcd_le_left _ (by norm_num)
      have hgpos : 0 < Nat.gcd 2 (2 ^ n - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
      have := Nat.le_of_dvd hgpos h1
      omega
    | POmegaOdd =>
      simp only [CFSG.Blueprint.Multiplier.genericOrders] at h1
      have := Nat.le_of_dvd (by norm_num) h1
      omega
    | POmegaPlus =>
      simp only [CFSG.Blueprint.Multiplier.genericOrders] at h1
      rw [if_pos hqeven] at h1
      exact hr.not_dvd_one (by simpa using h1)
    | POmegaMinus =>
      simp only [CFSG.Blueprint.Multiplier.genericOrders] at h1
      have hg4 : Nat.gcd 4 ((2 ^ n) ^ m + 1) ∣ 4 := Nat.gcd_dvd_left 4 _
      have hgpos : 0 < Nat.gcd 4 ((2 ^ n) ^ m + 1) :=
        Nat.gcd_pos_of_pos_left _ (by norm_num)
      have hle : r ≤ 4 :=
        (Nat.le_of_dvd hgpos h1).trans (Nat.le_of_dvd (by norm_num) hg4)
      interval_cases r
      · exact absurd (h1.trans hg4) (by norm_num)
      · exact absurd hr (by norm_num)
    | twistedE6 =>
      simp only [CFSG.Blueprint.Multiplier.genericOrders] at h1
      have hd1 : r ∣ 3 := (Nat.dvd_gcd_iff.mp h1).1
      have hd2 : r ∣ 2 ^ n + 1 := (Nat.dvd_gcd_iff.mp h1).2
      have hr3eq : r = 3 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 hd1
      rw [hr3eq] at hrdvd hd2
      have hsub : 3 ∣ 2 ^ n + 1 - (2 ^ n - 1) := Nat.dvd_sub hd2 hrdvd
      have h2 : 2 ^ n + 1 - (2 ^ n - 1) = 2 := by omega
      rw [h2] at hsub
      norm_num at hsub
    | E7 =>
      simp only [CFSG.Blueprint.Multiplier.genericOrders] at h1
      have hg4 : Nat.gcd 2 (2 ^ n - 1) ≤ 2 := Nat.gcd_le_left _ (by norm_num)
      have hgpos : 0 < Nat.gcd 2 (2 ^ n - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
      have := Nat.le_of_dvd hgpos h1
      omega
    | G2 =>
      simp only [CFSG.Blueprint.Multiplier.genericOrders] at h1
      exact hr.not_dvd_one (by simpa using h1)
    | F4 =>
      simp only [CFSG.Blueprint.Multiplier.genericOrders] at h1
      exact hr.not_dvd_one (by simpa using h1)
    | E8 =>
      simp only [CFSG.Blueprint.Multiplier.genericOrders] at h1
      exact hr.not_dvd_one (by simpa using h1)
    | trialityD4 =>
      simp only [CFSG.Blueprint.Multiplier.genericOrders] at h1
      exact hr.not_dvd_one (by simpa using h1)
    | twistedB2 =>
      simp only [CFSG.Blueprint.Multiplier.genericOrders] at h1
      exact hr.not_dvd_one (by simpa using h1)
    | twistedG2 =>
      simp only [CFSG.Blueprint.Multiplier.genericOrders] at h1
      exact hr.not_dvd_one (by simpa using h1)
    | twistedF4 =>
      simp only [CFSG.Blueprint.Multiplier.genericOrders] at h1
      exact hr.not_dvd_one (by simpa using h1)
    | Tits =>
      simp only [CFSG.Blueprint.Multiplier.genericOrders] at h1
      exact hr.not_dvd_one (by simpa using h1)
  · exact hnothalf h1

theorem not_dvd_card_center_bar2 (hN : uc22p20rNativeGriess) {M L : Subgroup G}
    (hL : L ∈ calC M) {t : StatedLieTag} {m n r : ℕ} (hmodel : LieModel (BarInf L) t m 2 n)
    (ht : t ≠ .PSL) (hE6 : t ≠ .E6) (hr : r.Prime) (hr2 : r ≠ 2) (hrdvd : r ∣ 2 ^ n - 1) :
    ¬ r ∣ Nat.card (center (Bar2 L)) := by
  intro hdvd
  have hq : CFSG.Open.IsQuasisimple (Bar2 L) := hL.2.2
  have hodd : Odd (Nat.card (center (Bar2 L))) :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20p_odd_center_bar2 ↥L
  obtain ⟨e⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21k_barInf_equiv_of_calC hL
  have hmodelK : LieModel (Bar2 L ⧸ Subgroup.center (Bar2 L)) t m 2 n :=
    CFSG.Blueprint.LieModel.of_mulEquiv e hmodel
  have hZ := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20v_card_center_dvd hN hq hodd hmodelK
  exact not_dvd_genericOrders_of_dvd_two_pow_sub_one ht hE6
    (CFSG.Blueprint.LieModel.admissible hmodel).2.1 hr hr2 hrdvd (hdvd.trans hZ)

theorem Ctx17_42.exists_cartan_rank_two_on {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ}
    {C Dc : Subgroup G} {Gamma : Set G} (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (h43 : R17_43At D V₀ V) (h46 : R17_46At D V₀ V) (h47 : R17_47At D V₀ V)
    (hK4 : Inputs1719.K_CartanRankLeThree) (hN : uc22p20rNativeGriess) :
    ∃ r, r.Prime ∧ r ≠ 2 ∧ r ∣ 2 ^ n - 1 ∧ 2 ≤ CFSG.Open.pRank r C ∧
      ¬ r ∣ Nat.card (center (Bar2 L)) := by
  obtain ⟨t, m, hadm, hmodel, hrank⟩ := ctx.rank
  have hl2 : l = 2 := h46 L X p n l C Dc Gamma ctx
  have hrank2 : CS17LieRank t m = 2 := by rw [hrank, hl2]
  have h43' : 2 < 2 ^ n := h43 L X p n l C Dc Gamma ctx
  have hn : 2 ≤ n := by
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp at h43'
    · exact h
  obtain ⟨r, hr, hrdvd⟩ := uc22p20v_exists_prime_dvd_sub_one hn
  have hr2 : r ≠ 2 := by
    rintro rfl
    have h2n : (2 : ℕ) ∣ 2 ^ n := dvd_pow_self 2 (by omega : n ≠ 0)
    have hpos : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
    have hsub : 2 ∣ 2 ^ n - (2 ^ n - 1) := Nat.dvd_sub h2n hrdvd
    have h2 : 2 ^ n - (2 ^ n - 1) = 1 := by omega
    rw [h2] at hsub
    exact hr.not_dvd_one hsub
  have htPSL : t ≠ .PSL := by
    rintro rfl
    simp [CS17LieRank] at hrank2
    have hm : m = 3 := by omega
    rw [hm] at hmodel
    exact h47 L X p n l C Dc Gamma ctx (by simpa [IsL3] using hmodel)
  have htE6 : t ≠ .E6 := by
    rintro rfl
    rw [show CS17LieRank .E6 m = 6 from rfl] at hrank2
    omega
  have hC2 : 2 ≤ CFSG.Open.pRank r C := by
    have h := cartanRank_le_pRank_cartan_on hK4 ctx.mem_calC ctx.cartan
      (hrank2.trans_le (by norm_num)) hmodel hr hr2 hrdvd
      (fun ht => absurd ht htPSL) (fun ht => absurd ht htE6)
    rwa [hrank2] at h
  exact ⟨r, hr, hr2, hrdvd, hC2,
    not_dvd_card_center_bar2 hN ctx.mem_calC hmodel htPSL htE6 hr hr2 hrdvd⟩

theorem Ctx17_42.exists_cartan_rank_two {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ}
    {C Dc : Subgroup G} {Gamma : Set G} (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (h43 : R17_43At D V₀ V) (h46 : R17_46At D V₀ V) (h47 : R17_47At D V₀ V)
    (hK4 : Inputs1719.K_CartanRank) (hN : uc22p20rNativeGriess) :
    ∃ r, r.Prime ∧ r ≠ 2 ∧ r ∣ 2 ^ n - 1 ∧ 2 ≤ CFSG.Open.pRank r C ∧
      ¬ r ∣ Nat.card (center (Bar2 L)) :=
  Ctx17_42.exists_cartan_rank_two_on ctx h43 h46 h47 hK4.leThree hN

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
