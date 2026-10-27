module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGroupFactsL2Seven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bridge13
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.L2Over17
public import CFSG.GH74.GLS.C3.Layer1.EvenSelBasic
public import CFSG.LocalAnalysis.SeitzReduction.CrossChar
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3312E
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP1SporNum
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22u
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGroupFacts
public import CFSG.LieType.SteinbergBRMulEquivCores
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.RankThreeUC
open CFSG.Blueprint (LieModel OddLieType)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open CFSG.ComponentClassification.HarrisLit.T1.SporRow (OddLieOrder)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem isL2Odd_seven_of_isL2Over17_seven {X : Type} [Group X] (h : IsL2Over17 X 7) :
    IsL2Odd X 7 := by
  obtain ⟨r, f, hr, hr2, hq, hf, hm⟩ := h
  have hdvd : r ∣ 7 := by
    rw [hq]; exact dvd_pow_self r (by omega)
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hdvd with h1 | h1
  · exact absurd h1 hr.one_lt.ne'
  · have h7 : 7 = 7 ^ f := by
      calc (7 : ℕ) = r ^ f := hq
        _ = 7 ^ f := by rw [h1]
    have hf1 : f = 1 := by
      rcases Nat.eq_zero_or_pos f with h0 | h0
      · rw [h0, pow_zero] at h7; omega
      · by_contra hne
        have h2 : 2 ≤ f := by omega
        have hle : 7 ^ 2 ≤ 7 ^ f := Nat.pow_le_pow_right (by norm_num) h2
        rw [← h7] at hle
        norm_num at hle
    subst h1; subst hf1
    simpa [IsL2Odd] using hm

theorem thin8_of_isL2Over17_seven {L : Subgroup G} (h : IsL2Over17 (Bar2 L) 7) :
    F08.Thin8 L := by
  haveI : Finite (Bar2 L) := inferInstance
  intro p hp hp2
  have hodd : IsL2Odd (Bar2 L) 7 := isL2Odd_seven_of_isL2Over17_seven h
  have hle : CFSG.Open.pRank p (⊤ : Subgroup (Bar2 L)) ≤ 1 := by
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank p (⊤ : Subgroup (Bar2 L))]
    exact Inputs1719.kL2SevenOddRank_holds (Bar2 L) hodd p hp hp2
  rw [← pRank_bar2_eq_of_odd (Y := L) hp hp2]
  exact hle

theorem oddLieOrder_of_oddLieType (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (h : OddLieType X) : OddLieOrder (Nat.card X) := by
  obtain ⟨t, n, p, f, hp, hp2, hadm, hm⟩ := h
  obtain ⟨-, h1, h2⟩ := hO X t n p f hadm hm
  exact ⟨t, n, p, f, hp, hp2, hadm, h1, h2⟩

theorem not_oddLieType_of_isJ1 (hO : LieOrderFormulasInput)
    {X : Type} [Group X] [Finite X] (hJ : IsJ1 X) : ¬ OddLieType X := by
  intro hodd
  have hcard : Nat.card X = 175560 := by
    obtain ⟨e⟩ := hJ
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J1.card_J1
  have h := oddLieOrder_of_oddLieType hO hodd
  rw [hcard] at h
  exact CFSG.ComponentClassification.GS82PumpInputs.SporNum.not_oddLieOrder_J1 h

theorem isL2Over17_five_of_alt5 {X : Type} [Group X]
    (e : X ≃* alternatingGroup (Fin 5)) : IsL2Over17 X 5 :=
  ⟨5, 1, Nat.prime_five, by norm_num, by rw [pow_one], le_rfl,
    Or.inl ⟨by decide, CFSG.Quasithin.H13.L3312.isL2_five_of_alt5 e⟩⟩

theorem isL2Over17_of_thin (hO : LieOrderFormulasInput) (hThin : ThinList13)
    (hK : K_LieModelNotL2)
    {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ} (hC : Ctx17_6 D V₀ V L r q)
    (hthin : F08.Thin8 L) : IsL2Over17 (Bar2 L) r ∧ 5 < r := by
  have hthin13 : F13.Thin13 L := hthin
  obtain ⟨hsimple, hlist⟩ := s13_list_bar hThin D hC.memL hthin13
  haveI : IsSimpleGroup (Bar2 L) := hsimple
  haveI : Finite (Bar2 L) := inferInstance
  have hcenter : Subgroup.center (Bar2 L) = ⊥ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21k_center_eq_bot hC.memL.2.2
  obtain ⟨e⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21k_barInf_equiv_of_center_bot hC.memL.2.2 hcenter
  obtain ⟨hr, hr2, t, n, f, hadm, -, hm⟩ := hC.lie
  have hm' : LieModel (Bar2 L) t n r f := hm.of_mulEquiv e
  have hodd : OddLieType (Bar2 L) := ⟨t, n, r, f, hr, hr2, hadm, hm'⟩
  have hfive : IsL2Over17 (Bar2 L) 5 → False := fun h =>
    hC.not_l2_five (isL2Over17_of_mulEquiv e h)
  have hL2r : IsL2Over17 (Bar2 L) r := by
    rcases hlist with ⟨a, ha⟩ | ⟨pL, hpL, hpL2, hmL⟩ | ⟨a, hsz⟩ | hJ1
    · exfalso
      have hdisj := CFSG.SeitzReduction.CrossChar.eq_of_lieModel_two_of_oddLieType hO ha hodd
      have ha2 : a = 2 := by
        rcases hdisj with ⟨-, -, h⟩ | ⟨-, h2, -⟩ | ⟨h1, -⟩
        · exact h
        · exact absurd h2 (by norm_num)
        · exact absurd h1 (by decide)
      subst ha2
      obtain ⟨e5⟩ : Nonempty (Bar2 L ≃* alternatingGroup (Fin 5)) :=
        CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model (Bar2 L) ha
      exact hfive (isL2Over17_five_of_alt5 e5)
    · have hp17 : IsL2Over17 (Bar2 L) pL := ⟨pL, 1, hpL, hpL2, by rw [pow_one], le_rfl, hmL⟩
      have htn : t = .PSL ∧ n = 2 := by
        by_contra hc
        exact hK (Bar2 L) t n r f pL hr2 (by tauto) hadm hm' hp17
      obtain ⟨rfl, rfl⟩ := htn
      have hpeq : r ^ f = pL := by
        have h := CFSG.GH74.GLS.EvenSelP.pow_eq_of_lieModel hr hr2 hpL hpL2 hm' hmL
        rwa [pow_one] at h
      have hf0 : f ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hpeq
        have := hpL.two_le
        omega
      have hrep : r = pL := by
        refine (Nat.prime_dvd_prime_iff_eq hr hpL).1 ?_
        exact hpeq ▸ dvd_pow_self r hf0
      have hf1 : f = 1 := by
        have hpeq' : pL ^ f = pL := by rw [← hrep]; exact hpeq.trans hrep.symm
        refine Nat.pow_right_injective hpL.two_le ?_
        simpa using hpeq'
      have hm1 : LieModel (Bar2 L) .PSL 2 pL 1 := by
        rw [← hrep, ← hf1]
        exact hm'
      exact ⟨pL, 1, hpL, hpL2, by rw [pow_one]; exact hrep, le_rfl, hm1⟩
    · exfalso
      exact CFSG.SeitzReduction.CrossChar.not_oddLieType_of_lieModel_two hO hsz
        (by rintro ⟨h, -⟩; exact absurd h (by decide))
        (by rintro ⟨h, -⟩; exact absurd h (by decide))
        (by rintro ⟨h, -⟩; exact absurd h (by decide))
        hodd
    · exfalso
      exact not_oddLieType_of_isJ1 hO hJ1 hodd
  refine ⟨hL2r, ?_⟩
  have hr3 : r ≠ 3 := by
    rintro rfl
    exact not_isL2Over17_three (Bar2 L) hL2r
  have hr5 : r ≠ 5 := fun h => hfive (h ▸ hL2r)
  obtain ⟨k, rfl⟩ := hr.odd_of_ne_two hr2
  have h2r : 2 ≤ 2 * k + 1 := hr.two_le
  have hk0 : k ≠ 0 := by rintro rfl; norm_num at h2r
  have hk1 : k ≠ 1 := by rintro rfl; exact hr3 rfl
  have hk2 : k ≠ 2 := by rintro rfl; exact hr5 rfl
  have hk3 : 3 ≤ k := by
    by_contra hc
    have hlt : k < 3 := Nat.not_le.mp hc
    interval_cases k <;> first | exact hk0 rfl | exact hk1 rfl | exact hk2 rfl
  omega

theorem uniqueMax_of_not_thin (D : Data G) {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) (h869 : F08.R869 D) (hnt : ¬ F08.Thin8 L) :
    UniqueMax D.M L := by
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le hC.memL.1
  have hcalN : calNOf L = {D.M} :=
    h869 L (Or.inl hC.memL) L le_rfl
      (sup_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 L)) hnt
  exact UC22.uc22p22u_uniqueMax_of_calN D hLM hcalN

theorem three_dvd_pred_mul_succ {r : ℕ} (hr : r.Prime) (hr3 : r ≠ 3) :
    3 ∣ (r - 1) * (r + 1) := by
  have h3r : ¬ 3 ∣ r := fun h => hr3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).1 h).symm
  have hlt : r % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hne : r % 3 ≠ 0 := fun h => h3r (Nat.dvd_of_mod_eq_zero h)
  have hdec : r = 3 * (r / 3) + r % 3 := (Nat.div_add_mod r 3).symm
  have hcase : r % 3 = 1 ∨ r % 3 = 2 := by omega
  rcases hcase with h | h
  · have h1 : 3 ∣ r - 1 := by
      refine ⟨r / 3, ?_⟩
      omega
    exact h1.mul_right (r + 1)
  · have h1 : 3 ∣ r + 1 := by
      refine ⟨r / 3 + 1, ?_⟩
      omega
    exact h1.mul_left (r - 1)

theorem isL2Odd_of_isL2Over17_prime {X : Type} [Group X] {q : ℕ} (hq : q.Prime)
    (h : IsL2Over17 X q) : IsL2Odd X q := by
  obtain ⟨r, f, hr, hr2, hqr, hf, hm⟩ := h
  have hdvd : r ∣ q := by rw [hqr]; exact dvd_pow_self r (by omega)
  rcases (Nat.dvd_prime hq).mp hdvd with h1 | h1
  · exact absurd h1 hr.one_lt.ne'
  · have hf1 : f = 1 := by
      have hq1 : q ^ 1 = q ^ f := by
        rw [pow_one]
        calc q = r ^ f := hqr
          _ = q ^ f := by rw [h1]
      exact (Nat.pow_right_injective hq.two_le hq1).symm
    subst h1; subst hf1
    simpa [IsL2Odd] using hm

theorem three_dvd_card_of_isL2Odd (hO : LieOrderFormulasInput) {X : Type} [Group X] [Finite X]
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3) (h : IsL2Odd X r) :
    3 ∣ Nat.card X := by
  obtain ⟨-, hM, -⟩ := hO X .PSL 2 r 1 h.admissible h
  simp only [pow_one] at hM
  have h2r : 2 ≤ r := hr.two_le
  have h2 : 2 * Nat.card X = r * ((r - 1) * (r + 1)) :=
    CFSG.SeitzReduction.CrossChar.two_mul_card_eq_of_PSL_two_odd (q' := r) (M := Nat.card X)
      (by omega) (hr.odd_of_ne_two hr2) hM
  have h3 : 3 ∣ r * ((r - 1) * (r + 1)) := (three_dvd_pred_mul_succ hr hr3).mul_left r
  rw [← h2] at h3
  exact (by norm_num : Nat.Coprime 3 2).dvd_of_dvd_mul_left h3

theorem three_dvd_card_of_isL2Over17 (hO : LieOrderFormulasInput) {L : Subgroup G} {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3) (h : IsL2Over17 (Bar2 L) r) :
    3 ∣ Nat.card L := by
  haveI : Finite (Bar2 L) := inferInstance
  have h3 := three_dvd_card_of_isL2Odd hO hr hr2 hr3 (isL2Odd_of_isL2Over17_prime hr h)
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L)]
  exact h3.mul_right _

theorem pRank_three_eq_one_of_thin_of_dvd {L : Subgroup G} (hthin : F08.Thin8 L)
    (h3 : 3 ∣ Nat.card L) : CFSG.Open.pRank 3 L = 1 := by
  have hle : CFSG.Open.pRank 3 L ≤ 1 := hthin 3 Nat.prime_three (by norm_num)
  have hge : 1 ≤ CFSG.Open.pRank 3 L := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 3 h3
    have hxG : orderOf ((x : ↥L) : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
    have hx3 : ((x : ↥L) : G) ^ 3 = 1 := by rw [← hxG]; exact pow_orderOf_eq_one _
    refine CFSG.SectionRank.le_pRank (p := 3) (by norm_num) (H := L)
      (E := Subgroup.zpowers ((x : ↥L) : G)) (k := 1) (Subgroup.zpowers_le.mpr x.2) ?_ ?_
    · exact isElemAbelian_zpowers hx3
    · rw [Nat.card_zpowers, hxG, pow_one]
  omega

theorem not_isL2Over17_five_of_isL2Over17 {X : Type} [Group X] [Finite X] {r : ℕ}
    (hr : IsL2Over17 X r) (h5 : 5 < r) : ¬ IsL2Over17 X 5 := by
  rintro ⟨q, g, hq, hq2, hq5, hg, hm5⟩
  obtain ⟨p, f, hp, hp2, hp5, hf, hmr⟩ := hr
  have h := CFSG.GH74.GLS.EvenSelP.pow_eq_of_lieModel hp hp2 hq hq2 hmr hm5
  have hr5 : r = 5 := by rw [hp5, h, ← hq5]
  omega

theorem oddLieType_of_isL2Over17 {X : Type} [Group X] {r : ℕ} (h : IsL2Over17 X r) :
    OddLieType X := by
  obtain ⟨p, f, hp, hp2, -, hf, hm⟩ := h
  exact ⟨.PSL, 2, p, f, hp, hp2, hm.admissible, hm⟩

theorem mem_uniqueSet_of_card_three (hO : LieOrderFormulasInput)
    {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ} (hC : Ctx17_6 D V₀ V L r q)
    (hthin : F08.Thin8 L) (hL2r : IsL2Over17 (Bar2 L) r) (h5 : 5 < r)
    (h8107 : F08.R8107 D) (hU3 : Inputs1719.K_U3FourPowThreeRankOne) :
    ∀ A : Subgroup G, A ≤ L → Nat.card A = 3 → A ∈ uniqueSet D.M := by
  intro A hAL hA3
  have hr : r.Prime := hC.lie.1
  have hr2 : r ≠ 2 := hC.lie.2.1
  have hr3 : r ≠ 3 := by omega
  have h3L : 3 ∣ Nat.card L := three_dvd_card_of_isL2Over17 hO hr hr2 hr3 hL2r
  have hp3L : CFSG.Open.pRank 3 L = 1 := pRank_three_eq_one_of_thin_of_dvd hthin h3L
  have hodd : OddLieType (Bar2 L) := oddLieType_of_isL2Over17 hL2r
  have hv := hC.violates
  simp only [Concl17_6] at hv
  have hdisj : (∀ g : G, g ∉ D.M → 3 ∉ piSet (L ⊓ D.M.map (MulAut.conj g).toMonoidHom)) ∨
      ¬((∃! K : Subgroup G, K ∈ calC D.M ∧ F08.Thin8 K ∧ CFSG.Open.pRank 3 K = 1) ∧
        ∀ K : Subgroup G, K ∈ calC D.M → ∀ n : ℕ, ¬ IsU3 (Bar2 K) (2 * n)) := by
    by_cases hpos : ∃ g : G, g ∉ D.M ∧ 3 ∈ piSet (L ⊓ D.M.map (MulAut.conj g).toMonoidHom)
    · refine Or.inr ?_
      rintro ⟨h1, h2⟩
      exact hv ⟨hL2r, fun _ => hpos, fun _ => ⟨h1, h2⟩⟩
    · refine Or.inl ?_
      intro g hg hmem
      exact hpos ⟨g, hg, hmem⟩
  rcases hdisj with hno | hnu
  · refine ⟨hAL.trans (CFSG.Quasithin.A3.subnormal_le hC.memL.1), ?_⟩
    intro g hAg
    by_cases hg : g ∈ D.M
    · refine Subgroup.mem_normalizer_iff_map_conj_eq.mp ?_
      rwa [CFSG.RankThreeCoreUniqueness.Helpers.maxTwoLocal_self_normalizing D.M D.maxLocal]
    · have hAK : A ≤ L ⊓ D.M.map (MulAut.conj g).toMonoidHom := le_inf hAL hAg
      have hdvd : Nat.card A ∣ Nat.card ↥(L ⊓ D.M.map (MulAut.conj g).toMonoidHom) := by
        have h1 : Nat.card ↥(A.subgroupOf (L ⊓ D.M.map (MulAut.conj g).toMonoidHom)) ∣
            Nat.card ↥(L ⊓ D.M.map (MulAut.conj g).toMonoidHom) :=
          Subgroup.card_subgroup_dvd_card _
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv] at h1
      exact absurd ⟨Nat.prime_three, hA3 ▸ hdvd⟩ (hno g hg)
  · rcases not_and_or.mp hnu with hnu1 | hnu2
    · have hex : ∃ K : Subgroup G, K ∈ calC D.M ∧ F08.Thin8 K ∧
          CFSG.Open.pRank 3 K = 1 ∧ K ≠ L := by
        by_contra hcon
        refine hnu1 ⟨L, ⟨hC.memL, hthin, hp3L⟩, fun K hK => ?_⟩
        by_contra hne
        exact hcon ⟨K, hK.1, hK.2.1, hK.2.2, hne⟩
      obtain ⟨K, hKmem, hKthin, hKp3, hKL⟩ := hex
      obtain ⟨A₂, hA₂K, -, hA₂card⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) K
      rw [hKp3, pow_one] at hA₂card
      exact (h8107 L hC.memL K hKmem (Ne.symm hKL) hp3L hKp3 (Or.inl hthin) (Or.inl hKthin)
        A A₂ hAL hA3 hA₂K hA₂card).1
    · have hexU : ∃ K : Subgroup G, K ∈ calC D.M ∧ ∃ n : ℕ, IsU3 (Bar2 K) (2 * n) := by
        by_contra hcon
        refine hnu2 (fun K hK n hU => ?_)
        exact hcon ⟨K, hK, n, hU⟩
      obtain ⟨K, hKmem, n, hU⟩ := hexU
      have hn1 : 1 ≤ n := by
        have hf : 1 ≤ 2 * n := hU.admissible.2.1
        omega
      have hp3K : CFSG.Open.pRank 3 K = 1 := by
        rw [← pRank_bar2_eq_of_odd (Y := K) Nat.prime_three (by norm_num)]
        exact hU3 (Bar2 K) n hn1 hU
      have hKL : K ≠ L := by
        rintro rfl
        have hdisj2 := CFSG.SeitzReduction.CrossChar.eq_of_lieModel_two_of_oddLieType hO hU hodd
        rcases hdisj2 with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h2, -⟩
        · exact absurd h1 (by decide)
        · exact absurd h1 (by decide)
        · exact absurd h2 (by norm_num)
      obtain ⟨A₂, hA₂K, -, hA₂card⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) K
      rw [hp3K, pow_one] at hA₂card
      exact (h8107 L hC.memL K hKmem (Ne.symm hKL) hp3L hp3K (Or.inl hthin) (Or.inr ⟨2 * n, hU⟩)
        A A₂ hAL hA3 hA₂K hA₂card).1

theorem seventeen_seven_two (hO : LieOrderFormulasInput) (hThin : ThinList13)
    (hK : K_LieModelNotL2)
    {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ} (hC : Ctx17_6 D V₀ V L r q)
    (hthin : F08.Thin8 L) (h8107 : F08.R8107 D)
    (hU3 : Inputs1719.K_U3FourPowThreeRankOne) : R17_7_2At D V₀ V L r q hC := by
  intro _ g hg h3mem
  obtain ⟨hL2r, h5⟩ := isL2Over17_of_thin hO hThin hK hC hthin
  have key := mem_uniqueSet_of_card_three hO hC hthin hL2r h5 h8107 hU3
  obtain ⟨-, hdvd⟩ := h3mem
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(L ⊓ D.M.map (MulAut.conj g).toMonoidHom)) 3 hdvd
  set A : Subgroup G := Subgroup.zpowers ((x : ↥(L ⊓ D.M.map (MulAut.conj g).toMonoidHom)) : G)
    with hAdef
  have hxG : orderOf ((x : ↥(L ⊓ D.M.map (MulAut.conj g).toMonoidHom)) : G) = 3 := by
    rw [Subgroup.orderOf_coe]; exact hx
  have hA3 : Nat.card A = 3 := by rw [hAdef, Nat.card_zpowers, hxG]
  have hAle : A ≤ L ⊓ D.M.map (MulAut.conj g).toMonoidHom := Subgroup.zpowers_le.mpr x.2
  have hmuniq := key A (hAle.trans inf_le_left) hA3
  refine hg ?_
  have h1 : g ∈ Subgroup.normalizer (D.M : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hmuniq.2 g (hAle.trans inf_le_right))
  rwa [CFSG.RankThreeCoreUniqueness.Helpers.maxTwoLocal_self_normalizing D.M D.maxLocal] at h1

theorem uniqueMax_of_thin (hO : LieOrderFormulasInput) (hThin : ThinList13)
    (hK : K_LieModelNotL2)
    {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ} (hC : Ctx17_6 D V₀ V L r q)
    (hthin : F08.Thin8 L) (h17_3 : R17_3At D V₀ V) (h8107 : F08.R8107 D)
    (hU3 : Inputs1719.K_U3FourPowThreeRankOne)
    (h920 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920odd D) :
    UniqueMax D.M L := by
  obtain ⟨hL2r, h5⟩ := isL2Over17_of_thin hO hThin hK hC hthin
  have key := mem_uniqueSet_of_card_three hO hC hthin hL2r h5 h8107 hU3
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le hC.memL.1
  have hr3 : r ≠ 3 := by have := hC.lie.1; omega
  have hr2 : r ≠ 2 := hC.lie.2.1
  have h3L : 3 ∣ Nat.card L := three_dvd_card_of_isL2Over17 hO hC.lie.1 hr2 hr3 hL2r
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 3 h3L
  have hxG : orderOf ((x : ↥L) : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  set A : Subgroup G := Subgroup.zpowers ((x : ↥L) : G) with hAdef
  have hA3 : Nat.card A = 3 := by rw [hAdef, Nat.card_zpowers, hxG]
  have hAL : A ≤ L := Subgroup.zpowers_le.mpr x.2
  have hAuniq : A ∈ uniqueSet D.M := key A hAL hA3
  unfold UniqueMax
  ext H
  simp only [calMOf, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hH, hLH⟩
    by_contra hne
    haveI : IsSimpleGroup G := D.standing.simple
    have htop : H ≠ ⊤ := CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top D.standing.nonab hH.1
    have hnotle : ¬ H ≤ D.M := fun hle => hne (hH.2 D.M D.maxLocal.1 hle).symm
    have hhyp : Hyp919c D L A L H :=
      ⟨hC.memL, hAL, hA3, hAuniq, hLM,
        by rw [inf_idem]
           exact (sup_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 L)).symm,
        by simp, ⟨0, by simp⟩, htop, hLH, hnotle⟩
    obtain ⟨A', hA'L, hA'p, hA'odd, hA'n⟩ :=
      h920 L A L H hhyp le_rfl r hC.lie.1 h5
        (isL2Odd_of_isL2Over17_prime hC.lie.1 hL2r)
    refine hA'n (h17_3 L hC.memL hthin A' ⟨Nat.card A', hA'p, ?_, rfl, hA'L⟩)
    intro h2
    rw [h2] at hA'odd
    exact (by decide : ¬ Odd 2) hA'odd
  · rintro rfl
    exact ⟨D.maxLocal, hLM⟩

theorem seventeen_seven (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q) (hO : LieOrderFormulasInput) (hThin : ThinList13)
    (hK : K_LieModelNotL2) (h17_3 : R17_3At D V₀ V) (h869 : F08.R869 D)
    (h8107 : F08.R8107 D) (hU3 : Inputs1719.K_U3FourPowThreeRankOne)
    (h920 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920odd D) :
    R17_7At D V₀ V L r q hC := by
  constructor
  · by_cases hthin : F08.Thin8 L
    · exact uniqueMax_of_thin hO hThin hK hC hthin h17_3 h8107 hU3 h920
    · exact uniqueMax_of_not_thin D hC h869 hthin
  · by_cases hthin : F08.Thin8 L
    · exact seventeen_seven_two hO hThin hK hC hthin h8107 hU3
    · intro h7
      exact absurd (thin8_of_isL2Over17_seven h7) hthin

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17