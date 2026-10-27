module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.NotThinShapes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1b
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20g
public import CFSG.RankThree.PartTwo.Sec4.Item422Proof
public import CFSG.RankThree.PartOne.K1320.Pair
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointSetup
public import CFSG.GroupTheory.PElementSubgroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open scoped commutatorElement
open CFSG.LocalAnalysis.UniquenessCase.UC22.F09 (Inv9)

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_ne_bot_of_mem_calC {M L : Subgroup G}
    (hchar : IsCharTwoType G) (hM : IsTwoLocal M) (hL : L ∈ calC M) :
    pCoreOf 2 L ≠ ⊥ := by
  intro hbot
  have hbot' : CFSG.pCore 2 ↥L = ⊥ := by
    have h := hbot
    rw [show pCoreOf 2 L = (CFSG.pCore 2 ↥L).map L.subtype from rfl,
      Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective] at h
    exact h
  let e : Bar2 L ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hbot').trans QuotientGroup.quotientBot
  have hq : CFSG.Open.IsQuasisimple L :=
    CFSG.Open.IsQuasisimple.of_mulEquiv e.symm hL.2.2
  exact CFSG.RankThreeEvenClassification.Helpers.charTwoType_no_local_component hchar M hM L
    ⟨CFSG.Open.IsSubnormal.le hL.1, hL.1, hq⟩

theorem isL2_field_unique {X : Type} [Group X] [Finite X] {n m : ℕ}
    (h1 : IsL2 X n) (h2 : IsL2 X m) : n = m :=
  CFSG.RankThree.PartOne.K1320.psl_two_degree_eq
    (LieModel.statedClassicalModel_of_ne_zero (by decide : (2 : ℕ) ≠ 0) h1)
    (LieModel.statedClassicalModel_of_ne_zero (by decide : (2 : ℕ) ≠ 0) h2)

theorem dvd_card_bar2_of_isL2_of_dvd_two_pow_sub_one {L : Subgroup G} {n r : ℕ}
    (hL2 : IsL2 (Bar2 L) n) (hrdvd : r ∣ 2 ^ n - 1) : r ∣ Nat.card (Bar2 L) := by
  have hcard : Nat.card (Bar2 L) = 2 ^ n * (2 ^ (2 * n) - 1) := card_of_isL2 hL2
  have hdvd2 : r ∣ 2 ^ (2 * n) - 1 :=
    hrdvd.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 (⟨2, by ring⟩ : n ∣ 2 * n))
  rw [hcard]
  exact dvd_mul_of_dvd_right hdvd2 _

theorem exists_elemAbelian_sq_of_mem_calC_ne {X L L' A : Subgroup G} {n r : ℕ}
    (hL : L ∈ calC X) (hL' : L' ∈ calC X) (hne : L ≠ L')
    (hA : A ≤ L) (hAcard : Nat.card A = r) (hr : r.Prime) (hrodd : r ≠ 2)
    (hsimple : IsSimpleGroup (Bar2 L)) (hnonab : ∃ a b : Bar2 L, a * b ≠ b * a)
    (hL2 : IsL2 (Bar2 L') n) (hrdvd : r ∣ 2 ^ n - 1) :
    ∃ E : Subgroup G, E ≤ X ∧ IsElemAbelian r E ∧ Nat.card E = r ^ 2 := by
  classical
  have hnorm : L ≤ Subgroup.normalizer (L' : Set G) :=
    uc22p22u_calC_normalizes hL' hL (Ne.symm hne)
  have hAL' : A ≤ Subgroup.normalizer (L' : Set G) := hA.trans hnorm
  have hrdvdBar : r ∣ Nat.card (Bar2 L') :=
    dvd_card_bar2_of_isL2_of_dvd_two_pow_sub_one hL2 hrdvd
  have hrdvdL : r ∣ Nat.card ↥L' := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L')
    rw [show Nat.card ↥L' = Nat.card (Bar2 L') * Nat.card ↥(CFSG.pCore 2 ↥L') from h]
    exact dvd_mul_of_dvd_left hrdvdBar _
  haveI : Fact (Nat.Prime r) := ⟨hr⟩
  obtain ⟨b, hbL', hbcent, hborder⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Item422Proof.exists_orderOf_eq_mem_centralizer
      (IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hAcard)) hAL' hrdvdL
  let B : Subgroup G := Subgroup.zpowers b
  have hBL' : B ≤ L' := Subgroup.zpowers_le.mpr hbL'
  have hcentL : Subgroup.center (Bar2 L) = ⊥ :=
    CFSG.GorensteinWalter.Helpers.center_eq_bot_of_noncommutative hnonab
  have hcentL' : Subgroup.center (Bar2 L') = ⊥ := uc22p22g_center_bot hL2
  have hcalCinf : A ⊓ B ≤ pCoreOf 2 L ⊓ pCoreOf 2 L' :=
    (inf_le_inf hA hBL').trans
      (calC_inf_le_pCore_of_ne
        hL hL' hne hcentL hcentL')
  have hinf : A ⊓ B ≤ pCoreOf 2 L := hcalCinf.trans inf_le_left
  have hbA : b ∉ A := by
    intro hbA
    have hbO2 : b ∈ pCoreOf 2 L := hinf ⟨hbA, Subgroup.mem_zpowers b⟩
    have h2grp : IsPGroup 2 ↥(pCoreOf 2 L) := uc22p20b_isPGroup_pCoreOf L
    exact hrodd (CFSG.QuasithinUnique.L246C127.eq_two_of_orderOf_eq_prime h2grp hbO2 hr hborder)
  have hcommAB : ∀ a ∈ A, a * b = b * a := by
    intro a ha
    exact Subgroup.mem_centralizer_iff.mp hbcent a ha
  obtain ⟨hEel, hEcard⟩ :=
    CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute hAcard hborder hbA hcommAB
  refine ⟨A ⊔ Subgroup.zpowers b, ?_, hEel, hEcard⟩
  exact sup_le (hA.trans (IsSubnormal.le hL.1)) (hBL'.trans (IsSubnormal.le hL'.1))

theorem exists_mem_uniqueSet_of_isL2_ne {D : Data G} {V₀ V : Subgroup G} {n r : ℕ}
    {L X L' : Subgroup G}
    (h3 : R17_3At D V₀ V) (hL : L ∈ calC D.M) (hXeq : X = conjClosure D.M L)
    (hXsup : X = L ⊔ L') (hL' : L' ∈ calC D.M) (hneLL' : L' ≠ L)
    (hthin : F08.Thin8 L) (hL2L : IsL2 (Bar2 L) n) (hL2L' : IsL2 (Bar2 L') n)
    (hmore : P17_42_more D X n)
    (hr : r.Prime) (hr5 : 5 < r) (hrdvd : r ∣ 2 ^ n - 1) :
    ∃ A : Subgroup G, A ≤ L ∧ Nat.card A = r ∧
      A ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M := by
  classical
  have hrodd : r ≠ 2 := by omega
  have hsimple : IsSimpleGroup (Bar2 L) :=
    LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2L
  have hnonab : ∃ a b : Bar2 L, a * b ≠ b * a :=
    CFSG.ComponentClassification.HarrisLit.nonabelian_of_lieModel_psl2
      (p := 2) (f := n) hL2L
  have hLM : L ≤ D.M := IsSubnormal.le hL.1
  have hXM : X ≤ D.M := by
    rw [hXeq]
    exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThree.conjClosure_le hLM
  have hL'X : L' ≤ X := by rw [hXsup]; exact le_sup_right
  have hL'X' : L' ∈ calC X := uc22p22u_calC_of_le hL' hL'X hXM
  have hLX' : L ∈ calC X := uc22p22u_calC_of_le hL (by rw [hXsup]; exact le_sup_left) hXM
  have hmX : X = Opp r D.M := (hmore.2 r hr hr5 hrdvd).1
  have hmE : ∀ E : Subgroup G, E ≤ X → IsElemAbelian r E → Nat.card E = r ^ 2 →
      E ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M :=
    (hmore.2 r hr hr5 hrdvd).2
  have hrdvdBar : r ∣ Nat.card (Bar2 L) :=
    dvd_card_bar2_of_isL2_of_dvd_two_pow_sub_one hL2L hrdvd
  obtain ⟨A, hAL, hAcard⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_exists_subgroup_of_dvd_card_bar hr hrdvdBar
  have hAM : A ≤ D.M := hAL.trans hLM
  have hN : Subgroup.normalizer (A : Set G) ≤ D.M :=
    h3 L hL hthin A ⟨r, hr, hrodd, hAcard, hAL⟩
  refine ⟨A, hAL, hAcard, ?_⟩
  rw [← CFSG.LocalAnalysis.UniquenessCase.PartTwo.inU_iff_mem_uniqueSet]
  refine CFSG.LocalAnalysis.UniquenessCase.UC6.inU_of_normalizer_le_of_fusion
    (CFSG.RankThreeCoreUniqueness.Helpers.maxTwoLocal_self_normalizing D.M D.maxLocal)
    hAM hN ?_
  intro g hAg
  let B : Subgroup G := CFSG.Open.uniqueFourConj g A
  have hBM : B ≤ D.M := hAg
  have hBcard : Nat.card B = r := by
    have hmap : B = A.map (MulAut.conj g⁻¹).toMonoidHom := rfl
    rw [hmap, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hAcard]
  have hBgroup : IsPGroup r B :=
    IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hBcard)
  haveI : Fact (Nat.Prime r) := ⟨hr⟩
  obtain ⟨P, hP, hBP⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.exists_isSylowOf_ge (K := D.M) hBM hBgroup
  have hrankEq : CFSG.Open.pRank r P = CFSG.Open.pRank r D.M :=
    CFSG.LocalAnalysis.RankFourTheoremC.pRank_eq_of_isSylowOf hr hP
  obtain ⟨E0, hE0X, hE0el, hE0card⟩ :=
    exists_elemAbelian_sq_of_mem_calC_ne hLX' hL'X' (Ne.symm hneLL')
      hAL hAcard hr hrodd hsimple hnonab hL2L' hrdvd
  have hE0M : E0 ≤ D.M := hE0X.trans hXM
  have h2rankM : 2 ≤ CFSG.Open.pRank r D.M := by
    refine CFSG.SectionRank.le_pRank hr.one_lt hE0M hE0el ?_
    rw [hE0card]
  have h2rankP : 2 ≤ CFSG.Open.pRank r P := hrankEq ▸ h2rankM
  obtain ⟨E, hBE, hEP, hEel, hEcard⟩ :=
    CFSG.GroupTheory.exists_isElemAbelian_card_sq_of_le_of_card_prime
      hP.isPGroup h2rankP hBP hBcard
  have hPX : P ≤ X := by
    rw [hmX]
    exact CFSG.le_pElementSubgroup_of_isPGroup hr hP.isPGroup hP.le
  have hEX : E ≤ X := hEP.trans hPX
  have hEunique := hmE E hEX hEel hEcard
  have hEcent : E ≤ Subgroup.centralizer (B : Set G) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hEel.comm he (hBE hb)).symm
  have hEconj : E ≤ CFSG.Open.uniqueFourConj g D.M := by
    intro e he
    rw [CFSG.LocalAnalysis.UniquenessCase.UC6.mem_uniqueFourConj_iff]
    have hcommA : ∀ a ∈ A, (g * e * g⁻¹) * a = a * (g * e * g⁻¹) := by
      intro a ha
      have hbB : g⁻¹ * a * g ∈ B :=
        Subgroup.mem_map.mpr ⟨a, ha, by simp [MulAut.conj_apply]⟩
      have hcomm := Subgroup.mem_centralizer_iff.mp (hEcent he) (g⁻¹ * a * g) hbB
      calc (g * e * g⁻¹) * a = g * (e * (g⁻¹ * a * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * a * g) * e) * g⁻¹ := by rw [hcomm]
        _ = a * (g * e * g⁻¹) := by group
    have hcentA : g * e * g⁻¹ ∈ Subgroup.centralizer (A : Set G) :=
      Subgroup.mem_centralizer_iff.mpr (fun a ha => (hcommA a ha).symm)
    exact hN (Subgroup.centralizer_le_normalizer (A : Set G) hcentA)
  have hginvM : g⁻¹ ∈ D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22r_mem_of_conj_le_of_unique D hEunique
      (g := g⁻¹) (by
        intro y hy
        have := CFSG.LocalAnalysis.UniquenessCase.UC6.mem_uniqueFourConj_iff.mp (hEconj hy)
        simpa using this)
  exact ⟨g, by simpa using D.M.inv_mem hginvM, rfl⟩

theorem exists_D3_of_self {D : Data G} (h8107 : F08.R8107 D) {p : ℕ} {L : Subgroup G}
    (hL : L ∈ calC D.M) (hHinf : Hinf D.M = Lp D p) {m : ℕ} (hm : P17_64_2 D p m)
    (hpow : IsPowTwo m) (hL2m : IsL2 (Bar2 L) m) :
    ∃ D₃ : Subgroup G, D₃ ≤ L ∧ Nat.card D₃ = 3 ∧
      D₃ ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M := by
  classical
  have hLrank : CFSG.Open.pRank 3 L = 1 := pRank_three_eq_one_of_isL2 hL2m
  have hLthin : F08.Thin8 L := thin8_of_isL2 hL2m
  obtain ⟨KA, KB, hKA, hKB, hKA2, hKBshape, hneAB⟩ :=
    exists_two_calC_of_p1642 hm hHinf
  have hm2 : 2 ≤ m := uc22p20g_two_le_of_isL2 hKA2
  have hsecond : ∃ K : Subgroup G, K ∈ calC D.M ∧ K ≠ L ∧
      (IsL2 (Bar2 K) m ∨ IsU3 (Bar2 K) m) ∧ CFSG.Open.pRank 3 K = 1 := by
    by_cases hKAL : KA = L
    · have hKBne : KB ≠ L := by
        intro hKBL
        exact hneAB (by rw [hKAL, hKBL])
      refine ⟨KB, hKB, hKBne, hKBshape, ?_⟩
      rcases hKBshape with hKB2 | hKBU3
      · exact pRank_three_eq_one_of_isL2 hKB2
      · exact pRank_three_eq_one_of_isU3FourPow hKBU3 hpow hm2
    · exact ⟨KA, hKA, hKAL, Or.inl hKA2, pRank_three_eq_one_of_isL2 hKA2⟩
  obtain ⟨K, hKmem, hKne, hKshape, hKrank⟩ := hsecond
  obtain ⟨D₃, hD₃L, -, hD₃card⟩ :=
    CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) L
  rw [hLrank, pow_one] at hD₃card
  obtain ⟨A₂, hA₂K, -, hA₂card⟩ :=
    CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) K
  rw [hKrank, pow_one] at hA₂card
  have hKshape8 : F08.Thin8 K ∨ ∃ n : ℕ, IsU3 (Bar2 K) n := by
    rcases hKshape with hL2K | hU3K
    · exact Or.inl (thin8_of_isL2 hL2K)
    · exact Or.inr ⟨m, hU3K⟩
  exact ⟨D₃, hD₃L, hD₃card,
    (h8107 L hL K hKmem (Ne.symm hKne) hLrank hKrank (Or.inl hLthin) hKshape8
      D₃ A₂ hD₃L hD₃card hA₂K hA₂card).1⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
