module

public import CFSG.Quasithin.EmptyFaithful.SzSurvLocCases
public import CFSG.Quasithin.EmptyFaithful.S1421QNSMain
public import CFSG.Quasithin.EmptyFaithful.S1421QA5
public import CFSG.Quasithin.EmptyFaithful.S1421QA9
public import CFSG.Quasithin.EmptyFaithful.S1421QNSAct
public import CFSG.Quasithin.EmptyFaithful.S1421QNSComp
public import CFSG.Quasithin.EmptyFaithful.S1421QNSRad
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace SzSurvLoc

open S1421NS in
theorem lemma14216NoSltTLoc_of_shape_aut (hA5 : AutQ8D8Facts) (hA9 : AutExt9Facts)
    (G : Type) [Group G] [Finite G] (T M H K1 : Subgroup G)
    (st : Setting1427 T M H K1) (sh : Shape1428 T H K1)
    (hsurv : F112SurvivorLoc K1 (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1))
    (hQ : pCoreOf 2 (mcOf T) = pCoreOf 2 K1) (hlt : S1421.sOf T K1 < T) : False := by
  have hyp := st.hyp
  have hN := st.notation_
  have hTH : T ≤ H := st.hStar.1.1
  obtain ⟨t, htT, htn⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (K1 : Set G) := by
    by_contra hall
    push Not at hall
    exact hlt.ne (inf_eq_left.mpr hall)
  have hK1lt : K1 < oTwoUpper H := by
    rcases hN.index with ⟨-, hTn⟩ | ⟨hlt', -⟩
    · exact absurd (hTn htT) htn
    · exact hlt'
  have hHMc : H ≤ mcOf T := (hyp.isUniqueM_centralizer st.hStar.1 st.hStar.2.1).1.2
  have hKMc : oTwoUpper H ≤ mcOf T := (oTwoUpper_le H).trans hHMc
  have hTMc : T ≤ mcOf T := hyp.toQTFE14.t_le_mc
  have hMcO : pCoreOf 2 (mcOf T) ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal hyp.mc_max.1
  have hchar : CharTwo (mcOf T) := charTwo_of_inH' hyp.qtke hyp.sylow ⟨hTMc, hMcO⟩
  have hKN : oTwoUpper H ≤ Subgroup.normalizer (pCoreOf 2 K1 : Set G) := by
    rw [← hQ]
    exact hKMc.trans (le_normalizer_pCoreOf 2 (mcOf T))
  have hKC : oTwoUpper H ⊓ Subgroup.centralizer (pCoreOf 2 K1 : Set G) ≤ pCoreOf 2 K1 := by
    rw [← hQ]
    exact fun x hx => hchar ⟨hKMc hx.1, hx.2⟩
  have hQ2 : IsPGroup 2 (pCoreOf 2 K1) := pCoreOf_isPGroup 2 K1
  have hact : ∀ m : ℕ, Odd m → m ∣ Nat.card (oTwoUpper H) →
      m ∣ Nat.card (MulAut (pCoreOf 2 K1)) := fun m hm hmK =>
    dvd_natCard_mulAut_of_odd_dvd hQ2 hKN hKC hm hmK
  have hcardK1 : Nat.card (OTwoQuot K1) ∣ Nat.card K1 := Subgroup.card_quotient_dvd_card _
  have hcases := survivorLoc_cases_legacyBare st.notation_.cComp_mem inf_le_right hsurv
  rcases sh.cases with ⟨h1, -⟩ | ⟨hK1c, -⟩ | ⟨-, -, hL⟩
  · exact absurd h1 hK1lt.ne
  ·
    rcases hcases with ⟨hc, hs, hQ9⟩ | ⟨hc, hs, hQ8⟩
    · have hrad := solvRad_le_pCoreOf_of_simple hs (by rw [hc]; norm_num)
      have h7 : 7 ∣ Nat.card K1 := (by rw [hc] at hcardK1; omega : 7 ∣ Nat.card K1)
      have h49 := sq_dvd_card_of_conj_component hK1c (hTH htT) htn hN.le_K
        (le_normalizer_oTwoUpper H) hrad (m := 7) (by decide) h7
      have h49' := hact (7 ^ 2) (by decide) h49
      obtain ⟨E, hE⟩ := exists_subgroup_card_of_dvd (by norm_num : Nat.Prime 7) h49'
      exact (hA9 ↥(pCoreOf 2 K1) hQ9).2.2 ⟨E, by rw [hE]; norm_num⟩
    · have hrad := solvRad_le_pCoreOf_of_simple hs (by rw [hc]; norm_num)
      have h5 : 5 ∣ Nat.card K1 := (by rw [hc] at hcardK1; omega : 5 ∣ Nat.card K1)
      have h25 := sq_dvd_card_of_conj_component hK1c (hTH htT) htn hN.le_K
        (le_normalizer_oTwoUpper H) hrad (m := 5) (by decide) h5
      have h25' := hact (5 ^ 2) (by decide) h25
      obtain ⟨E, hE⟩ := exists_subgroup_card_of_dvd (by norm_num : Nat.Prime 5) h25'
      exact (hA5 ↥(pCoreOf 2 K1) hQ8).2.2 ⟨E, by rw [hE]; norm_num⟩
  ·
    obtain ⟨n, hn2, hn1, hnK⟩ := hL.exists_n
    have hcardX : Nat.card (OTwoQuot (oTwoUpper H)) ∣ Nat.card (oTwoUpper H) :=
      Subgroup.card_quotient_dvd_card _
    have key := dvd_card_of_isCentralL3Sp4 hnK
    rcases hcases with ⟨hc, -, hQ9⟩ | ⟨hc, -, hQ8⟩
    · have hn : n = 3 := eq_three_of_card_504 hn2 hn1 hc
      rcases key.2 hn with h | h
      · exact (hA9 ↥(pCoreOf 2 K1) hQ9).2.1 (hact _ (by decide) (h.trans hcardX))
      · exact (hA9 ↥(pCoreOf 2 K1) hQ9).1 (hact _ (by decide) (h.trans hcardX))
    · have hn : n = 2 := eq_two_of_card_sixty hn2 hn1 hc
      rcases key.1 hn with h | h
      · exact (hA5 ↥(pCoreOf 2 K1) hQ8).1 (hact _ (by decide) (h.trans hcardX))
      · exact (hA5 ↥(pCoreOf 2 K1) hQ8).2.1 (hact _ (by decide) (h.trans hcardX))

end SzSurvLoc

theorem lemma14216NoSltTLoc_holds :
    ∀ (G : Type) [Group G] [Finite G] (T M H K1 : Subgroup G), Setting1427 T M H K1 →
      pCoreOf 2 (yOfL22 T M) ≤ S1421.sOf T K1 →
      F112SurvivorLoc K1 (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1) →
      pCoreOf 2 (mcOf T) = pCoreOf 2 K1 → S1421.sOf T K1 < T → False :=
  fun G _ _ T M H K1 st _ hs hQ hlt =>
    SzSurvLoc.lemma14216NoSltTLoc_of_shape_aut autQ8D8Facts_holds autExt9Facts_holds G T M H K1 st
      st.shape hs hQ hlt

theorem lemma14216TailLoc_of_parts (hQ : Lemma14216QLoc) :
    Lemma14216TailLoc := by
  have hN := lemma14216NoSltTLoc_holds
  intro G _ _ T M H K1 st h13 hsurv
  have hQ' := hQ G T M H K1 st h13 hsurv
  refine ⟨?_, ?_, hQ'⟩ <;>
  · by_cases hS : S1421.sOf T K1 = T
    · rcases st.notation_.index with ⟨hK, -⟩ | ⟨-, hrel⟩
      · first | exact hK.symm | exact hS.symm
      · rw [hS, Subgroup.relIndex_self] at hrel
        omega
    · exact (hN G T M H K1 st h13 hsurv hQ' (lt_of_le_of_ne inf_le_left hS)).elim

end CFSG.Quasithin
