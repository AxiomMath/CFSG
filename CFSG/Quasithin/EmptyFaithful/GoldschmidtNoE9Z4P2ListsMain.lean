module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2ListsXi
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2ListsSp
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2ListsCases
public import CFSG.Quasithin.Background.C2A3Orbits

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedClassicalModel StatedSL StatedLieTag
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.E9P2L
open CFSG.Quasithin.EmptyFaithfulMultiple


theorem input14614ListsE9_of_prop134
    (h35 : Lemma1435)
    (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hD36 : D36) (hD37 : D37) (hD321 : D321)
    (hI5 : Insp5a) (hD310 : D310) (hD391 : D391) (hI4 : Insp4)
    (h134E9 : EmptyFaithfulMultiple.Prop134E9He) : Input14614ListsE9 := by
  intro G _ _ T M S H PQ p hred _hmax hshape hne
  classical
  have hshape' := hshape
  obtain rfl : p = 3 := hshape.1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3 : A3Orbits G := a3Orbits_of_a37_a38 hA37 hA38
  have hTMc : T ≤ mcOf T := S.isHTM_mcOf.1.1
  have hsylMc : IsSylowTwoOf T (mcOf T) := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTMc
  have hKMc : oTwoUpper H ≤ mcOf T := (oTwoUpper_le H).trans (S.le_mcOf hred.isHTM)
  have hX : IsXi T (oTwoUpper H) := isXi_oTwoUpper h35 S hred hshape'
  have hi : (pCoreOf 2 (oTwoUpper H)).relIndex (oTwoUpper H) = 3 ^ 2 :=
    relIndex_pCoreOf_oTwoUpper h35 S hred hshape'
  have hpX : 3 ∣ Nat.card (oTwoUpper H) := by
    rw [card_eq_card_pCoreOf_mul_relIndex, hi]
    exact Dvd.dvd.mul_left (dvd_pow_self 3 two_ne_zero) _
  obtain ⟨P, hP, -⟩ := exists_isSylowIn_ge 3 (bot_le : ⊥ ≤ oTwoUpper H) IsPGroup.of_bot
  have hPc : Nat.card P = 3 ^ 2 := by rw [hX.card_sylow (by norm_num) hpX hP, hi]
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hPc
    norm_num at hPc
  have hPMc : pCoreOf 2 (mcOf T) ≠ ⊥ := S.isHTM_mcOf.1.2
  have := S.hyp.simple
  have hsq : CFSG.SectionRank.IsSQTKCat ↥(mcOf T) :=
    (qtkeCore_of_cat S.hyp.nonabelian S.hyp.qtke).1 (mcOf T) hPMc
  rcases h134E9 G (mcOf T) T (oTwoUpper H) P hsq hPMc hsylMc hKMc hX (by simpa using hi) hP.le
    hP.isPGroup (by simpa using hPc) with hN | ⟨L, hL, hq, hXL, hcases⟩
  · exact absurd (le_antisymm (conjClosure_le fun g hg k hk =>
      (Subgroup.mem_normalizer_iff.mp (hN hg) k).mp hk) (le_conjClosure _ _)) hne
  rcases hcases with ⟨⟨t, htSN, htL, hPeq, -⟩, htype⟩ | ⟨hTL, htype⟩ | ⟨hTL, ⟨n, hn, hmod⟩, -⟩ |
      ⟨hTL, htype⟩ | ⟨hMcL, hHe⟩
  ·
    have hnL : ¬ T ≤ Subgroup.normalizer (L : Set G) := fun hTL => htL (hTL htSN.1)
    have hPL : P ⊓ L ≠ ⊥ := S146zX.inf_ne_bot_of_eq_sup hPeq hPne
    have htype' : (∃ n : ℕ, 3 ∣ 2 ^ n - 1 ∧
          StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) StatedLieTag.PSL 2 2 n) ∨
        ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
          StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) StatedLieTag.PSL 2 q 1 := by
      rcases htype with ⟨n, hn, hm⟩ | hq'
      · exact Or.inl ⟨n, S146zX.three_dvd_two_pow_sub_one' hn, hm⟩
      · exact Or.inr hq'
    obtain ⟨s, hsT, hsN, hKc, hres⟩ := S146zX.pair_case hA37 hA38 hD36 hD37 hD321 hI5 hA3 S
      (p := 3) (Or.inl rfl) hL hq hXL hP.le hP.isPGroup hnL hPL htype'
    rcases hres with hI | ⟨hp5, -, -⟩
    · exact ⟨L, hL, Or.inl ⟨s, hsT, hsN, hKc, hI.elim Or.inl fun h => Or.inr h.2⟩⟩
    · omega
  ·
    exfalso
    obtain ⟨hMcL, hKL⟩ := invariant_data hA3 S hL hXL hTL
    have hcenter : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := by
      rcases htype with h | h
      · exact facts15420_centerPSL _ 3 3 1 h
      · exact facts15420_centerSL33M11 _ (Or.inl h)
    exact false_of_l33 h35 S hred hshape' hL (S146zX.conjClosure_eq_of_invariant' (by norm_num)
      hL hMcL hKL hq hcenter hP.le hP.isPGroup hPne) htype
  ·
    obtain ⟨hMcL, hKL⟩ := invariant_data hA3 S hL hXL hTL
    have hKc : conjClosure (oTwoUpper H) (mcOf T) = L :=
      S146zX.conjClosure_eq_of_invariant' (by norm_num) hL hMcL hKL hq
        (center_eq_bot_of_sp4_model hmod) hP.le hP.isPGroup hPne
    obtain ⟨e⟩ := nonempty_mulEquiv_symplectic_of_model hmod
    refine ⟨L, hL, Or.inr ⟨hKc, Or.inl ⟨n, ?_, hn, ⟨(Der6D.oTwoQuotEquiv L).trans e⟩⟩⟩⟩
    have h1 := one_le_of_sp4_model hmod
    obtain ⟨k, rfl⟩ := hn
    omega
  ·
    exfalso
    obtain ⟨hMcL, hKL⟩ := invariant_data hA3 S hL hXL hTL
    rcases htype with h | h | h
    · have hcenter := facts15420_centerSL33M11 _ (Or.inr h)
      exact false_of_m11 h35 S hred hshape' hL (S146zX.conjClosure_eq_of_invariant'
        (by norm_num) hL hMcL hKL hq hcenter hP.le hP.isPGroup hPne) h
    · have hcenter := facts15420_centerPSL _ 4 2 1 h
      exact false_of_sl_binary h35 S hred hshape' hL (S146zX.conjClosure_eq_of_invariant'
        (by norm_num) hL hMcL hKL hq hcenter hP.le hP.isPGroup hPne) (Or.inl rfl)
        (S146zX.nonempty_mulEquiv_sl_zmod_two h)
    · have hcenter := facts15420_centerPSL _ 5 2 1 h
      exact false_of_sl_binary h35 S hred hshape' hL (S146zX.conjClosure_eq_of_invariant'
        (by norm_num) hL hMcL hKL hq hcenter hP.le hP.isPGroup hPne) (Or.inr rfl)
        (S146zX.nonempty_mulEquiv_sl_zmod_two h)
  ·
    exfalso
    obtain ⟨eHe⟩ := hHe
    have hTL : T ≤ Subgroup.normalizer (L : Set G) := fun g hg => hMcL (hsylMc.1 hg)
    have hcenter : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := facts15420_centerHe _ ⟨eHe⟩
    have hs := S146zX.isSimpleGroup_kbar_of_isQuasisimple hq hcenter
    have h4 := S146zX.fourList_of_invariant hA37 hA38 hD310 hD391 hI4 S hL hs hTL
    exact S146zX.not_fourList_of_he ⟨(kbarEquiv L).trans eHe⟩ h4

end CFSG.Quasithin
