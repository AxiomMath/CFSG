module

public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofPairNL
public import CFSG.RankThree.PartTwo.Sec8.Item84KFacts4ProofSp4
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7ProofConj
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7ProofCent
import CFSG.RankThree.PartTwo.Sec8.Item812Res7ProofD4N
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofRee
import CFSG.RankThree.PartTwo.Sec21.LangTwisted2ProofD4

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item8KFacts3

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec8.Item83Proof CFSG.RankThree.PartTwo.Sec8.Item86ResProof
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)


theorem kBar_of_unitary {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} {a d : G} {n : ℕ} (h : Sec8Std G A c L a d n) {k : ℕ}
    (hU : IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) k) :
    Nonempty (imageModTheta L (inSubgroup perfectResidual
      (L ⊓ Subgroup.centralizer ({d} : Set G))) ≃* projSL 2 (GaloisField 2 (3 * n))) := by
  have hn1 : 1 ≤ n := h.data83.odd.pos
  rcases h.data83.cases with ⟨hDG, -, -⟩ | ⟨hRee, -, -⟩ | ⟨-, -, hK⟩ | ⟨-, -, hK⟩ | ⟨hSp, -, -⟩
  · exact (not_isUnitaryTwo_of_isList86 hn1
      (hDG.elim Or.inl fun hG => Or.inr (Or.inl hG)) k hU).elim
  · exact (not_isUnitaryTwo_of_profile (profile_of_isoReeF4 (by omega) hRee)
      (fun j hj => (CFSG.Timmesfeld.Orders.z2F4_le (by omega) hj).trans (by omega))
      (by omega) k hU).elim
  · exact hK
  · exact hK
  · exact (not_isUnitaryTwo_of_isList86 hn1 (Or.inr (Or.inr hSp)) k hU).elim

theorem pair84GammaUL_of (h45 : Sec4.Item4_5) (h418 : Item418Theta) (hL : Item82TwoList)
    (hC : Sec11.KS11Lie4Proof.G2ThreeConjSL2Minus) (hA : Sec11.KS11Lie4Proof.G2ThreeACentMinus)
    (hSp : KF84Sp4ThreeCent) : Pair84GammaUL := by
  intro G _ _ A c L a d n h b X hb hrel hLU hXU
  obtain ⟨k, hU⟩ := hLU
  have hK := kBar_of_unitary h hU
  have hR : KF84FieldReeStd := kF84FieldReeStd_holds
  have hO : KF84OuterL2 :=
    kF84OuterL2_of (inputs47ClassesD4_of_lang kF82D4LangCoset_holds kF82D4SecondCent_holds)
  have hF : KF84FieldStd := kF84FieldStd_of hO hR
  have hKB : KF83KBarTwo := kF83KBarTwo_of_even (kF83KBarEven_of hO hR)
  have hG2 : KF83IndepGTwo := kF83IndepGTwo_holds
  have hInd : KF83Indep := kF83Indep_of hG2
  have hn1 : 1 ≤ n := h.data83.odd.pos
  have hcN := le_normalizer_of_partner h45 h hb hrel h.mem_A
  have hc3 : c ^ 3 = 1 := h.mem_partTwoF.1.2 c h.mem_A
  obtain ⟨-, hck⟩ := kinds_of_partner h418 hF h hb hrel
  have hne := Item812Res7.ne_one_of_partner h hb hrel hcN
  obtain ⟨m, hm, hD | ⟨q, hq2, hqe, hG⟩ | hRee | hSpX⟩ :=
    nonUnitary_cases (isList82Two_of_partner hL h45 h418 hF hKB hInd hG2 h hb hrel) hXU
  ·
    obtain ⟨hm1, K, _, _, σ, hKc, hσ, ⟨E⟩⟩ := Item812Res7.exists_trialityD4_model hD
    obtain ⟨hk, eM⟩ := eq_of_residualShape h hb hrel hK (by omega)
      (d4_residualShape hcN hc3 hck hne hm1 hKc hσ E)
    have hmn : m = n := by omega
    subst hmn
    exact ⟨h.mem_A, h.ne_one, hn1, Or.inr ⟨Or.inl hD, eM⟩⟩
  ·
    obtain ⟨K, _, _, hKc, ⟨E⟩⟩ := Item8KFactsProof.isoGTwoEven_of_isoGTwo hq2 hqe hG
    have hm1 : 1 ≤ m := hm.pos
    obtain ⟨hk, eM⟩ := eq_of_residualShape h hb hrel hK (by omega)
      (g2_residualShape hC hA hcN hc3 hck hne (f := 3 * m) (by omega) hKc E)
    have hmn : m = n := by omega
    subst hmn
    exact ⟨h.mem_A, h.ne_one, hn1, Or.inr ⟨Or.inr (Or.inl ⟨q, hq2, hqe, hG⟩), eM⟩⟩
  ·
    exfalso
    obtain ⟨hq, hx⟩ := isQuasisimple_central_of_isoSUThree hm (ree_residual hcN hc3 hck hne hRee)
    exact false_of_residual_central h hb hrel hK hq hx
  ·
    obtain ⟨eSp⟩ := hSpX
    have hm1 : 1 ≤ m := hm.pos
    obtain ⟨hk, eM⟩ := eq_of_residualShape h hb hrel hK (by omega)
      (Or.inl (sp4_residual hSp hcN hc3 hck hne (f := 3 * m) (by omega) eSp))
    have hmn : m = n := by omega
    subst hmn
    exact ⟨h.mem_A, h.ne_one, hn1, Or.inr ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨eSp⟩))), eM⟩⟩

theorem pair84GammaUL_of' (h45 : Sec4.Item4_5) (h418 : Item418Theta) (hL : Item82TwoList) :
    Pair84GammaUL :=
  pair84GammaUL_of h45 h418 hL Sec11.KS11Lie7Proof.g2ThreeConjSL2Minus_holds
    Sec11.KS11Lie7Proof.g2ThreeACentMinus_holds Item84KFacts4.kF84Sp4ThreeCent_holds

end CFSG.RankThree.PartTwo.Sec8.Item8KFacts3
