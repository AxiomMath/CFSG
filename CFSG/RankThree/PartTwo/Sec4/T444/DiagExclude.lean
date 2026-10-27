module

public import CFSG.RankThree.PartTwo.Sec4.Item426RestInner
public import CFSG.RankThree.PartTwo.Sec4.T444.DiagSetting

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)

section Certs

theorem ys03_I06_not_G2_J3 {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {s : G} {L J : Subgroup G}
    (h : DiagSetting G A M H s L) (hJ : J ∈ thetaComponents 3 G)
    (hsec : HasSection (J.map (starQuot G) ⧸ Subgroup.center (J.map (starQuot G))) (projSL 3 (GaloisField 2 2))) :
    ¬ (Blueprint.ChevalleyExceptionalModel (J.map (starQuot G) ⧸ Subgroup.center (J.map (starQuot G))) .G2 3 1 ∨
       Nonempty (J.map (starQuot G) ⧸ Subgroup.center (J.map (starQuot G)) ≃* Blueprint.NativeSporadic.J3)) := by
  have hdvd : 20160 ∣ Nat.card (J.map (starQuot G) ⧸ Subgroup.center (J.map (starQuot G))) := by
    have h1 := CFSG.RankThree.PartTwo.KFacts.L34.hasSection_card_dvd hsec
    rwa [CFSG.RankThree.PartTwo.KFacts.L34.card_projSL] at h1
  rintro (hG2 | hJ3e)
  ·
    have h2 := dvd_trans hdvd (CFSG.RankThree.PartTwo.Sec4.Item426Rest.card_dvd_of_G2_three hG2)
    norm_num at h2
  ·
    obtain ⟨e⟩ := hJ3e
    have hJ3 : Nat.card (J.map (starQuot G) ⧸ Subgroup.center (J.map (starQuot G))) = 50232960 := by
      rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.J3.card_J3]
    rw [hJ3] at hdvd
    norm_num at hdvd

end Certs

end CFSG.RankThree.PartTwo.Sec4

end
