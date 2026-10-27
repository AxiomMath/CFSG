module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148TIdX
import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSL3Ident
import CFSG.RankThree.PartTwo.Sec14.Ronan148TOddGlue
import CFSG.RankThree.PartTwo.Sec14.Ronan148TCenterFree

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open CFSG CFSG.GH74.GLS CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec13

theorem l3IdentHeis_of (hθ : ThetaHeis148) (hS : SimpleHeis148) : L3IdentHeis := by
  intro X _ _ P K₀ Q D hH hL hZ hns hPe hP9 hb hQ hh hK hperf hq
  have hinv := Ronan148B.inv_of_hyp hZ hh
  have hθ' := hθ X P K₀ hH hP9 hZ hinv hperf hq
  have hKq' : IsQuasisimple K₀ := CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hθ').trans QuotientGroup.quotientBot) hq
  obtain ⟨p, e, hp, he, hiso⟩ := hL
  have hZK : Subgroup.center K₀ = ⊥ :=
    center_eq_bot_of_isoLThreePi he hiso hKq' (isPGroup_center_of_theta_eq_bot hθ')
  have : IsSimpleGroup (K₀ ⧸ Subgroup.center K₀) := hKq'.2.1
  haveI hKs : IsSimpleGroup K₀ := MulEquiv.isSimpleGroup
    ((QuotientGroup.quotientMulEquivOfEq hZK).trans QuotientGroup.quotientBot).symm
  have hnonab : ∃ a b : K₀, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hKq'.2.2
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
        exact ⟨a, b, fun h => hab (by rw [← QuotientGroup.mk_mul, h, QuotientGroup.mk_mul])⟩
  exact hS X P K₀ Q D hH ⟨p, e, hp, he, hiso⟩ hZ hns hPe hP9 hb hQ hh hK hKs hnonab

theorem kf148SigGenL3Ident_of_heis (hI : L3IdentHeis) : Ronan148B.KF148SigGenL3Ident := by
  intro Γ _ _ A L b hA hbA hb1 hLb hAL hsec _ _ hL _ hpt hsol K₀ Q D hQ hh hK hperf hq _
  obtain ⟨hPe, hP9⟩ := Ronan148B.autThetaQuot_e9 hA hbA hb1 hAL hsec
  exact hI _ _ K₀ Q D (xHeis148 Γ A L b hA hbA hb1 hLb hAL hsec hL hpt hsol) hL
    (Ronan148B.isPerfect_center_of_isLThreePi hL hsol).2 hsol hPe hP9 hpt.2.2.2.2 hQ hh hK
    hperf hq

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
