module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeNbrCaseIIDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrTwE6RankDichotomy

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint TableB

theorem ggTwE6ThreeNbrRankInput_of_caseII (hII : GGTwE6ThreeNbrCaseII)
    (hE6r : GGTwE6LocalRankInput) (hcen : GGLabelCenterPCyclicInput) :
    GGTwE6ThreeNbrRankInput := by
  intro G _ _ p B Bs x L D J hcfg hp y K hnb hLab hN hsc
  subst hp
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨hK, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => GGTwE6BadLabel 3 lab)
    (P' := fun R _ I _ => IsSimpleGroup R → GGTwE6LocalRank R)
    (fun lab hlab hs => TwE6Delta.labelAll hs.1 fun K _ _ hK hsimple =>
      hE6r lab.n hlab.1 hs.2.2 K hK hsimple)
    (fun _ _ _ _ _ _ hP => hP.1) hLab
  obtain ⟨R, _, I, F, hs, hna, θ, ⟨hbad, -, hBsN, h3⟩, hlr⟩ := largeEvenRawDatum_exists hraw
  have hhas : GGHasLabel lab (K ⧸ Subgroup.center K) := by
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R' _ I' F' ⟨-, -, θ', -⟩
    exact ⟨θ'⟩
  have hcyc : ∀ E : Subgroup K, E ≤ Subgroup.center K → IsElemAbelian 3 E → Nat.card E ≤ 3 :=
    fun E hE hEa => hcen 3 Nat.prime_three (by norm_num) lab hlab K hK hhas E hE hEa
  rcases ggNbr_rank_dichotomy_twE6 hcfg hnb hK θ (hlr hs) hcyc hN with
    h5 | ⟨hBeq, hBs5, hm, h4, hC⟩
  · exact absurd h5 (not_le.mpr hlt)
  · exact hII G B Bs x L D J hcfg y K hnb hLab hN hsc hBeq hBs5 hm h4 hC

end CFSG.StandardType

end
