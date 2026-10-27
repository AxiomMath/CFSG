module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFixHalfDelta
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3ZpAssembly
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3AssemblyP
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3AssemblyC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16b
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154AssemblyT

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_r16_4_hyp154_of_three (D : Data G) (S : s16h_Std D)
    (hr3 : CFSG.Open.evenRank G = 3) (hσG : SigmaThree D)
    (h1219 : ∀ V₀ V : Subgroup G, Hyp125 D V₀ V → D.sig = D.sig1) (hRows : K_FixHalfRows)
    (h880 : F08.R880 D) (h163c : R16_3FComp D) (hSchur : RSchur153) (hJP : K_JonesParshallH1)
    (h1217 : R1217 D) (hU2 : R8100U2 D) (h920L28 : s16h_e3_R920L28 D) :
    R16_4_hyp154 D := by
  intro V₀ V L hV h hc hs hnot
  obtain ⟨t, ht, ht2, ht1, htr, hW⟩ := hc
  have hσ : D.sig = D.sig1 := h1219 V₀ V h.hyp151.hyp125
  have hδ : s15 D.M V₀ V h.hyp151.isElemAbelian L = 2 →
      delta15 D.M V₀ V h.hyp151.isElemAbelian L <
        gamma15 D.M V₀ V h.hyp151.isElemAbelian L - 1 :=
    s16fh_delta_hyp_of_not_concl hRows D h1217 h163c h ⟨t, ht, ht2, ht1, htr, hW⟩ hnot
  rcases hW.2.2 with h133 | htens | hcomp3 | hcomp4
  · by_cases hp : (Nat.card ↥(lBar V₀ V hV L)).Prime
    · haveI : Fact (Nat.card ↥(lBar V₀ V hV L)).Prime := ⟨hp⟩
      exact s16h_hyp154_of_cyclic_e3 D S hr3 hσ hσG h ⟨t, ht, ht2, ht1, htr, hW⟩ hs hnot hδ hp
        ⟨isCyclic_of_prime_card rfl, rfl⟩
    · exact s16h_hyp154_of_pgroup_e3 D S hσ h hs hnot hδ ht ht2 ht1 htr hW h133 hp
  · obtain ⟨K, hK, g, hg, hne, hL, hT⟩ := htens
    exact s16h_hyp154_of_tensor D S hσ h hs hnot hδ ht ht2 ht1 htr hW hK hg hne hL hT
  · exact s16h_hyp154_of_component_e3 D S hr3 hσ h880 h163c hSchur hJP h1217 hU2 h920L28 h hs
      hnot hδ
      ht ht2 ht1 htr hW hcomp3.1
  · exact s16h_hyp154_of_component_e3 D S hr3 hσ h880 h163c hSchur hJP h1217 hU2 h920L28 h hs
      hnot hδ
      ht ht2 ht1 htr hW hcomp4.2.2.1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
