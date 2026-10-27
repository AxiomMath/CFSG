module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightK133
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKTens
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSum
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightMain

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem s16k_concl163_s1 (h : S16kBase D V₀ V L hV) (hGA : CFSG.Open.GriessAllModelsStatement)
    (hRI : S16kRowInputs) (hG2 : S16kG2IsU33)
    (hSchur : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hOut : S16kOmega8OutInner) :
    Concl163 D V₀ V hV L := by
  obtain ⟨t, -, -, -, htr, -, -, h133 | ⟨K, hK, g, hg, hne, hL, hcases⟩ | ⟨hcomp, hsum, htrans⟩ |
    ⟨hirr, -, hcomp, h135⟩⟩ := h.conc
  · exact s16k_concl163_of_133 h h133
  · exact s16k_concl163_of_tensor h hK hg hne hL hcases
  · exact s16k_concl163_of_sum h hGA hSchur hOut hcomp hsum htrans
  · exact s16k_concl163_of_irr h hGA hRI hG2 htr hirr hcomp h135

theorem s16k_r16_8_four (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (hSg : UC6S846.SigmaStd D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D)
    (h638 : UC6.R6_38 D) (h1110 : R1110Core D) (h164 : R16_4 D) (h165 : R16_5 D)
    (h63 : UC6.R6_3 D) (h126 : R126 D) (h1211 : R1211_1 D) (h111 : W3Thm111 G)
    (h6161ii : W3Lem616_1ii G) (h77 : F07.R77Eq D)
    (h1219 : ∀ V₀ V : Subgroup G, Hyp125 D V₀ V → D.sig = D.sig1) (h119 : F11.R119 D)
    (hGA : CFSG.Open.GriessAllModelsStatement) (hRI : S16kRowInputs) (hG2 : S16kG2IsU33)
    (hSchur : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hOut : S16kOmega8OutInner) :
    R16_8 D := by
  have h1217 : R1217 D := r1217_of_twelve_seventeen D hx h61 h127 h1214
  refine r16_8_four_holds D hx h4 hSg h61 h127 h1214 h638 h1110
    (fun V₀ V L hV hset hL hconc => ?_) h164 h165 h63 h126 h1211 h111 h6161ii h77 h1219
  exact s16k_concl163_s1 ⟨⟨hx, h4, hSg, h61, h127, h1214, h638, h1110, h164, h63, h126, h1211,
    h111, h6161ii, h77, h1219, h119⟩, hset, hL, hconc,
    s16f_s15_eq_one_of_four D hx h4 h61 h127 h1217 h164 hV hset hL hconc⟩ hGA hRI hG2 hSchur hOut

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
