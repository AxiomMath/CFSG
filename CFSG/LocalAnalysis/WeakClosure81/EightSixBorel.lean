module

public import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelOne
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitDefs
import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelData
import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelFrattini
import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelRoot
import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelRootSmall
import CFSG.LocalAnalysis.WeakClosure81.EightFiveU3Aut

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G]


theorem w3Borel86T' (hConf : SpURootConfiguration) : W3Borel86T' G := by
  intro V H T hV7 hH hH0 hT hKT _ hi hδ
  have h : Hyp83 V H T := Hyp83.of_hyp7 hV7 hH hH0 hT
  rcases hi with hC | hN
  · exact not_shape86DeltaT'_of_centralizersInM hConf h hKT hC hδ
  · obtain ⟨S, _, ψ, ρ, t₀, hD⟩ := exists_borel86Data h hKT hδ
    exact hD.false_of_normalizersInMTwo hN

theorem w3Borel86'_of_split (hConf : SpURootConfiguration)
    (h711 : ∀ H : Subgroup G, W3Lem711Alt ↥H) (g4 : W3Lem85TwoGap4) (g6 : W3Lem85TwoGap6) :
    W3Borel86' G := by
  intro V H T hV7 hH hH0 hT hKT hW hi hδ
  have h : Hyp83 V H T := Hyp83.of_hyp7 hV7 hH hH0 hT
  refine w3Borel86T' hConf V H T hV7 hH hH0 hT hKT hW hi ?_
  obtain ⟨m, n, hm2, hn, hr, hsh⟩ := hδ
  rcases Nat.lt_or_ge 3 m with hm | hm
  · exact shape86DeltaT'_of_shape86Delta h711 w3Lem85TwoGap1_holds g4 g6 h hKT
      ⟨m, n, hm, hn, hr, hsh⟩
  · exact shape86DeltaT'_of_small h hKT hn hr hm2 hm hsh

theorem w3Borel86_of_split (hConf : SpURootConfiguration)
    (h711 : ∀ H : Subgroup G, W3Lem711Alt ↥H) (g4 : W3Lem85TwoGap4) (g6 : W3Lem85TwoGap6) :
    W3Borel86 G :=
  fun V H T hV7 hH hH0 hT hKT hW hi ⟨m, n, hm, hn, hr, hsh⟩ =>
    w3Borel86'_of_split hConf h711 g4 g6 V H T hV7 hH hH0 hT hKT hW hi
      ⟨m, n, by omega, hn, hr, hsh⟩

end CFSG.LocalAnalysis.WeakClosure81

end
