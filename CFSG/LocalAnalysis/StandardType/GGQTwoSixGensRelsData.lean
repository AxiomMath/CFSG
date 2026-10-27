module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSixGensRels
public import CFSG.LocalAnalysis.StandardType.GGQTwoSixGensData

public section

namespace CFSG.StandardType.QTwo.SixPoint

theorem qTwoSixRels_splitSupport :
    qTwoSixRelsSplitSupport qTwoSixData_inWindow qTwoSixData_support := by
  have h : relsP.all (fun w =>
      decide ((∃ s : Fin 3, qTwoSixRelsInWindow qTwoSixData_inWindow s w) ∨
        ∃ a b : Fin 18, Disjoint (qTwoSixData_support a) (qTwoSixData_support b) ∧
          (qTwoSixData_support a ∪ qTwoSixData_support b).card ≤ 5 ∧
            w = [(a, true), (b, true), (a, false), (b, false)])) = true := by
    decide +kernel
  intro w hw
  simpa using List.all_eq_true.1 h w hw

theorem qTwoSixRels_evalG_eq_one_data {X Y G : Type} [Group X] [Group Y] [Group G]
    (emb : Fin 3 → Y →* X) (hemb : ∀ s, Function.Injective (emb s))
    (native : Fin 18 → X) (hnative : ∀ w ∈ relsP, evalG native w = 1)
    (lift : Fin 3 → Fin 18 → Y)
    (hlift : ∀ s i, qTwoSixData_inWindow s i → emb s (lift s i) = native i)
    (g : Fin 18 → G) (φ : Fin 3 → Y →* G)
    (hφ : ∀ s i, qTwoSixData_inWindow s i → g i = φ s (lift s i))
    (hcomm : ∀ a b : Fin 18, Disjoint (qTwoSixData_support a) (qTwoSixData_support b) →
      (qTwoSixData_support a ∪ qTwoSixData_support b).card ≤ 5 → Commute (g a) (g b)) :
    ∀ w ∈ relsP, evalG g w = 1 :=
  qTwoSixRels_evalG_eq_one emb hemb native hnative qTwoSixData_inWindow
    qTwoSixData_support lift hlift g φ hφ qTwoSixRels_splitSupport hcomm

end CFSG.StandardType.QTwo.SixPoint

end
