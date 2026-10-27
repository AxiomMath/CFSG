module

public import CFSG.LocalAnalysis.StandardType.GGInnerD4RegimeDefs
public import CFSG.LocalAnalysis.StandardType.GGInnerD4TagExc
public import CFSG.LocalAnalysis.StandardType.GGInnerD4TagBC
public import CFSG.LocalAnalysis.StandardType.GGInnerD4TagA

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ltrd4s_cover (lab : LargeEvenLabel)
    (h : ¬ (lab.tag = .E6 ∨ lab.tag = .twE6)) :
    ((lab.tag = .A ∧ ¬ (3 ∣ lab.rank + 1 ∧ 3 ∣ 2 ^ lab.n - 1)) ∨
        (lab.tag = .twA ∧ ¬ (3 ∣ lab.rank + 1 ∧ 3 ∣ 2 ^ lab.n + 1))) ∨
      ((lab.tag = .A ∧ 3 ∣ lab.rank + 1 ∧ 3 ∣ 2 ^ lab.n - 1) ∨
        (lab.tag = .twA ∧ 3 ∣ lab.rank + 1 ∧ 3 ∣ 2 ^ lab.n + 1)) ∨
      (lab.tag = .B ∨ lab.tag = .C) ∨
      ((lab.tag = .D ∨ lab.tag = .twD) ∧ lab.rank ≤ 3) ∨
      ((lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank) ∨
      lab.tag = .F4 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨
      (lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4 ∨
        lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der) := by
  rcases lab with ⟨t, r, n⟩
  cases t <;> simp_all <;> (first | omega | tauto)

theorem ggInnerOnD4_of_regimes
    (hB : GGK0ExcB) (hRA : GGInnerOnD4RA) (hD : GGInnerOnD4DGen)
    (hS : GGInnerOnD4Small) : GGInnerOnD4 := by
  rw [ggInnerOnD4_iff]
  refine GGInnerOnD4On.mono ltrd4s_cover ?_
  exact GGInnerOnD4On.union ggInnerOnD4_tagAGen
    (GGInnerOnD4On.union hRA
      (GGInnerOnD4On.union ggInnerOnD4_tagBC
        (GGInnerOnD4On.union ggInnerOnD4_tagDLow
          (GGInnerOnD4On.union hD
            (GGInnerOnD4On.union (ggInnerOnD4_tagF4 hB)
              (GGInnerOnD4On.union (ggInnerOnD4_tagE7 hB)
                (GGInnerOnD4On.union (ggInnerOnD4_tagE8 hB) hS)))))))

end CFSG.StandardType

end
