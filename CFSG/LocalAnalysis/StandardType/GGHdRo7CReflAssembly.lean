module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CReflSteps

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem c2_refl_of_steps (hS : C2SuppTwoLeaf) (hN : C2ReflNormLeaf) (hC : C2ReflCoefLeaf)
    (hSg : C2ReflSignLeaf) (hTr : C2ReflTrickLeaf) (hAr : C2ReflArithLeaf) (hFl : C2TableFlipLeaf)
    (hSm : C2TableSmallLeaf) : C2ReflLeaf := by
  intro p _ hp n hn V _ _ b A hP hStab hNoT r hrA hr
  by_cases hfix : r (b 0) = b 0
  · exact Or.inl (hStab r hrA hfix)
  · obtain ⟨u, φ, hnf⟩ := hN p hp n hn V b A hP hStab hNoT r hrA hr hfix
    obtain ⟨c, hc⟩ := hC hS p hp n hn V b A hP hStab r u φ hnf
    by_cases h : c = 0 ∨ ∀ i, i ≠ 0 → b.coord i u = 0
    · exact Or.inr (Or.inl (hSg p hp n hn V b A hP hNoT r u φ hnf c hc h))
    · have h' : c ≠ 0 ∧ ∃ i, i ≠ 0 ∧ b.coord i u ≠ 0 := by
        constructor
        · exact fun h0 => h (Or.inl h0)
        · by_contra hcon
          exact h (Or.inr fun i hi => by
            by_contra hne
            exact hcon ⟨i, hi, hne⟩)
      have hk := hAr p hp n hn V b A r u φ hnf c hc
      by_cases hflip : (c = 1 ∧ 5 ≤ (Finset.univ.filter fun i => i ≠ 0 ∧ b.coord i u ≠ 0).card) ∨
          (c = -1 ∧ 4 ≤ (Finset.univ.filter fun i => i ≠ 0 ∧ b.coord i u ≠ 0).card)
      · exact (hFl hTr hS p hp n hn V b A hP hStab r u φ hnf c hc hk hflip).elim
      · exact Or.inr (Or.inr (hSm hTr hS p hp n hn V b A hP hStab r u φ hnf c hc h'.1 h'.2 hk hflip))

end CFSG.StandardType.HdRo7C
