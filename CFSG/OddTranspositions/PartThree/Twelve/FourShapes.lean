module

public import CFSG.OddTranspositions.PartThree.Twelve.FourSp
public import CFSG.OddTranspositions.PartThree.Twelve.FourU
public import CFSG.OddTranspositions.PartThree.Twelve.FourOrth
public import CFSG.OddTranspositions.PartThree.Twelve.One
import CFSG.OddTranspositions.PartFour.Fourteen.RootBlockFive
import CFSG.RankThree.GF2n.Tim79aSec2

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.OddTranspositions.PartFour CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {G : Type} [Group G] [Finite G] {D : Set G}

section Certs


theorem twelveFour (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hH : TwelveOneShape hC) :
    hC.alpha = {hC.d} ∧
      ((∃ s ∈ imageClass hC, ∃ m f : ℕ, 4 ≤ m ∧ 2 ≤ f ∧
          (IsSymplecticTransvection
              (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) m f s ∨
            IsUnitaryTransvection
              (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) m f s)) ∨
        ∃ (k : ℕ) (ε π : Bool), 4 ≤ k ∧ PartThree.IsFiveReflectionModel k ε π (imageClass hC)) := by
  rcases hH with ⟨s, hs, m, f, hm, hf, hSp | hU | ⟨hm6, hO⟩⟩ | ⟨k, ε, π, hk, h5⟩
  · exact ⟨alpha_eq_singleton_of_isSymplecticTransvection hC hMZ hs hm hf hSp,
      Or.inl ⟨s, hs, m, f, hm, hf, Or.inl hSp⟩⟩
  · exact ⟨alpha_eq_singleton_of_isUnitaryTransvection hC hMZ hs hm hf hU,
      Or.inl ⟨s, hs, m, f, hm, hf, Or.inr hU⟩⟩
  · exact (false_of_isOrthReflection hC hMZ hs hm6 hf hO).elim
  · have hcls := imageClass_isClass hC
    obtain ⟨s, hs⟩ := imageClass_nonempty hC
    obtain ⟨hb1, hne⟩ := subset_rootBlock_and_ne_of_isFiveReflectionModel hcls hk h5 hs
    exact ⟨alpha_eq_singleton_of_rootBlock_eq_singleton hC hMZ hs hb1 hne
      (rootBlock_eq_singleton_of_isFiveReflectionModel hcls hk h5 hs), Or.inr ⟨k, ε, π, hk, h5⟩⟩

end Certs

end CFSG.OddTranspositions.PartThree
