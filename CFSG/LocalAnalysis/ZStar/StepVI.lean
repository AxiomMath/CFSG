module

public import CFSG.LocalAnalysis.ZStar.TwoAdicWedderburn
public import CFSG.LocalAnalysis.ZStar.WedderburnCharacters
public import CFSG.LocalAnalysis.ZStar.AbstractStepV

public section

namespace CFSG

namespace ZStar.StepVI

open ZStar.TransferReduction
open ZStar.CentralizerInduction
open ZStar.AbstractStepV
open ZStar.CharacterContradiction
open ZStar.PadicBlockField
open ZStar.TwoAdicWedderburn
open ZStar.WedderburnCharacters

noncomputable section

universe u

variable {X : Type u} [Group X] [Fintype X]

theorem component_character_eq_neg_degree_or_zStar
    {t sigma : X}
    (ht : Isolated t) (ht2 : t * t = 1)
    (hmin : ∀ H : Subgroup X, H.Normal → t ∈ H → H = ⊤)
    (ih :
      ∀ {Y : Type u} [Group Y] [Fintype Y] {y : Y},
        Nat.card Y < Nat.card X → Isolated y → y * y = 1 →
          ZStarConclusion Y y)
    (hsigma1 : sigma ≠ 1) (hsigma2 : sigma * sigma = 1)
    (htsigma : Commute t sigma)
    (htsigma_not_conj : ¬ IsConj t sigma)
    (D : Decomposition X) (i : Fin D.blockCount)
    (hstable : CentralizerOddCoreStable
      (componentCharacter D.equiv i))
    (hcharsigma : componentCharacter D.equiv i sigma ≠ 0)
    (hchart : componentCharacter D.equiv i t ≠
      (D.blockSize i : TwoAdicComplex)) :
    ZStarConclusion X t ∨
      componentCharacter D.equiv i t =
        -(D.blockSize i : TwoAdicComplex) := by
  let tau : X := t * sigma
  have htau2 : tau * tau = 1 := by
    dsimp only [tau]
    calc
      (t * sigma) * (t * sigma) = t * (sigma * t) * sigma := by group
      _ = t * (t * sigma) * sigma := by rw [← htsigma.eq]
      _ = (t * t) * (sigma * sigma) := by group
      _ = 1 := by rw [ht2, hsigma2, one_mul]
  have httau : Commute t tau := by
    dsimp only [tau]
    exact (Commute.refl t).mul_right htsigma
  have htau_not_conj : ¬ IsConj t tau := by
    intro hconj
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    have hgtcomm : Commute (g * t * g⁻¹) t := by
      rw [hg]
      exact httau.symm
    have hgt : g * t * g⁻¹ = t := ht g hgtcomm.eq
    have htau_eq : tau = t := hg.symm.trans hgt
    apply hsigma1
    apply mul_left_cancel (a := t)
    simpa only [tau, mul_one] using htau_eq
  rcases abstract_stepV ht ht2 hmin ih hsigma2 htsigma
      htsigma_not_conj (componentCharacter D.equiv i)
      (fun h ↦ componentCharacter_eq_of_isConj D.equiv i h) hstable with
    hZ | hconst
  · exact Or.inl hZ
  rcases abstract_stepV ht ht2 hmin ih htau2 httau htau_not_conj
      (componentCharacter D.equiv i)
      (fun h ↦ componentCharacter_eq_of_isConj D.equiv i h) hstable with
    hZ | hconstTau
  · exact Or.inl hZ
  right
  have hfirst :=
    componentCharacter_mul_eq_degree_mul_of_product_constancy
      D.equiv i t sigma hconst
  have hsecondRaw :=
    componentCharacter_mul_eq_degree_mul_of_product_constancy
      D.equiv i t tau hconstTau
  have htTau : t * tau = sigma := by
    dsimp only [tau]
    rw [← mul_assoc, ht2, one_mul]
  have hsecond :
      componentCharacter D.equiv i t *
          componentCharacter D.equiv i (t * sigma) =
        (D.blockSize i : TwoAdicComplex) *
          componentCharacter D.equiv i sigma := by
    simpa only [tau, htTau] using hsecondRaw
  exact character_value_eq_neg_degree
    (by
      let : NeZero (D.blockSize i) := D.blockSize_neZero i
      exact_mod_cast (NeZero.ne (D.blockSize i)))
    hfirst hsecond hcharsigma hchart

end

end ZStar.StepVI

end CFSG
