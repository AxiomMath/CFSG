module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KDiagOmega8mCore
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KDiagOmega8mTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KDiagAssembly

public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

theorem kDiag_of_isOmega8m {n : ℕ} {X : Type} [Group X] [Finite X] (hX : IsOmega8m X n) :
    ∀ (θ : MulAut X), Odd (orderOf θ) →
      ∀ S : Sylow 2 X, (∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) →
      ∀ P : Subgroup X, IsParabolicTwo X P →
        (S : Subgroup X) ≤ Subgroup.normalizer (P : Set X) → ∀ x ∈ P, θ x ∈ P :=
  kDiag_of_isOmega8m_of_tail
    (fun {K : Type} [Field K] [Finite K] [CharP K 2] (b c : K)
      (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) =>
      kDiag_omegaTail (K := K) (b := b) (c := c) hirr)
    hX

theorem kDiag_holds :
    KDiag :=
  kDiag_of_omega8m fun {n : ℕ} {X : Type} [Group X] [Finite X] (hX : IsOmega8m X n)
    θ hodd S hSθ P hP hSP x hx =>
    kDiag_of_isOmega8m hX θ hodd S hSθ P hP hSP x hx

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
