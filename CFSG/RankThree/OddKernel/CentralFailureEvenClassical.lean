module

public import CFSG.RankThree.OddKernel.CentralFailureComponents

public section

namespace CFSG.RankThree.OddKernel

open Subgroup CFSG.SectionRank CFSG.LocalCores CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (localRank)

variable {p : ℕ}

theorem original_central_failure_excludes_even_classical_components {G : Type} [Group G]
    [Finite G] (hK : IsKGroupCat G) (he : CFSG.twoLocalOddRank G ≤ 3)
    (hr : ∀ r : ℕ, r.Prime → 3 < r → localRank r G ≤ 2) (H : Subgroup G) (N₀ : Subgroup H)
    [N₀.Normal] (hS : CFSG.layer (H ⧸ N₀) = ⊤) (hp : p.Prime) (hp3 : 3 < p)
    (hfail : 2 < localRank p (H ⧸ N₀) ∨ (pRank p G ≤ 3 ∧ pRank p G < pRank p (H ⧸ N₀)))
    (X : Subgroup H) (hXS : X.map (QuotientGroup.mk' N₀) = ⊤)
    (hXmin : ∀ U : Subgroup H, U.map (QuotientGroup.mk' N₀) = ⊤ → Nat.card X ≤ Nat.card U) :
    let ρX : X →* H ⧸ N₀ := (QuotientGroup.mk' N₀).comp X.subtype
    let C₀ : Subgroup X := (center (H ⧸ N₀)).comap ρX
    let D₀ : Subgroup X := sylowPrimeComplement p C₀
    ∃ _ : D₀.Normal, ∃ _ : (D₀.map ρX).Normal, ∃ _ : (C₀.map (QuotientGroup.mk' D₀)).Normal,
    ∃ f : X ⧸ D₀ →* (H ⧸ N₀) ⧸ D₀.map ρX,
      (∀ x : X, f (QuotientGroup.mk x) = QuotientGroup.mk (ρX x)) ∧ Function.Surjective f ∧
      f.ker = (N₀.subgroupOf X ⊔ D₀).map (QuotientGroup.mk' D₀) ∧ f.ker ≠ ⊥ ∧
      f.ker ≤ C₀.map (QuotientGroup.mk' D₀) ∧
      C₀.map (QuotientGroup.mk' D₀) = center (X ⧸ D₀) ∧ CFSG.layer (X ⧸ D₀) = ⊤ ∧
      (∀ K : Subgroup (X ⧸ D₀), CFSG.IsComponent K →
        ∀ t ∈ ({.PSL, .PSU, .PSp, .POmegaOdd, .POmegaPlus, .POmegaMinus} : Set StatedLieTag),
        ∀ n a : ℕ, ¬ StatedClassicalModel (K ⧸ center K) t n 2 a) ∧
      ((CFSG.IsQuasisimple (X ⧸ D₀) ∧ Nat.card (ComponentIndex (X ⧸ D₀)) = 1) ∨
        (Nat.card (ComponentIndex (X ⧸ D₀)) = 2 ∧
          ∃ K₁ K₂ : Subgroup (X ⧸ D₀), CFSG.IsComponent K₁ ∧ CFSG.IsComponent K₂ ∧ K₁ ≠ K₂ ∧
            (∀ K : Subgroup (X ⧸ D₀), CFSG.IsComponent K → K = K₁ ∨ K = K₂) ∧
            IsCyclic (center (X ⧸ D₀)) ∧ center K₁ ≠ ⊥ ∧ IsCyclic (center K₁) ∧
            center K₂ ≠ ⊥ ∧ IsCyclic (center K₂) ∧
            K₁ ⊓ K₂ = (center K₁).map K₁.subtype ⊓ (center K₂).map K₂.subtype ∧
            K₁ ⊓ K₂ ≠ ⊥ ∧ pRank p K₁ = 2 ∧ pRank p K₂ = 2 ∧ localRank p K₁ = 1 ∧
            localRank p K₂ = 1 ∧ K₁ ⊔ K₂ = ⊤ ∧
            center (X ⧸ D₀) = (center K₁).map K₁.subtype ⊔ (center K₂).map K₂.subtype ∧
            ∃ μ : K₁ × K₂ →* X ⧸ D₀, (∀ x : K₁ × K₂, μ x = (x.1 : X ⧸ D₀) * x.2) ∧
              Function.Surjective μ ∧
              ∀ x : K₁ × K₂, μ x = 1 ↔
                ∃ z ∈ K₁ ⊓ K₂, (x.1 : X ⧸ D₀) = z ∧ (x.2 : X ⧸ D₀) = z⁻¹)) := by
  intro ρX C₀ D₀
  obtain ⟨hDn, hZ₀n, hPn, f, hf, hfs, hfker, hA, -, hAP, hPZ, hEY, hmod, hcomp⟩ :=
    original_central_failure_components hK he hr H N₀ hS hp hp3 hfail X hXS hXmin
  refine ⟨hDn, hZ₀n, hPn, f, hf, hfs, hfker, hA, hAP, hPZ, hEY, ?_, hmod⟩
  intro K hKc t ht n a hM
  obtain ⟨hZ, hZp, hloc⟩ := hcomp K hKc
  exact hZ (CentralLift.even_classical_small_local_rank_quasisimple_prime_center_trivial
      hp hp3 hKc.1 hZp hloc ht hM)

end CFSG.RankThree.OddKernel
