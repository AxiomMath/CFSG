module

public import CFSG.RankThree.OddKernel.FailureReduction
public import CFSG.RankThree.OddKernel.CompleteRankComparison

public section

namespace CFSG.RankThree.OddKernel

open Subgroup CFSG.SectionRank
open CFSG.Assembly.RankThreeEven (localRank)

variable {p : ℕ}

theorem stationary_original_noncentral_odd_kernel_failure_exclusion {G : Type} [Group G]
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
      IsPGroup p f.ker ∧ f.ker ≤ C₀.map (QuotientGroup.mk' D₀) ∧
      C₀.map (QuotientGroup.mk' D₀) = center (X ⧸ D₀) ∧ CFSG.layer (X ⧸ D₀) = ⊤ ∧
      ⁅(⊤ : Subgroup (X ⧸ D₀)), C₀.map (QuotientGroup.mk' D₀)⁆ = ⊥ := by
  intro ρX C₀ D₀
  have : Fact p.Prime := ⟨hp⟩
  have h6 := stationary_source_four_one_odd_prime_kernel_failure_reduction hK he hr H N₀ hS hp
    hp3 hfail X hXS hXmin
  obtain ⟨-, -, -, -, -, -, -, hDn, hZ₀n, -, -, -, hPn, f, hf, hfs, hfker, hA, hAP, hYp, -, hP1,
    hPp, -, hZp, -, hpre, ⟨e, -⟩, hZq, hLq, -, hnoP, -, -, hlY, hlX2, -, -, h1, h2, hcen,
    -⟩ := h6
  have hAp : IsPGroup p f.ker := hPp.to_le hAP
  have hPZ : C₀.map (QuotientGroup.mk' D₀) ≤ center (X ⧸ D₀) := by
    by_contra hnot
    have hSp : Group.IsPerfect (H ⧸ N₀) :=
      Group.IsPerfect.top_iff.mp (hS ▸ CFSG.LocalCores.layer_isPerfect)
    have hZYP : center ((X ⧸ D₀) ⧸ C₀.map (QuotientGroup.mk' D₀)) = ⊥ := by
      rw [← map_center_eq e.symm, hZq, Subgroup.map_bot]
    have hLYP : CFSG.layer ((X ⧸ D₀) ⧸ C₀.map (QuotientGroup.mk' D₀)) = ⊤ :=
      CFSG.LocalCores.layer_eq_top_of_surjective hLq e.symm.toMonoidHom e.symm.surjective
    have hYP : ⁅(⊤ : Subgroup (X ⧸ D₀)), C₀.map (QuotientGroup.mk' D₀)⁆ ≠ ⊥ := by
      intro h
      apply hnot
      rw [commutator_comm, commutator_eq_bot_iff_le_centralizer, coe_top,
        centralizer_univ] at h
      exact h
    have h5 := noncentral_odd_prime_kernel_complete_rank_comparison hp3
      (C₀.map (QuotientGroup.mk' D₀)) hPp hP1 hLYP hZYP hYP (hlY ▸ hlX2) f hfs hAP hZp hpre hnoP
    rcases hfail with hf1 | ⟨hf1, hf2⟩
    · have := (h1 hf1).1
      omega
    · obtain ⟨-, hY3, hS₀3⟩ := h2 hf1 hf2
      have := h5.2 hY3.le
      omega
  obtain ⟨hPeq, hLY, -⟩ := hcen hPZ
  refine ⟨hDn, hZ₀n, hPn, f, hf, hfs, hfker, hA, hAp, hAP, hPeq, hLY, ?_⟩
  rw [commutator_comm]
  exact commutator_eq_bot_iff_le_centralizer.2 (by rw [coe_top, centralizer_univ]; exact hPZ)

end CFSG.RankThree.OddKernel
