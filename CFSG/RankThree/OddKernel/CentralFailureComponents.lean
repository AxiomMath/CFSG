module

public import CFSG.RankThree.OddKernel.FailureExclusion
public import CFSG.RankThree.OddKernel.CentralCoverComponentModels

public section

namespace CFSG.RankThree.OddKernel

open Subgroup CFSG.SectionRank CFSG.LocalCores
open CFSG.Assembly.RankThreeEven (localRank)

variable {p : ℕ}

theorem original_central_failure_components {G : Type} [Group G] [Finite G]
    (hK : IsKGroupCat G) (he : CFSG.twoLocalOddRank G ≤ 3)
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
                ∃ z ∈ K₁ ⊓ K₂, (x.1 : X ⧸ D₀) = z ∧ (x.2 : X ⧸ D₀) = z⁻¹)) ∧
      ∀ K : Subgroup (X ⧸ D₀), CFSG.IsComponent K →
        center K ≠ ⊥ ∧ IsPGroup p (center K) ∧ localRank p K ≤ 2 := by
  intro ρX C₀ D₀
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨_i₁, _i₂, _i₃, -, -, -, -, -, -, -, hPZ, hEY, -⟩ :=
    stationary_original_noncentral_odd_kernel_failure_exclusion hK he hr H N₀ hS hp hp3 hfail X
      hXS hXmin
  obtain ⟨-, -, -, -, -, -, -, hDn, hZ₀n, -, -, -, hPn, f, hf, hfs, hfker, hA, hAP, -, -, hP1,
    hPp, -, -, -, -, -, -, -, -, -, -, -, hlY, hlX2, -, -, h1, h2, -, -⟩ :=
    stationary_source_four_one_odd_prime_kernel_failure_reduction hK he hr H N₀ hS hp hp3 hfail X
      hXS hXmin
  have hY2 : localRank p (X ⧸ D₀) ≤ 2 := hlY ▸ hlX2
  have hZY : center (X ⧸ D₀) ≠ ⊥ := hPZ ▸ hP1
  have hZYp : IsPGroup p (center (X ⧸ D₀)) := hPZ ▸ hPp
  have hAZ : f.ker ≤ center (X ⧸ D₀) := hPZ ▸ hAP
  have e := QuotientGroup.quotientKerEquivOfSurjective f hfs
  have hlq : localRank p ((X ⧸ D₀) ⧸ f.ker) = localRank p ((H ⧸ N₀) ⧸ D₀.map ρX) :=
    CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e hp
  have hpq : pRank p ((X ⧸ D₀) ⧸ f.ker) = pRank p ((H ⧸ N₀) ⧸ D₀.map ρX) := by
    rw [pRank_eq_open_pRank_top, pRank_eq_open_pRank_top]
    exact pRank_top_eq_of_mulEquiv hp.one_lt e
  have hfail' : 2 < localRank p ((X ⧸ D₀) ⧸ f.ker) ∨
      (pRank p (X ⧸ D₀) ≤ 3 ∧ pRank p (X ⧸ D₀) < pRank p ((X ⧸ D₀) ⧸ f.ker)) := by
    rcases hfail with h | ⟨h3, h4⟩
    · exact .inl (hlq ▸ (h1 h).1)
    · obtain ⟨-, hY3, hS3⟩ := h2 h3 h4
      exact .inr ⟨hY3.le, by rw [hpq, hY3]; exact hS3⟩
  have hmod := stationary_central_prime_cover_failure_component_models hp hp3 hEY hZY hZYp hY2
    f.ker hA hAZ hfail'
  refine ⟨hDn, hZ₀n, hPn, f, hf, hfs, hfker, hA, hPp.to_le hAP, hAP, hPZ, hEY, hmod,
    fun K hKc => ⟨?_, isPGroup_center_component hEY hZYp hKc,
      (CFSG.RankThree.PartTwo.localRank_subgroup_le hp K).trans hY2⟩⟩
  rcases hmod with ⟨hq, hcard⟩ | ⟨-, K₁, K₂, -, -, -, hall, -, hZ₁, -, hZ₂, -⟩
  · have htop : CFSG.IsComponent (⊤ : Subgroup (X ⧸ D₀)) :=
      ⟨isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hq, Subgroup.IsSubnormal.top⟩
    have : Subsingleton (ComponentIndex (X ⧸ D₀)) :=
      (Nat.card_eq_one_iff_unique.mp hcard).1
    have hKtop : K = ⊤ := congrArg Subtype.val
      (Subsingleton.elim (⟨K, hKc⟩ : ComponentIndex (X ⧸ D₀)) ⟨⊤, htop⟩)
    subst hKtop
    intro hbot
    apply hZY
    rw [← Subgroup.map_center_eq (Subgroup.topEquiv : (⊤ : Subgroup (X ⧸ D₀)) ≃* X ⧸ D₀), hbot,
      Subgroup.map_bot]
  · rcases hall K hKc with rfl | rfl
    · exact hZ₁
    · exact hZ₂

end CFSG.RankThree.OddKernel
