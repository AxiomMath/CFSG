module

public import CFSG.RankThree.OddKernel.CentralFailureAllClassical
public import CFSG.RankThree.LocalRank.AlternatingCentralExtension

public section

namespace CFSG.RankThree.OddKernel

open Subgroup CFSG.SectionRank CFSG.LocalCores CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (localRank)

variable {p : ℕ}

theorem original_central_failure_excludes_alternating_components {G : Type} [Group G]
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
        (∀ n : ℕ, 5 ≤ n → ¬ Nonempty (K ⧸ center K ≃* alternatingGroup (Fin n))) ∧
        (CFSG.Blueprint.ExceptionalRep (K ⧸ center K) ∨
          CFSG.Blueprint.NativeSporadic.SporadicRep (K ⧸ center K))) ∧
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
  obtain ⟨_i₁, _i₂, _i₃, -, -, -, -, -, -, -, -, hCl, -⟩ :=
    original_central_failure_excludes_all_classical_components hK he hr H N₀ hS hp hp3 hfail X
      hXS hXmin
  have hKY : IsKGroupCat (X ⧸ D₀) := ((hK.subgroup H).subgroup X).quotient D₀
  refine ⟨hDn, hZ₀n, hPn, f, hf, hfs, hfker, hA, hAP, hPZ, hEY, fun K hKc => ?_, hmod⟩
  obtain ⟨hZ, hZp, -⟩ := hcomp K hKc
  have : Group.IsPerfect K := hKc.1.1
  have : IsSimpleGroup (K ⧸ center K) := hKc.1.2.1
  have halt : ∀ n : ℕ, 5 ≤ n → ¬ Nonempty (K ⧸ center K ≃* alternatingGroup (Fin n)) := by
    rintro n hn ⟨e⟩
    let η : K →* alternatingGroup (Fin n) := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    have hη : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hker : η.ker = center K := by
      ext k
      simp only [η, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    apply hZ
    rw [← hker]
    exact LocalRank.perfect_central_prime_extension_alternating_ker_eq_bot η hn hp hp3 hη
      hker.le (hker ▸ hZp)
  refine ⟨halt, ?_⟩
  have hcat : CFSG.Blueprint.Catalog (K ⧸ center K) :=
    catalog_of_isKGroupCat_of_surjective hKY K (QuotientGroup.mk' (center K))
      (QuotientGroup.mk'_surjective _)
  rcases hcat with ⟨q, -, ⟨e⟩⟩ | ⟨n, hn, he'⟩ | ⟨t, n, ℓ, a, hM⟩ | h | h
  · exfalso
    obtain ⟨u, v, huv⟩ := hKc.1.2.2
    apply huv
    apply e.injective
    rw [map_mul, map_mul, mul_comm]
  · exact absurd he' (halt n hn)
  · exact absurd hM (hCl K hKc ℓ hM.1.1 t
      (CFSG.Milestones.statedClassicalModel_tag_mem _ t n ℓ a hM) n a)
  · exact .inl h
  · exact .inr h

end CFSG.RankThree.OddKernel
