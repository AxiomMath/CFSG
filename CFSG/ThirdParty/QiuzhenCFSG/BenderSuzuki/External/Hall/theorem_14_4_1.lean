module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Hall.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Hall.lemma_14_4_5

namespace CFSG
end CFSG
open CFSG

/-!
# Hall Theorem 14.4.1

Source interface for P. Hall's transfer theorem in Hall §14.4.
-/

namespace CFSG.BenderSuzuki
namespace External

universe u


/-- Hall Theorem 14.4.1 with Hall-Wielandt's weak-closure choice: the fixed
elements used in every Engel generator all lie in Q. -/
public theorem hall_theorem_14_4_1_p_hall_of_weakly_closed
    {G : Type u} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (P₁ : Sylow p G) (Q N₁ H₁ G₀ H P : Subgroup G)
    (hN₁ : N₁ = Subgroup.normalizer ((P₁ : Subgroup G) : Set G))
    (hN₁_le_H₁ : N₁ ≤ H₁)
    (hH₁ : H₁ = Subgroup.normalizer (Q : Set G))
    (hweak : WeaklyClosedIn (P₁ : Subgroup G) Q)
    (hG₀ : G₀ = hallPResidual p G)
    (hH : H = G₀ ⊓ H₁)
    (hP : P = G₀ ⊓ (P₁ : Subgroup G)) :
    (hallPResidual p H₁).map H₁.subtype = (hallPResidual p H).map H.subtype ∧
      ((hallPResidual p H).map H.subtype < H →
        ∃ Zs : Finset G,
          (∀ z : G, z ∈ Zs → z ∈ Q) ∧
            ∃ E : Set G,
              (∀ x : G, x ∈ E →
                ∃ u z c : G, u ∈ P ∧ z ∈ Zs ∧ c ∈ G₀ ∧ x ∈ H ∧
                  x = c * engelSymbol p u z * c⁻¹) ∧
              H ≤ hallTransferModulus p H H₁ ⊔ Subgroup.closure E) := by
  classical
  refine ⟨hallPResidual_map_inf_eq p H₁ G₀ H hG₀ hH, ?_⟩
  intro _
  let H₀ : Subgroup G := hallTransferModulus p H H₁
  have hdata :=
    hall_lemma_14_4_5_cycle_factor_engel_congruence_of_weakly_closed
      (G := G) p P₁ Q N₁ H₁ G₀ H P H₀ hN₁ hN₁_le_H₁
        hH₁ hweak hG₀ hH hP rfl
  simp only [hallCycleFactorDataIn] at hdata
  rcases hdata with
    ⟨Zs, cycleFactors, hZs, _hfactorization, hcongruent, hgenerated⟩
  let E : Set G :=
    {x : G | ∃ u z c : G, u ∈ P ∧ z ∈ Zs ∧ c ∈ G₀ ∧ x ∈ H ∧
      x = c * engelSymbol p u z * c⁻¹}
  refine ⟨Zs, hZs, ⟨E, ?_, ?_⟩⟩
  · intro x hx
    exact hx
  · refine le_trans hgenerated ?_
    refine sup_le le_sup_left ?_
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨u, hu, d, hd, rfl⟩
    obtain ⟨z, hzZs, w, hwG₀, hconjH, hdiv⟩ :=
      hcongruent u hu d hd
    let y : G := w * engelSymbol p (u : G) z * w⁻¹
    have hyE : y ∈ E := by
      exact ⟨(u : G), z, w, hu, hzZs, hwG₀, hconjH, rfl⟩
    have hdivSup : (d : G) / y ∈
        H₀ ⊔ Subgroup.closure E :=
      (show H₀ ≤ H₀ ⊔ Subgroup.closure E from le_sup_left) hdiv
    have hySup : y ∈ H₀ ⊔ Subgroup.closure E :=
      (show Subgroup.closure E ≤ H₀ ⊔ Subgroup.closure E from le_sup_right)
        (Subgroup.subset_closure hyE)
    have hmul := (H₀ ⊔ Subgroup.closure E).mul_mem hdivSup hySup
    simpa [y] using hmul
end External
end CFSG.BenderSuzuki

