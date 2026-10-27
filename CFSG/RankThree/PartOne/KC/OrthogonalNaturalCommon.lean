module

public import CFSG.RankThree.PartOne.KC.OrthogonalNaturalCommonRigid
public import CFSG.RankThree.PartOne.KC.OrthogonalKernelSectorRigidity

public section

namespace CFSG.RankThree.PartOne

open Polynomial Module QuadraticMap CFSG CFSG.RankThree.Classical2 CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.ClassicalGroups.Orthogonal

theorem orthogonal_natural_common_centralizer_with_nonexceptional_fixed_sectors
    {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpl : p ≠ ringChar K)
    (D : Subgroup (MulAut (ProjOrthDerived Q)))
    (hD : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ D)
    (A : Subgroup (ProjOrthDerived Q)) (hA : Assembly.IsElemAbelian p A)
    (hAc : Nat.card A = p ^ 2) (Ã : Subgroup (orthDerived Q))
    (hÃ : Ã ≤ A.comap (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) ∧
      ∀ P : Sylow p (A.comap (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))),
        (P : Subgroup (A.comap (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))))).map
          (A.comap (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))).subtype =
            Ã)
    (hdim : ∀ M : Subgroup Ã, Nat.card M = p → lineSpace M ≠ ⊥ → 3 ≤ finrank K (lineFixSpace M))
    (hq3 : Nat.card K = 3 → ∀ M : Subgroup Ã, Nat.card M = p → lineSpace M ≠ ⊥ →
      finrank K (lineFixSpace M) ≠ 3)
    (hsplit : (Nat.card K = 2 ∨ Nat.card K = 3) → ∀ M : Subgroup Ã, Nat.card M = p →
      lineSpace M ≠ ⊥ → ¬ (finrank K (lineFixSpace M) = 4 ∧
        ∃ S : Submodule K (lineFixSpace M), finrank K S = 2 ∧
          ∀ s ∈ S, (Q.comp (lineFixSpace M).subtype) s = 0))
    (σ : K ≃+* K) (F : V ≃+ V) (hFσ : ∀ (c : K) (v : V), F (c • v) = σ c • F v) (μ : K)
    (_hμ : μ ≠ 0) (hFQ : ∀ v, Q (F v) = μ * σ (Q v)) (κ : MulAut (ProjOrthDerived Q))
    (hκF : ∀ g g' : ↥(orthDerived Q),
      (∀ v, (g' : V ≃ₗ[K] V) v = F ((g : V ≃ₗ[K] V) (F.symm v))) →
      κ (QuotientGroup.mk g) = QuotientGroup.mk g')
    (hcent : ∀ a ∈ A, a ≠ 1 → ∀ d ∈ CFSG.layer ↥(D ⊓ Subgroup.centralizer
        ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))),
      κ * (d : MulAut (ProjOrthDerived Q)) = (d : MulAut (ProjOrthDerived Q)) * κ) :
    σ = RingEquiv.refl K ∧ (∃ c : Kˣ, ∀ v, F v = (c : K) • v) ∧ κ = 1 := by
  have hV3 : 3 ≤ finrank K V := by
    obtain ⟨U, hU3, -⟩ := hT
    exact hU3 ▸ Submodule.finrank_le U
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  exact orthogonal_natural_common_centralizer_of_kernel_sector_rigidity Q hQ hT hp hp3 hpl D hD A
    hA hAc Ã hÃ hdim hq3 hsplit σ F hFσ μ _hμ hFQ κ hκF hcent
    (orthogonal_primary_special_groups_kernel_sector_scalar_rigidity Q hQ hp hp3 hpl A hA hAc Ã hÃ
      σ F hFσ μ _hμ hFQ κ hκF)

end CFSG.RankThree.PartOne
