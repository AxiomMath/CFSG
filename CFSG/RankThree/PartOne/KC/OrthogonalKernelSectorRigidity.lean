module

public import CFSG.RankThree.PartOne.KC.OrthogonalBlockProduct
public import CFSG.RankThree.PartOne.KC.OrthogonalKernelSectorRigidityRep

public section

namespace CFSG.RankThree.PartOne

open Polynomial Module QuadraticMap CFSG.Assembly CFSG.RankThree.Classical
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal
open scoped IsMulCommutative

theorem orthogonal_primary_special_groups_kernel_sector_scalar_rigidity
    {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Nontrivial V] (Q : QuadraticForm K V) (hQ : (polarBilin Q).Nondegenerate)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpl : p ≠ ringChar K)
    (A : Subgroup (ProjOrthDerived Q)) (hA : IsElemAbelian p A) (hAc : Nat.card A = p ^ 2)
    (Ã : Subgroup (orthDerived Q))
    (hÃ : Ã ≤ A.comap (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) ∧
      ∀ P : Sylow p (A.comap (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))),
        (P : Subgroup (A.comap (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))))).map
          (A.comap (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))).subtype = Ã)
    (σ : K ≃+* K) (F : V ≃+ V) (hFσ : ∀ (c : K) (v : V), F (c • v) = σ c • F v)
    (μ : K) (_hμ : μ ≠ 0) (hFQ : ∀ v, Q (F v) = μ * σ (Q v))
    (κ : ProjOrthDerived Q ≃* ProjOrthDerived Q)
    (hκF : ∀ g g' : ↥(orthDerived Q),
      (∀ v, (g' : V ≃ₗ[K] V) v = F ((g : V ≃ₗ[K] V) (F.symm v))) →
        κ (QuotientGroup.mk g) = QuotientGroup.mk g')
    (hscal : ∀ M : Subgroup Ã, Nat.card M = p → lineSpace M ≠ ⊥ →
      ∃ c : Kˣ, ∀ v ∈ lineFixSpace M, F v = (c : K) • v)
    (hcent : ∀ x : orthDerived Q, x ∈ Ã → x ≠ 1 →
      ∀ h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap, h ≠ X - 1 →
        2 ≤ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h →
          ∀ j ∈ componentImage Q (x : V ≃ₗ[K] V) h, κ j = j) :
    σ = RingEquiv.refl K ∧ (∃ c : Kˣ, ∀ v, F v = (c : K) • v) ∧ κ = 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hD := kernelLineData Q hQ hp (by omega) hpl A hA hAc Ã hÃ
  refine orthogonal_primary_special_groups_kernel_sector_scalar_rigidity_of_orbit_representatives
    Q hQ hp hp3 hpl A hA hAc Ã hÃ σ F hFσ μ _hμ hFQ κ hκF hscal fun x hx hx1 => ?_
  have hxp : x ^ p = 1 := by simpa using congrArg Subtype.val (hD.exp ⟨x, hx⟩)
  obtain ⟨Rep, hRep⟩ := (oddOrderIsometry_of_orthDerived hp hpl hQ x
    (orderOf_eq_prime hxp hx1)).exists_orbitRepresentatives
  exact ⟨Rep, hRep, fun h hh h1 hm j hj => hcent x hx hx1 h (hRep.1 hh) h1 hm j hj⟩

end CFSG.RankThree.PartOne
