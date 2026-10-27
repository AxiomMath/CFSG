module

public import CFSG.RankThree.PartOne.KC.OrthogonalNaturalCommonLine

public section

namespace CFSG.RankThree.PartOne

open Polynomial Module QuadraticMap CFSG CFSG.RankThree.Classical2 CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.ClassicalGroups.Orthogonal

@[expose] def KernelSectorScalarRigidity {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (p : ℕ) (Ã : Subgroup (orthDerived Q)) (σ : K ≃+* K) (F : V ≃+ V)
    (κ : MulAut (ProjOrthDerived Q)) : Prop :=
  (∀ M : Subgroup Ã, Nat.card M = p → lineSpace M ≠ ⊥ →
    ∃ c : Kˣ, ∀ v ∈ lineFixSpace M, F v = (c : K) • v) →
  (∀ x : orthDerived Q, x ∈ Ã → x ≠ 1 → ∀ h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap,
    h ≠ X - 1 → 2 ≤ primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h →
      ∀ j ∈ componentImage Q (x : V ≃ₗ[K] V) h, κ j = j) →
  σ = RingEquiv.refl K ∧ (∃ c : Kˣ, ∀ v, F v = (c : K) • v) ∧ κ = 1

theorem orthogonal_natural_common_centralizer_of_kernel_sector_rigidity
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
      κ * (d : MulAut (ProjOrthDerived Q)) = (d : MulAut (ProjOrthDerived Q)) * κ)
    (hrig : KernelSectorScalarRigidity Q p Ã σ F κ) :
    σ = RingEquiv.refl K ∧ (∃ c : Kˣ, ∀ v, F v = (c : K) • v) ∧ κ = 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hV3 : 3 ≤ finrank K V := by
    obtain ⟨U, hU3, -⟩ := hT
    exact hU3 ▸ Submodule.finrank_le U
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨hpow, hinj1, hker⟩ := natural_lift_facts hQ hp hp3 hpl A hA hAc Ã hÃ
  have hÃA : ∀ x ∈ Ã, (QuotientGroup.mk x : ProjOrthDerived Q) ∈ A := fun x hx => hÃ.1 hx
  refine hrig (fun M hM hact => ?_) (fun x hxÃ hx1 h hh hne hm j hj => ?_)
  · exact natural_line_scalar hQ hT hp hp3 hpl D hD A hA hAc Ã hÃA hpow hinj1 σ F hFσ μ _hμ hFQ
      κ hκF hcent M hM (hker M hM) (hdim M hM hact) (fun h3 => hq3 h3 M hM hact)
      (fun h23 => hsplit h23 M hM hact)
  · have hxord : orderOf x = p := orderOf_eq_prime (hpow x hxÃ) hx1
    have hxne : (QuotientGroup.mk x : ProjOrthDerived Q) ≠ 1 := fun h => hx1 (hinj1 x hxÃ h)
    exact natural_primary_component_fixed hQ hT hp hp3 hpl D hD A hA hAc x hxord (hÃA x hxÃ) hxne
      κ (hcent _ (hÃA x hxÃ) hxne) h hh hne hm j hj

end CFSG.RankThree.PartOne
