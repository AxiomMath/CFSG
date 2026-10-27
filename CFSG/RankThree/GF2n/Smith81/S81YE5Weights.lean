module

public import CFSG.RankThree.GF2n.Smith81.S81E7Basic
public import CFSG.RankThree.GF2n.Smith81.S81YGenDef

public section

namespace CFSG.RankThree.GF2n.Smith81.RootGenE5

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.RankThree.GF2n.Smith81
  CFSG.RankThree.GF2n.Smith81.E7Model CFSG.RankThree.GF2n.Smith81.RootGen


theorem isRoot_root126 (k : Fin 126) : IsRoot .E7 ((Tag.rootCertificate .E7).root k) := by
  have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
  exact RootCertificate.isRoot_root (Tag.rootCertificate_check .E7) k (by omega)

theorem w2_check : ∀ k : Fin 126, (Tag.rootCertificate .E7).root k ≠ -theta →
    ∃ γ : Fin e7Data.d, pr γ theta = 1 ∧ pr γ ((Tag.rootCertificate .E7).root k) ≠ -1 := by
  decide +kernel

theorem exists_pr_ne {δ : Fin (Tag.rank .E7) → ℤ} (hδ : IsRoot .E7 δ) (hne : δ ≠ -theta) :
    ∃ γ : Fin e7Data.d, pr γ theta = 1 ∧ pr γ δ ≠ -1 := by
  have h := (forall_isRoot_iff fun x => x ≠ -theta →
    ∃ γ : Fin e7Data.d, pr γ theta = 1 ∧ pr γ x ≠ -1).2 w2_check
  exact h δ hδ hne

theorem w3_check : ∀ μ : Fin e7Data.d, pr μ theta = 1 → ∀ γ : Fin e7Data.d, pr γ theta = 1 →
    μ = γ ∨
    (∃ k : Fin 126, (Tag.rootCertificate .E7).root k node1 = 0 ∧
      pr μ ((Tag.rootCertificate .E7).root k) = -1 ∧
      e7Data.wt γ = e7Data.wt μ + MinData.toWeight ((Tag.rootCertificate .E7).root k)) ∨
    (∃ ν : Fin e7Data.d, pr ν theta = 1 ∧
      ∃ k₁ : Fin 126, (Tag.rootCertificate .E7).root k₁ node1 = 0 ∧
        pr μ ((Tag.rootCertificate .E7).root k₁) = -1 ∧
        e7Data.wt ν = e7Data.wt μ + MinData.toWeight ((Tag.rootCertificate .E7).root k₁) ∧
        ∃ k₂ : Fin 126, (Tag.rootCertificate .E7).root k₂ node1 = 0 ∧
          pr ν ((Tag.rootCertificate .E7).root k₂) = -1 ∧
          e7Data.wt γ = e7Data.wt ν + MinData.toWeight ((Tag.rootCertificate .E7).root k₂)) := by
  decide +kernel

theorem exists_two_steps {μ γ : Fin e7Data.d} (hμ : pr μ theta = 1) (hγ : pr γ theta = 1) :
    μ = γ ∨
    (∃ β, β ∈ Perp ∧ pr μ β = -1 ∧ shift β μ = γ) ∨
    (∃ β₁ β₂ ν, β₁ ∈ Perp ∧ pr μ β₁ = -1 ∧ shift β₁ μ = ν ∧
      β₂ ∈ Perp ∧ pr ν β₂ = -1 ∧ shift β₂ ν = γ) := by
  rcases w3_check μ hμ γ hγ with h | ⟨k, hk, hpr, hwt⟩ |
    ⟨ν, _, k₁, hk₁, hpr₁, hwt₁, k₂, hk₂, hpr₂, hwt₂⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨(Tag.rootCertificate .E7).root k,
      perp_iff.2 ⟨isRoot_root126 k, hk⟩, hpr, shift_eq hwt⟩)
  · exact Or.inr (Or.inr ⟨(Tag.rootCertificate .E7).root k₁, (Tag.rootCertificate .E7).root k₂, ν,
      perp_iff.2 ⟨isRoot_root126 k₁, hk₁⟩, hpr₁, shift_eq hwt₁,
      perp_iff.2 ⟨isRoot_root126 k₂, hk₂⟩, hpr₂, shift_eq hwt₂⟩)

end CFSG.RankThree.GF2n.Smith81.RootGenE5
