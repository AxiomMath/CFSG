module

public import CFSG.RankThree.GF2n.Smith81.S81YE5Weights
public import CFSG.RankThree.GF2n.Smith81.S81D6Basic
public import CFSG.RankThree.GF2n.Smith81.S81YE5Def

public section

namespace CFSG.RankThree.GF2n.Smith81.RootGenE4

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.RankThree.GF2n.Smith81
  CFSG.RankThree.GF2n.Smith81.E7Model CFSG.RankThree.GF2n.Smith81.D6Spin
  CFSG.RankThree.GF2n.Smith81.RootGen CFSG.RankThree.GF2n.Smith81.RootGenE5


theorem w2_check4 : ∀ k : Fin 126, (Tag.rootCertificate .E7).root k node1 = 0 →
    (Tag.rootCertificate .E7).root k ≠ -theta4 →
    ∃ γ : Fin e7Data.d, pr γ theta = 0 ∧ pr γ theta4 = 1 ∧
      pr γ ((Tag.rootCertificate .E7).root k) ≠ -1 := by
  decide +kernel

theorem exists_pr_ne4 {δ : Fin (Tag.rank .E7) → ℤ} (hδ : δ ∈ Perp) (hne : δ ≠ -theta4) :
    ∃ γ : Fin e7Data.d, γ ∈ idx0 ∧ pr γ theta4 = 1 ∧ pr γ δ ≠ -1 := by
  have h := (forall_isRoot_iff fun x => x node1 = 0 → x ≠ -theta4 →
    ∃ γ : Fin e7Data.d, pr γ theta = 0 ∧ pr γ theta4 = 1 ∧ pr γ x ≠ -1).2 w2_check4
  obtain ⟨hr, h0⟩ := perp_iff.1 hδ
  obtain ⟨γ, g0, g1, g2⟩ := h δ hr h0 hne
  exact ⟨γ, mem_idx0.2 g0, g1, g2⟩

theorem w3_check4 : ∀ μ : Fin e7Data.d, pr μ theta = 0 → pr μ theta4 = 1 →
    ∀ γ : Fin e7Data.d, pr γ theta = 0 → pr γ theta4 = 1 →
    μ = γ ∨
    (∃ k : Fin 126, (Tag.rootCertificate .E7).root k node1 = 0 ∧
      MinData.toWeight ((Tag.rootCertificate .E7).root k) ⬝ᵥ theta4 = 0 ∧
      pr μ ((Tag.rootCertificate .E7).root k) = -1 ∧
      e7Data.wt γ = e7Data.wt μ + MinData.toWeight ((Tag.rootCertificate .E7).root k)) ∨
    (∃ ν : Fin e7Data.d, pr ν theta = 0 ∧ pr ν theta4 = 1 ∧
      ∃ k₁ : Fin 126, (Tag.rootCertificate .E7).root k₁ node1 = 0 ∧
        MinData.toWeight ((Tag.rootCertificate .E7).root k₁) ⬝ᵥ theta4 = 0 ∧
        pr μ ((Tag.rootCertificate .E7).root k₁) = -1 ∧
        e7Data.wt ν = e7Data.wt μ + MinData.toWeight ((Tag.rootCertificate .E7).root k₁) ∧
        ∃ k₂ : Fin 126, (Tag.rootCertificate .E7).root k₂ node1 = 0 ∧
          MinData.toWeight ((Tag.rootCertificate .E7).root k₂) ⬝ᵥ theta4 = 0 ∧
          pr ν ((Tag.rootCertificate .E7).root k₂) = -1 ∧
          e7Data.wt γ = e7Data.wt ν + MinData.toWeight ((Tag.rootCertificate .E7).root k₂)) := by
  decide +kernel

theorem exists_two_steps4 {μ γ : Fin e7Data.d} (hμ : μ ∈ idx0) (hμ1 : pr μ theta4 = 1)
    (hγ : γ ∈ idx0) (hγ1 : pr γ theta4 = 1) :
    μ = γ ∨
    (∃ β, β ∈ Perp4 ∧ pr μ β = -1 ∧ shift β μ = γ) ∨
    (∃ β₁ β₂ ν, β₁ ∈ Perp4 ∧ pr μ β₁ = -1 ∧ shift β₁ μ = ν ∧
      β₂ ∈ Perp4 ∧ pr ν β₂ = -1 ∧ shift β₂ ν = γ) := by
  rcases w3_check4 μ (mem_idx0.1 hμ) hμ1 γ (mem_idx0.1 hγ) hγ1 with
    h | ⟨k, hk0, hk1, hpr, hwt⟩ | ⟨ν, _, _, k₁, hk₁0, hk₁1, hpr₁, hwt₁, k₂, hk₂0, hk₂1, hpr₂, hwt₂⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨(Tag.rootCertificate .E7).root k,
      mem_Perp4.2 ⟨perp_iff.2 ⟨isRoot_root126 k, hk0⟩, hk1⟩, hpr, shift_eq hwt⟩)
  · exact Or.inr (Or.inr ⟨(Tag.rootCertificate .E7).root k₁, (Tag.rootCertificate .E7).root k₂, ν,
      mem_Perp4.2 ⟨perp_iff.2 ⟨isRoot_root126 k₁, hk₁0⟩, hk₁1⟩, hpr₁, shift_eq hwt₁,
      mem_Perp4.2 ⟨perp_iff.2 ⟨isRoot_root126 k₂, hk₂0⟩, hk₂1⟩, hpr₂, shift_eq hwt₂⟩)

end CFSG.RankThree.GF2n.Smith81.RootGenE4
