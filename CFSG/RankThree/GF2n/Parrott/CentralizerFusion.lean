module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.GF2n.Parrott.Basic

@[expose] public section

namespace CFSG.RankThree.GF2n.Parrott

variable {G : Type} [Group G] [Finite G] {z : G}

def CJ (z : G) (σ : G) : Subgroup G := Subgroup.centralizer ({σ} : Set G) ⊓ J z

theorem mem_CJ {σ : G} {x : G} : x ∈ CJ z σ ↔ x ∈ Subgroup.centralizer ({σ} : Set G) ∧ x ∈ J z :=
  Iff.rfl

theorem CJ_eq_of_conj_eq_of_card_eq {σ₁ σ₂ : G}
    (hcard : Nat.card (CJ z σ₁) = Nat.card (CJ z σ₂))
    (hfix : ∀ x ∈ CJ z σ₁, σ₂ * x * σ₂⁻¹ = x) :
    CJ z σ₁ = CJ z σ₂ := by
  haveI : Finite ↥(CJ z σ₂) := Subtype.finite
  apply Subgroup.eq_of_le_of_card_ge
  · intro x hx
    rw [mem_CJ] at hx ⊢
    refine ⟨?_, hx.2⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := hfix x (by rwa [mem_CJ])
    calc x * σ₂ = (σ₂ * x * σ₂⁻¹) * σ₂ := by rw [h]
      _ = σ₂ * x := by group
  · rw [← hcard]

theorem not_forall_conj_eq_of_ne {σ₁ σ₂ : G}
    (hcard : Nat.card (CJ z σ₁) = Nat.card (CJ z σ₂))
    (hne : CJ z σ₁ ≠ CJ z σ₂) :
    ¬ ∀ x ∈ CJ z σ₁, σ₂ * x * σ₂⁻¹ = x := by
  intro hfix
  exact hne (CJ_eq_of_conj_eq_of_card_eq hcard hfix)

end CFSG.RankThree.GF2n.Parrott
