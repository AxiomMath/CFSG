module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20z
public import CFSG.LocalAnalysis.UniquenessCase.Lie.Sp4Aut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

@[expose] def uc22pwCartanSL3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsQuasisimple X → ∀ n : ℕ, 2 < n →
    IsSL3 X n →
    ∀ (U : Sylow 2 X) (P : Type) [Group P], IsPGroup 2 P → ∀ ψ : P →* MulAut X,
      (∀ (g : P) (x : X), x ∈ (U : Subgroup X) ↔ ψ g x ∈ (U : Subgroup X)) →
      ∀ e m' : ℕ, Odd m' → n = 2 ^ e * m' →
      ∃ E : Subgroup X, E ≤ normalizer ((U : Subgroup X) : Set X) ∧ IsMulCommutative E ∧
        Odd (Nat.card E) ∧
        (∀ p : ℕ, p.Prime → ∃ Q : Sylow p E, IsElemAbelian p (Q : Subgroup E) ∧ Nat.card Q ≤ p ^ 2) ∧
        piSet E = etaSet n ∧
        (∀ (g : P), ∀ x ∈ E, ψ g x ∈ E ⊔ (U : Subgroup X)) ∧
        (∀ (g : P), ∀ x ∈ oPi {p | p.Prime ∧ p ∣ 2 ^ m' - 1} E, ψ g x * x⁻¹ ∈ (U : Subgroup X)) ∧
        ∃ w : X, w ^ 2 = 1 ∧ (∀ x ∈ E, w * x * w⁻¹ = x⁻¹) ∧
          normalizer ((U : Subgroup X) : Set X) ⊔ Subgroup.zpowers w = ⊤

theorem uc22pwCartanGraph_of_sl3 (h : uc22pwCartanSL3) : uc22pwCartanGraph := by
  intro X _ _ hqs n hn hshape U P _ hP ψ hψ e m' hm' hnem
  rcases hshape with hsl3 | hsp4
  · exact h X hqs n hn hsl3 U P hP ψ hψ e m' hm' hnem
  · have hc := uc22pwlie_sp4_of_isSp4 hn hsp4 U hP ψ hψ hm' hnem
    unfold uc22pwlie_Concl at hc
    obtain ⟨E, hEN, ⟨hcomm, hodd, hsyl⟩, hpi, hinv, hα, w, hw2, hwinv, hwgen⟩ := hc
    exact ⟨E, hEN, hcomm, hodd, hsyl, hpi, hinv, hα, w, hw2, hwinv, hwgen⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
