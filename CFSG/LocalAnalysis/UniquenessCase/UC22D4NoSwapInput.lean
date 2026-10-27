module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2ExcNoSwap
import CFSG.LocalAnalysis.UniquenessCase.UC22D4FunCentralizer
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2Rho
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2RhoGen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open scoped MatrixGroups


theorem uc22s2112r34_d4_noSwapInput {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hX : LieModel X .trialityD4 0 p 1) (S : Sylow 2 X)
    {K₁ K₂ : Subgroup X}
    (h₁ : K₁ ∈ F14.FunSet (fundPred p) X (S : Subgroup X))
    (h₂ : K₂ ∈ F14.FunSet (fundPred p) X (S : Subgroup X)) (hne : K₁ ≠ K₂)
    (hcomm : ⁅K₁, K₂⁆ = ⊥) :
    UC22NoSwapInput p (S : Subgroup X) K₁ K₂ := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hadm : StatedLieAdmissible .trialityD4 0 p 1 := ⟨hp, le_rfl, rfl⟩
  have h₁' : K₁ ∈ F14.FunSet (fundPred (p ^ 1)) X (S : Subgroup X) := by rwa [pow_one]
  have h₂' : K₂ ∈ F14.FunSet (fundPred (p ^ 1)) X (S : Subgroup X) := by rwa [pow_one]
  have hC₁ := d4_centralizer_funSet_le hp hp2 hadm hX S h₁' h₂' hne
  have hC₂ := d4_centralizer_funSet_le hp hp2 hadm hX S h₂' h₁' hne.symm
  have hF : Nat.card (GaloisField p 1) = p := by
    rw [GaloisField.card p 1 (by norm_num), pow_one]
  have hF3 : Nat.card (GaloisField p (3 * 1)) = p ^ 3 := GaloisField.card p (3 * 1) (by norm_num)
  have hlong : ∀ K ∈ F14.FunSet (fundPred p) X (S : Subgroup X),
      Nonempty (K ≃* SL(2, GaloisField p 1)) →
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F p)
        (ρ : normalizer (K : Set X) →* PGL(Fin 2, F)),
        (∀ g, ρ g = 1 ↔ ∀ k ∈ K, (g : X) * k * (g : X)⁻¹ = k) ∧
        ((S : Subgroup X) ≤ normalizer (K : Set X) →
          ¬ IsCyclic ((((S : Subgroup X) ⊓ K).subgroupOf (normalizer (K : Set X))).map ρ)) := by
    rintro K hK ⟨eK⟩
    exact ⟨GaloisField p 1, inferInstance, inferInstance, inferInstance,
      uc22s2112r34_rho K hp5 hF eK, uc22s2112r34_rho_eq_one_iff hp5 hF eK,
      fun _ => uc22s2112r34_rho_not_isCyclic hp5 hF eK hK.2⟩
  have hshort : ∀ K ∈ F14.FunSet (fundPred p) X (S : Subgroup X), ∀ K' : Subgroup X,
      centralizer (K : Set X) ≤ K' → centralizer (K' : Set X) ≤ K → ⁅K, K'⁆ = ⊥ →
      Nonempty (K ≃* SL(2, GaloisField p (3 * 1))) → Nonempty (K' ≃* SL(2, GaloisField p 1)) →
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F p)
        (ρ : normalizer (K : Set X) →* PGL(Fin 2, F)),
        (∀ g, ρ g = 1 ↔ ∀ k ∈ K, (g : X) * k * (g : X)⁻¹ = k) ∧
        ((S : Subgroup X) ≤ normalizer (K : Set X) →
          ¬ IsCyclic ((((S : Subgroup X) ⊓ K).subgroupOf (normalizer (K : Set X))).map ρ)) := by
    rintro K hK K' hKK' hK'K hKc ⟨eK⟩ ⟨eK'⟩
    obtain ⟨ρ, hρ1, hρ2⟩ := uc22s2112r34_exists_rho_of_partner hp hp5 ⟨1, rfl⟩ hF3 hKK' hK'K
      hKc hF eK eK'
    exact ⟨GaloisField p (3 * 1), inferInstance, inferInstance, inferInstance, ρ, hρ1,
      fun _ => hρ2 hK.2⟩
  have hcomm' : ⁅K₂, K₁⁆ = ⊥ := (Subgroup.commutator_comm K₂ K₁).trans hcomm
  refine ⟨hC₁, hC₂, fun K hK => ?_, fun _ _ K hK => ?_⟩
  · rcases d4_funSet_equiv_sl2 hp2 hadm hX S h₁' h₂' hne with ⟨e₁, e₂⟩ | ⟨e₂, e₁⟩ <;>
      rcases hK with rfl | rfl
    · exact hlong _ h₁ e₁
    · exact hshort _ h₂ _ hC₂ hC₁ hcomm' e₂ e₁
    · exact hshort _ h₁ _ hC₁ hC₂ hcomm e₁ e₂
    · exact hlong _ h₂ e₂
  · obtain ⟨w, hwS, hw⟩ :=
      uc22s2112r34_exc_exists_not_mem_sup hp hp2 (Or.inr rfl) hX S h₁.1 h₂.1 hcomm hC₁
    exact ⟨w, hwS, uc22s2112r34_noswap_outer_of_not_mem hC₁ hC₂ hw K hK⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
