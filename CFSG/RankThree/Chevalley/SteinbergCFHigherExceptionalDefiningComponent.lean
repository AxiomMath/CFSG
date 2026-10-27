module

public import CFSG.RankThree.Chevalley.SteinbergCFExceptionalModelCover
public import CFSG.RankThree.Chevalley.SteinbergCFOddFourCommutingSL2
public import CFSG.RankThree.CentralCover.SteinbergBNCommutingSL2Defining
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalDefiningComponent

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (localRank)

theorem four_mul_le_localRank_of_higherExceptional {L : Type*} [Group L] [Finite L] {p f : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hf : 1 ≤ f) {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = p ^ f) (e : L ⧸ Subgroup.center L ≃* AdjointQuotient τ K) :
    4 * f ≤ localRank p L := by
  have : Fintype K := Fintype.ofFinite K
  have : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by
    rw [ringChar.eq K p]
    omega
  obtain ⟨φ, hφ, hker⟩ := exists_central_surjection_adjointGroup e
  obtain ⟨ι, hι, hcomm⟩ := higher_ordinary_exceptional_four_commuting_faithful_SL2 K hK2 τ hτ
  obtain ⟨-, -, -, -, -, -, -, hrank⟩ :=
    CFSG.RankThree.CentralCover.commuting_SL2_actual_central_cover_defining_local_rank
      (⊤ : Subgroup L) hp hp3 hf (by norm_num : 1 ≤ 4)
      (by rw [← Nat.card_eq_fintype_card]; exact hK) φ hφ hker ι hι hcomm
  exact hrank

theorem higher_ordinary_exceptional_defining_prime_actual_component_exclusion {X : Type}
    [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (N : Subgroup X) [N.Normal]
    (hN : ¬p ∣ Nat.card N) (hX : localRank p X ≤ 3) (L : Subgroup (X ⧸ N)) {τ : StatedLieTag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (f : ℕ) :
    ¬ChevalleyExceptionalModel (L ⧸ Subgroup.center L) τ p f := by
  intro hmod
  have hL := CFSG.RankThree.Classical.localRank_le_of_le_quotient hp (by omega) N hN L
  have key : ∀ τ' : Tag, (τ' = .F4 ∨ τ' = .E6 ∨ τ' = .E7 ∨ τ' = .E8) → 1 ≤ f →
      UntwistedChevalleyModel (L ⧸ Subgroup.center L) τ' (p ^ f) → False := by
    rintro τ' hτ' hf ⟨K, _, _, hK, ⟨e⟩⟩
    have := four_mul_le_localRank_of_higherExceptional hp hp3 hf hτ' hK e
    omega
  rcases hτ with rfl | rfl | rfl | rfl
  · exact key .F4 (Or.inl rfl) hmod.1.2.1 hmod.2
  · exact key .E6 (Or.inr (Or.inl rfl)) hmod.1.2.1 hmod.2
  · exact key .E7 (Or.inr (Or.inr (Or.inl rfl))) hmod.1.2.1 hmod.2
  · exact key .E8 (Or.inr (Or.inr (Or.inr rfl))) hmod.1.2.1 hmod.2

end CFSG.RankThree.Chevalley
