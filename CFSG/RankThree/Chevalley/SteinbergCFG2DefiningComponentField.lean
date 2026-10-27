module

public import CFSG.RankThree.Chevalley.SteinbergCFExceptionalModelCover
public import CFSG.RankThree.Chevalley.SteinbergCFOddCommutingSL2
public import CFSG.RankThree.CentralCover.SteinbergBNCommutingSL2Defining
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalDefiningComponent

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (localRank)

theorem two_mul_le_localRank_of_G2 {L : Type*} [Group L] [Finite L] {p f : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = p ^ f)
    (e : L ⧸ Subgroup.center L ≃* AdjointQuotient .G2 K) : 2 * f ≤ localRank p L := by
  have : Fintype K := Fintype.ofFinite K
  have : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by
    rw [ringChar.eq K p]
    omega
  obtain ⟨φ, hφ, hker⟩ := exists_central_surjection_adjointGroup e
  obtain ⟨ι₁, ι₂, h₁, h₂, hcomm⟩ := G2_two_commuting_faithful_SL2 K hK2
  obtain ⟨-, -, -, -, -, -, -, hrank⟩ :=
    CFSG.RankThree.CentralCover.commuting_SL2_actual_central_cover_defining_local_rank
      (⊤ : Subgroup L) hp hp3 hf (by norm_num : 1 ≤ 2)
      (by rw [← Nat.card_eq_fintype_card]; exact hK) φ hφ hker ![ι₁, ι₂]
      (fun i => by fin_cases i <;> assumption) (fun i j hij A B => by
        fin_cases i <;> fin_cases j
        · exact absurd rfl hij
        · exact hcomm A B
        · exact (hcomm B A).symm
        · exact absurd rfl hij)
  exact hrank

theorem G2_defining_prime_actual_component_field_restriction {X : Type} [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (N : Subgroup X) [N.Normal] (hN : ¬p ∣ Nat.card N)
    (hX : localRank p X ≤ 3) (L : Subgroup (X ⧸ N)) {f : ℕ}
    (hmod : ChevalleyExceptionalModel (L ⧸ Subgroup.center L) .G2 p f) : f = 1 := by
  have hL := CFSG.RankThree.Classical.localRank_le_of_le_quotient hp (by omega) N hN L
  have hf : 1 ≤ f := hmod.1.2.1
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmod.2
  have := two_mul_le_localRank_of_G2 hp hp3 hf hK e
  omega

end CFSG.RankThree.Chevalley
