module

public import CFSG.Quasithin.Background.RonanF617Shapes
public import CFSG.Quasithin.Background.RonanF610
public import CFSG.Quasithin.Background.F6F613
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLargeHolds

public section

namespace CFSG.Quasithin.RonanF617

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F6

variable {D : Type} [Group D] [Finite D] {G₁ G₂ : Subgroup D}

theorem f6_17_of
    (hW : WalterModelsStatement) (h : IsGoldschmidtTriple G₁ G₂)
    (hO : CFSG.pPrimeCore 3 D = ⊥) (hO2 : Open.pCore 2 D = ⊥)
    (hcyc : IsCyclic ↥(CFSG.pCore 3 D))
    (hev : ∀ K : Subgroup D, CFSG.IsComponent K →
      CFSG.Open.evenRank (↥K ⧸ Subgroup.center ↥K) ≤ 2) :
    (twoResidual (⊤ : Subgroup D) = CFSG.generalizedFitting D ∧
        CFSG.IsQuasisimple ↥(twoResidual (⊤ : Subgroup D))) ∨
      (∃ (K Z : Subgroup D) (p e : ℕ),
        IsL2 p e ↥K ∧ (p ^ e % 24 = 11 ∨ p ^ e % 24 = 13) ∧
        Nat.card ↥Z = 3 ∧ K ⊔ Z = twoResidual (⊤ : Subgroup D) ∧ K ⊓ Z = ⊥ ∧
        (∀ k ∈ K, ∀ z ∈ Z, k * z = z * k) ∧
        Nonempty (↥(G₁ ⊓ G₂) ≃* DihedralGroup 4) ∧
        ((Nonempty (↥G₁ ≃* DihedralGroup 12) ∧ Nonempty (↥G₂ ≃* Equiv.Perm (Fin 4))) ∨
          (Nonempty (↥G₂ ≃* DihedralGroup 12) ∧ Nonempty (↥G₁ ≃* Equiv.Perm (Fin 4)))) ∧
        ∀ t ∈ G₁ ⊓ G₂, t ∉ K → InducesOuterAut t K ∧ InducesOuterAut t Z) := by
  obtain ⟨K, hKc⟩ := exists_isComponent_of_isCyclic h hO hcyc
  obtain ⟨hKn, hcases, -⟩ := RonanF610.f6_10_of_list goldschmidtS3ListCat_holds.{0} h hKc
  have hF613 := f613Two_of_list goldschmidtS3ListCat_holds.{0}
  rcases hcases with ⟨h₁, -⟩ | ⟨h₂, -⟩
  · by_cases h₂ : twoResidual G₂ ≤ K
    · exact Or.inl ⟨(generalizedFitting_eq_twoResidual h hO hKc h₁ h₂).symm,
        twoResidual_eq_of_le h hKc h₁ h₂ ▸ hKc.1⟩
    · have hS : Setting G₁ G₂ K :=
        ⟨h, hO, hO2, hKc, hKn, h₁, h₂,
          card_twoResidual_eq_three_of_F613Two hF613 h hO2 (hX := hKn) h₁ h₂⟩
      obtain ⟨p, e, hL2, hq, hZ, hsup, hinf, hcomm, hT, hG₁, hG₂, hout⟩ :=
        hS.nonquasisimple hW (hev K hKc)
      exact Or.inr ⟨K, _, p, e, hL2, hq, hZ, hsup, hinf, hcomm, hT, Or.inl ⟨hG₁, hG₂⟩, hout⟩
  · by_cases h₁ : twoResidual G₁ ≤ K
    · exact Or.inl ⟨(generalizedFitting_eq_twoResidual h hO hKc h₁ h₂).symm,
        twoResidual_eq_of_le h hKc h₁ h₂ ▸ hKc.1⟩
    · have hS : Setting G₂ G₁ K :=
        ⟨h.symm, hO, hO2, hKc, hKn, h₂, h₁,
          card_twoResidual_eq_three_of_F613Two hF613 h.symm hO2 (hX := hKn) h₂ h₁⟩
      obtain ⟨p, e, hL2, hq, hZ, hsup, hinf, hcomm, hT, hG₂, hG₁, hout⟩ :=
        hS.nonquasisimple hW (hev K hKc)
      refine Or.inr ⟨K, _, p, e, hL2, hq, hZ, hsup, hinf, hcomm, ?_, Or.inr ⟨hG₂, hG₁⟩,
        fun t ht htK => hout t (by rwa [inf_comm] at ht) htK⟩
      rw [inf_comm]
      exact hT

end CFSG.Quasithin.RonanF617
