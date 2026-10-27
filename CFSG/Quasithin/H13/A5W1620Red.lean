module

public import CFSG.Quasithin.H13.A5S136h
public import CFSG.Quasithin.Background.C41PfCorr

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def Lemma13620L32Red : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V), S.Hyp1367 →
    ∀ K : Subgroup G, K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G)) → S.InYz K →
      S.Tv ≤ Subgroup.normalizer (K : Set G) →
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
        Nonempty (↥(S.plus K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))) →
    ∀ K₀ : Subgroup G, K₀ ≤ K → K₀ ∈ lFamily S.Tv → S.Tv ≤ Subgroup.normalizer (K₀ : Set G) →
      autOn K₀ (S.WK K) = S.plus K → ¬ K₀ ≤ Subgroup.centralizer ({S.z} : Set G) →
      CharTwo (K₀ ⊔ S.Tv) → IsMSPair (K₀ ⊔ S.Tv) S.Tv →
      S.WK K ≤ pCoreOf 2 (K₀ ⊔ S.Tv) →
      IsTwoReducedIn (K₀ ⊔ S.Tv) (conjClosure S.V1 (K₀ ⊔ S.Tv)) →
      S.Lv ≤ Subgroup.normalizer (K₀ : Set G) →
      (∀ g : G, (∀ t ∈ S.Tv,
          (g * S.z * g⁻¹) * t * (g * S.z * g⁻¹)⁻¹ * t⁻¹ ∈ Subgroup.zpowers S.v12) →
        ¬ K₀ ≤ Subgroup.centralizer ({g * S.z * g⁻¹} : Set G)) →
      (∃ (F : Type) (_ : Field F) (_ : Fintype F)
        (α : ↥K₀ →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)),
        Fintype.card F = 2 ∧ IsModO2Surj K₀ α) →
      (∃ i : ℕ, C134CorrLocal.IsC134CaseCorr i (K₀ ⊔ S.Tv) S.Tv K₀) →
        S.Lv ≤ K₀

end CFSG.Quasithin.H13.A5
