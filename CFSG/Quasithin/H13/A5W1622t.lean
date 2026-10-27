module

public import CFSG.Quasithin.H13.A5S136h

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def Lem13622A7Block : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V), S.Hyp1367 →
    ∀ K : Subgroup G, K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G)) → S.InYz K →
      S.Tv ≤ Subgroup.normalizer (K : Set G) → S.Lv ≤ K → IsAlt 7 ↥(S.plus K) →
      IsBlock2 (K ⊔ S.Tv) K → IsAltType K 7 →
        ∃ K₁ : Subgroup G, K₁ ≤ K ∧ K₁ ∈ lFamily S.Tv ∧
          S.Tv ≤ Subgroup.normalizer (K₁ : Set G) ∧ S.Lv ≤ K₁ ∧
          Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* alternatingGroup (Fin 6))

@[expose] def Lemma13622C : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V), S.Hyp1367 →
    ∀ K : Subgroup G, K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G)) → S.InYz K →
      S.Tv ≤ Subgroup.normalizer (K : Set G) →
      (∀ (F : Type) [Field F] [Finite F], Nat.card F = 2 →
        ¬ Nonempty (↥(S.plus K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))) ∧
      ¬ IsAlt 6 ↥(S.plus K) ∧
      (∀ (F : Type) [Field F] [Finite F], Nat.card F = 2 →
        ¬ Nonempty (↥(S.plus K) ≃* ↥⁅CFSG.Open.quasithinG2 F, CFSG.Open.quasithinG2 F⁆)) ∧
      ¬ IsHat ↥(S.plus K) ↥(alternatingGroup (Fin 6)) ∧ ¬ IsAlt 7 ↥(S.plus K)

@[expose] def Lemma13623C : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V), S.Hyp1367 →
    ∀ K : Subgroup G, K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G)) → S.InYz K →
      S.Tv ≤ Subgroup.normalizer (K : Set G) →
      ¬ Nonempty (↥(S.plus K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2))) ∧
      ¬ Nonempty (↥(S.plus K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2)))

end CFSG.Quasithin.H13.A5
