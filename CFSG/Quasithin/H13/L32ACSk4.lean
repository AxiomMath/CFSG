module

public import CFSG.Quasithin.H13.A6Inputs13_3
public import CFSG.Quasithin.H13.L32ASk2

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def Lemma14_7_50_Mod : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ K ∈ cComp H, H = K ⊔ T → L32A.l1 T L V ≤ K → IsAlt 7 (L32A.cStar K) →
    ∀ π : ↥H →* Equiv.Perm (Fin 7), π.ker = CFSG.Open.pCore 2 ↥H →
      alternatingGroup (Fin 7) ≤ π.range →
      ∃ I : Subgroup G, fsuV1 T V ≤ I ∧ I < conjClosure V H ∧
        H ≤ Subgroup.normalizer (I : Set G) ∧
        ((π.range = alternatingGroup (Fin 7) ∧ ∃ Δ : Finset (Fin 7), Δ.card = 3 ∧
            ∀ h : ↥H, (h : G) ∈ Subgroup.normalizer ((V ⊔ I : Subgroup G) : Set G) ↔
              ∀ i ∈ Δ, π h i ∈ Δ) ∨
          ∃ β : ↥(conjClosure V H) →* ↥(G6.coreMod 7), Function.Surjective β ∧
            β.ker = I.subgroupOf (conjClosure V H) ∧
            ∀ (h : ↥H) (x x' : ↥(conjClosure V H)), (x' : G) = h * x * (h : G)⁻¹ →
              β x' = G6.coreAct 7 (π h) (β x))

@[expose] def Lemma14_7_51_Mod : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ K ∈ cComp H, H = K ⊔ T → L32A.l1 T L V ≤ K → IsPSL 4 2 1 (L32A.cStar K) →
    ∀ π : ↥H →* Equiv.Perm (Fin 8), Function.Surjective π →
      π.ker = CFSG.Open.pCore 2 ↥H →
      ∀ V₂ : Subgroup G, A6.IsV2 T V V₂ →
        2 ≤ CFSG.pRank 3 ↥(Subgroup.centralizer (V₂ : Set G))

end CFSG.Quasithin.H13.L32A.C
