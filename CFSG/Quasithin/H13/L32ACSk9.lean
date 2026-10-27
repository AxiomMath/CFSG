module

public import CFSG.Quasithin.H13.A6Inputs13_3
public import CFSG.Quasithin.H13.L32ASk2

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def Lemma14751Levi : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ K ∈ cComp H, H = K ⊔ T → L32A.l1 T L V ≤ K → IsPSL 4 2 1 (L32A.cStar K) →
    ∀ π : ↥H →* Equiv.Perm (Fin 8), Function.Surjective π → π.ker = CFSG.Open.pCore 2 ↥H →
    ∀ I : Subgroup G, fsuV1 T V ≤ I → I < conjClosure V H →
      H ≤ Subgroup.normalizer (I : Set G) →
    ∀ Y V₂ T₀ : Subgroup G, A6.IsV2 T V V₂ → Y ≤ K → oTwoUpper Y = Y → T₀ ≤ T →
      T₀.relIndex T = 2 → T₀ ≤ K ⊔ pCoreOf 2 H → T₀ ≤ Subgroup.normalizer (Y : Set G) →
      IsSylowTwoOf T₀ (Y ⊔ T₀) → quasithinO2QuotientIso (Y ⊔ T₀) (Equiv.Perm (Fin 3)) →
      ⁅V₂, Y⁆ ≤ I → (fsuV1 T V).relIndex (conjClosure V₂ Y) ≠ 8

end CFSG.Quasithin.H13.L32A.C
