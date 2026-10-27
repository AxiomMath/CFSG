module

public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.H13.L32ASk2

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def Lemma14741PGL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ K ∈ cComp H, H = K ⊔ (l1 T L V ⊔ T) →
      ∀ n : ℕ, 1 < n → A315.IsLieChar2 n (cStar K ⧸ Subgroup.center (cStar K)) →
        ¬ l1 T L V ≤ K → CFSG.oddCore (↥H ⧸ CFSG.pCore 2 ↥H) = ⊥ →
          ¬ IsPSL 3 2 2 (cStar K ⧸ Subgroup.center (cStar K))

@[expose] def Lemma14_7_42_S5S3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ K ∈ cComp H, H = K ⊔ (l1 T L V ⊔ T) →
      ∀ n : ℕ, 1 < n → A315.IsLieChar2 n (cStar K ⧸ Subgroup.center (cStar K)) →
        ¬ l1 T L V ≤ K →
        ∃ ρ : ↥H →* Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3), Function.Surjective ρ ∧
          ρ.ker = CFSG.Open.pCore 2 ↥H

end CFSG.Quasithin.H13.L32A.C
