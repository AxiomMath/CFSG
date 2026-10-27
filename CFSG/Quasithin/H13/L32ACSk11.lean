module

public import CFSG.Quasithin.H13.L32ASk1
public import CFSG.Quasithin.H13.L32ASk2

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def tensSums : (Fin 5 → Fin 3 → ZMod 2) →+ (Fin 5 → ZMod 2) × (Fin 3 → ZMod 2) where
  toFun M := (fun i => ∑ j, M i j, fun j => ∑ i, M i j)
  map_zero' := by
    ext <;> simp
  map_add' M N := by
    ext <;> simp [Finset.sum_add_distrib]

@[expose] def tensMod53 : Subgroup (Multiplicative (Fin 5 → Fin 3 → ZMod 2)) :=
  (AddMonoidHom.toMultiplicative tensSums).ker

@[expose] def Lemma14_7_42 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ K ∈ cComp H, H = K ⊔ (l1 T L V ⊔ T) →
      ∀ n : ℕ, 1 < n → A315.IsLieChar2 n (cStar K ⧸ Subgroup.center (cStar K)) →
        ¬ l1 T L V ≤ K →
        ∃ ρ : ↥H →* Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3), Function.Surjective ρ ∧
          ρ.ker = CFSG.Open.pCore 2 ↥H ∧
          (⁅conjClosure V H, K⁆ ⊔ fsuV1 T V) ⊔ centralizerMod (fsuV1 T V) (conjClosure V H) K =
            conjClosure V H ∧
          (⁅conjClosure V H, K⁆ ⊔ fsuV1 T V) ⊓ centralizerMod (fsuV1 T V) (conjClosure V H) K =
            fsuV1 T V ∧
          ∃ β : ↥(⁅conjClosure V H, K⁆ ⊔ fsuV1 T V) →* Multiplicative (Fin 5 → Fin 3 → ZMod 2),
            β.range = tensMod53 ∧
            β.ker = (fsuV1 T V).subgroupOf (⁅conjClosure V H, K⁆ ⊔ fsuV1 T V) ∧
            ∀ (h : ↥H) (x x' : ↥(⁅conjClosure V H, K⁆ ⊔ fsuV1 T V)),
              (x' : G) = h * x * (h : G)⁻¹ → ∀ i j, Multiplicative.toAdd (β x') i j =
                Multiplicative.toAdd (β x) ((ρ h).1⁻¹ i) ((ρ h).2⁻¹ j)

@[expose] def Lemma14_7_43 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ K ∈ cComp H, H = K ⊔ (l1 T L V ⊔ T) →
      ∀ n : ℕ, 1 < n → A315.IsLieChar2 n (cStar K ⧸ Subgroup.center (cStar K)) →
        ¬ IsPSU 3 2 3 (cStar K ⧸ Subgroup.center (cStar K))

@[expose] def Lemma14_7_44 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ K ∈ cComp H, H = K ⊔ (l1 T L V ⊔ T) →
      ∀ n : ℕ, 1 < n → A315.IsLieChar2 n (cStar K ⧸ Subgroup.center (cStar K)) →
        ¬ IsPSL 3 2 2 (cStar K ⧸ Subgroup.center (cStar K))

@[expose] def Lemma14_7_46_Amalgam : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ K ∈ cComp H, H = K ⊔ (l1 T L V ⊔ T) →
      ∀ n : ℕ, 1 < n → A315.IsLieChar2 n (cStar K ⧸ Subgroup.center (cStar K)) →
        ¬ l1 T L V ≤ K → ∀ V₂ : Subgroup G, A6.IsV2 T V V₂ →
          pCoreOf 2 (L32A.i2 T V V₂ ⊔ K ⊔ T) ≠ ⊥

end CFSG.Quasithin.H13.L32A.C
