module

public import CFSG.Quasithin.Background.F9Tilde
public import CFSG.Quasithin.EmptyFaithful.S145Basic
public import CFSG.Quasithin.EmptyFaithful.S146Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

section Defs

variable {G : Type} [Group G]

@[expose] def HypB146 (T M : Subgroup G) : Prop :=
  ∀ H : Subgroup G, IsHTM T M H → OddCoreModTwoTrivial H

abbrev KBar (K : Subgroup G) : Type := ↥K ⧸ (pCoreOf 2 K).subgroupOf K

@[expose] def KbarIsL3Two (K : Subgroup G) : Prop :=
  Nonempty (KBar K ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))

@[expose] def KbarIsA6 (K : Subgroup G) : Prop :=
  Nonempty (KBar K ≃* ↥(alternatingGroup (Fin 6)))

@[expose] def KbarInducesOuter (K : Subgroup G) (s : G) : Prop :=
  ∀ k ∈ K, ∃ x ∈ K, ⁅s * k⁻¹, x⁆ ∉ pCoreOf 2 K

@[expose] def KbarFusesThrees (K : Subgroup G) (s : G) : Prop :=
  ∃ x ∈ K, x ^ 3 ∈ pCoreOf 2 K ∧ x ∉ pCoreOf 2 K ∧
    ∀ k ∈ K, (k * x * k⁻¹)⁻¹ * (s * x * s⁻¹) ∉ pCoreOf 2 K

@[expose] def KbarNontrivialOnDynkin (K : Subgroup G) (s : G) : Prop :=
  (KbarIsL3Two K ∧ KbarInducesOuter K s) ∨ (KbarIsA6 K ∧ KbarFusesThrees K s)

@[expose] def IsNaturalLike (K Z U₁ : Subgroup G) : Prop :=
  (KbarIsL3Two K ∧ mIdx U₁ Z = 3 ∧ IsIrredOnSection K U₁ Z) ∨
    (KbarIsA6 K ∧ ((mIdx U₁ Z = 4 ∧ IsIrredOnSection K U₁ Z ∧ ⁅U₁, K⁆ ⊔ Z = U₁) ∨
      (mIdx U₁ Z = 5 ∧ ⁅U₁, K⁆ ⊔ Z = U₁)))

structure IsDecompUK (T M K U₁ U₂ : Subgroup G) (s : G) : Prop where
  mem : s ∈ T ⊓ Subgroup.normalizer (K : Set G)
  dynkin : KbarNontrivialOnDynkin K s
  Z₁ : quasithinOmegaOneCenter T ≤ U₁
  Z₂ : quasithinOmegaOneCenter T ≤ U₂
  conj : U₂ = conjSub s U₁
  sup : ⁅uOfL22 T M, K⁆ ⊔ quasithinOmegaOneCenter T = U₁ ⊔ U₂
  natural : IsNaturalLike K (quasithinOmegaOneCenter T) U₁

@[expose] def IsCase2 (T K : Subgroup G) : Prop :=
  ∃ t ∈ T, t ∉ Subgroup.normalizer (K : Set G) ∧ perfectCore (mcOf T) = K ⊔ conjSub t K

@[expose] def IsChoiceU (T M K U₁ : Subgroup G) (u : G) : Prop :=
  (¬ IsCase2 T K ∧ u ∈ U₁ ∧ ¬ ⁅Subgroup.zpowers u, K⁆ ≤ quasithinOmegaOneCenter T ∧
      T ⊓ Subgroup.normalizer (U₁ : Set G) ≤ tZero T u) ∨
    (IsCase2 T K ∧ u ∈ ⁅uOfL22 T M, K⁆ ∧ u ∉ quasithinOmegaOneCenter T ∧
      T ⊓ Subgroup.normalizer (K : Set G) ≤ tZero T u)

@[expose] def Conc14619 (T M : Subgroup G) : Prop :=
  ∀ H : Subgroup G, IsHTM T M H →
    OddCoreModTwoTrivial H ∧ ∀ K ∈ cComp H, IsSimpleGroup (KBar K)

@[expose] def Conc14620 (T M : Subgroup G) : Prop :=
  ∀ H : Subgroup G, IsHTM T M H → ∀ K ∈ cComp H,
    (KbarIsL3Two K ∨ KbarIsA6 K) ∧ ∃ s ∈ T ⊓ Subgroup.normalizer (K : Set G), KbarNontrivialOnDynkin K s

@[expose] def Conc14621 (T K : Subgroup G) : Prop :=
  (perfectCore (mcOf T) = K ∧ (KbarIsL3Two K ∨ KbarIsA6 K)) ∨
  (IsCase2 T K ∧ KbarIsL3Two K) ∨
  (∃ Kp ∈ cComp (mcOf T), Kp ≠ K ∧ mcOf T ≤ Subgroup.normalizer (K : Set G) ∧
      mcOf T ≤ Subgroup.normalizer (Kp : Set G) ∧ perfectCore (mcOf T) = K ⊔ Kp ∧
      KbarIsL3Two K ∧ KbarIsL3Two Kp)

@[expose] def Conc14622 (T M K : Subgroup G) : Prop :=
  (∃ (U₁ U₂ : Subgroup G) (s : G), IsDecompUK T M K U₁ U₂ s) ∧
    ∀ Kp ∈ cComp (mcOf T), Kp ≠ K → ⁅⁅uOfL22 T M, K⁆, Kp⁆ = ⊥

@[expose] def Conc14623 (T M : Subgroup G) : Prop :=
  (perfectCore (mcOf T) = oTwoUpper (mcOf T) ∧ mcOf T = perfectCore (mcOf T) ⊔ T) ∧
    (M = yOfL22 T M ⊔ T ∧ T = M ⊓ mcOf T) ∧
    (tildeOf (quasithinOmegaOneCenter T) (uOfL22 T M) =
        (⨆ K ∈ cComp (mcOf T), tildeOf (quasithinOmegaOneCenter T) ⁅uOfL22 T M, K⁆) ⊔
          tildeOf (quasithinOmegaOneCenter T)
            (centralizerMod (quasithinOmegaOneCenter T) (uOfL22 T M) (mcOf T)) ∧
      ∀ K ∈ cComp (mcOf T),
        tildeOf (quasithinOmegaOneCenter T) ⁅uOfL22 T M, K⁆ ⊓
          (⨆ K' ∈ {K' | K' ∈ cComp (mcOf T) ∧ K' ≠ K},
              tildeOf (quasithinOmegaOneCenter T) ⁅uOfL22 T M, K'⁆) = ⊥)

@[expose] def Conc14624 (T M K : Subgroup G) (u : G) : Prop :=
  IsInvU T M (mcOf T) u ∧ KbarIsL3Two K ∧ K = perfectCore (mcOf T) ∧
    IsI T M u (Subgroup.centralizer ({u} : Set G))

structure BData146 (T M K U₁ U₂ : Subgroup G) (s : G) (u : G) : Prop where
  hK : K ∈ cComp (mcOf T)
  c19 : Conc14619 T M
  c20 : Conc14620 T M
  c21 : Conc14621 T K
  c22 : Conc14622 T M K
  c23 : Conc14623 T M
  dec : IsDecompUK T M K U₁ U₂ s
  choice : IsChoiceU T M K U₁ u
  c24 : Conc14624 T M K u

end Defs

@[expose] def Stage14619 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M → HypB146 T M →
    Conc14619 T M

@[expose] def Stage14620 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M → HypB146 T M →
    Conc14619 T M → Conc14620 T M

@[expose] def Stage14621 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M → HypB146 T M →
    Conc14619 T M → Conc14620 T M → ∀ K ∈ cComp (mcOf T), Conc14621 T K

@[expose] def Stage14622 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M → HypB146 T M →
    Conc14619 T M → Conc14620 T M → ∀ K ∈ cComp (mcOf T), Conc14621 T K → Conc14622 T M K

@[expose] def Stage14623 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M → HypB146 T M →
    Conc14619 T M → Conc14620 T M → (∀ K ∈ cComp (mcOf T), Conc14621 T K ∧ Conc14622 T M K) →
      Conc14623 T M

@[expose] def Stage146D4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M → HypB146 T M →
    ∀ K ∈ cComp (mcOf T), Conc14621 T K → Conc14622 T M K → Conc14623 T M →
      ∀ (U₁ U₂ : Subgroup G) (s : G), IsDecompUK T M K U₁ U₂ s → ∃ u : G, IsChoiceU T M K U₁ u

@[expose] def Stage14624 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M → HypB146 T M →
    Conc14619 T M → Conc14620 T M → Conc14623 T M →
    ∀ K ∈ cComp (mcOf T), Conc14621 T K → Conc14622 T M K →
      ∀ (U₁ U₂ : Subgroup G) (s : G), IsDecompUK T M K U₁ U₂ s →
        ∀ u : G, IsChoiceU T M K U₁ u → Conc14624 T M K u

@[expose] def Stage146FRank : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M → HypB146 T M →
    ∀ (K U₁ U₂ : Subgroup G) (s u : G), BData146 T M K U₁ U₂ s u →
      4 < (pCoreOf 2 (mcOf T)).relIndex T ∧
        4 ≤ mIdx (conjClosure (VZ T M) (mcOf T))
          (Subgroup.centralizer (pCoreOf 2 (mcOf T) : Set G))

@[expose] def Stage146FH2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M → HypB146 T M →
    ∀ (K U₁ U₂ : Subgroup G) (s u : G), BData146 T M K U₁ U₂ s u →
      Nonempty (OTwoQuot (centralizerMod (quasithinOmegaOneCenter T) (mcOf T)
          (Subgroup.zpowers u)) ≃* Equiv.Perm (Fin 3)) ∧
        ¬ centralizerMod (quasithinOmegaOneCenter T) (mcOf T) (Subgroup.zpowers u) ≤ M

@[expose] def Stage146FFour : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M → HypB146 T M →
    ∀ (K U₁ U₂ : Subgroup G) (s u : G), BData146 T M K U₁ U₂ s u →
      Nat.card (conjClosure (VZ T M) (oTwoUpper (centralizerMod (quasithinOmegaOneCenter T)
        (mcOf T) (Subgroup.zpowers u)))) = 2 ^ 4

end CFSG.Quasithin
