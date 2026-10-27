module

public import CFSG.Quasithin.Background.F9Eighteen
public import CFSG.Quasithin.Background.A3Structure315Defs
public import CFSG.Quasithin.H13.A6Statements
public import CFSG.Quasithin.H13.L32ASetting
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

namespace L32A

variable {G : Type} [Group G]

abbrev cStar (K : Subgroup G) : Type := ↥K ⧸ (pCoreOf 2 K).subgroupOf K

@[expose] def IsSLnSection (n : ℕ) (K X Y : Subgroup G) : Prop :=
  K ≤ Subgroup.normalizer (X : Set G) ∧
    ∃ (π : K →* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
      (β : X →* Multiplicative (Fin n → ZMod 2)),
      Function.Surjective π ∧ π.ker = (pCoreOf 2 K).subgroupOf K ∧
      Function.Surjective β ∧ β.ker = Y.subgroupOf X ∧
      ∀ (k : K) (x x' : X), (x' : G) = k * x * (k : G)⁻¹ →
        β x' = Multiplicative.ofAdd (((π k : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
          Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (Multiplicative.toAdd (β x)))

@[expose] def IsS7NaturalSection (H X Y : Subgroup G) : Prop :=
  H ≤ Subgroup.normalizer (X : Set G) ∧
    ∃ (π : H →* Equiv.Perm (Fin 7)) (β : X →* ↥(G6.coreMod 7)),
      Function.Surjective π ∧ π.ker = (pCoreOf 2 H).subgroupOf H ∧
      Function.Surjective β ∧ β.ker = Y.subgroupOf X ∧
      ∀ (h : H) (x x' : X), (x' : G) = h * x * (h : G)⁻¹ → β x' = G6.coreAct 7 (π h) (β x)

end L32A

@[expose] def Lemma14_7_30 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ K ∈ cComp H, CFSG.IsQuasisimple (L32A.cStar K) ∧ ¬ K ≤ Subgroup.normalizer (L : Set G) ∧
      Setting147 G T L V (conjClosure K T ⊔ (L32A.l1 T L V ⊔ T)) ∧
      HypF918 T V L (fsuV1 T V) V (conjClosure K T ⊔ (L32A.l1 T L V ⊔ T)) K

@[expose] def Lemma14_7_36 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ K ∈ cComp H, ∀ s : TauCeti.SporadicName,
      ¬ IsSporadic s (L32A.cStar K ⧸ Subgroup.center (L32A.cStar K))

@[expose] def Thm14_7_40 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ K ∈ cComp H, H = K ⊔ (L32A.l1 T L V ⊔ T) →
      ∀ n : ℕ, 1 < n → A315.IsLieChar2 n (L32A.cStar K ⧸ Subgroup.center (L32A.cStar K)) →
        quasithinO2QuotientIso H (Equiv.Perm (Fin 5)) ∧
          L32A.IsL24Section K (conjClosure V H) (centralizerMod (fsuV1 T V) (conjClosure V H) K)

@[expose] def Lemma14_7_47 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ K ∈ cComp H, L32A.l1 T L V ≤ K ∧
      ((∃ n : ℕ, IsPSL n 2 1 (L32A.cStar K)) ∨ (∃ n : ℕ, IsAlt n (L32A.cStar K)) ∨
        IsPSU 3 3 1 (L32A.cStar K))

@[expose] def Lemma14_7_48 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∃ K : Subgroup G, cComp H = {K} ∧ H = K ⊔ T ∧ conjClosure V H = ⁅conjClosure V H, K⁆

@[expose] def Thm14_7_52 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ K ∈ cComp H, H = K ⊔ T ∧ H = A6.g1 T V ∧
      (∀ H' : Subgroup G, Setting147 G T L V H' → H' = H) ∧ conjClosure V H = fsuU T V ∧
      (IsAlt 5 (L32A.cStar K) ∨ IsPSU 3 3 1 (L32A.cStar K))

@[expose] def Thm14_7_53 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ K ∈ cComp H, ¬ IsPSU 3 3 1 (L32A.cStar K)

end CFSG.Quasithin.H13
