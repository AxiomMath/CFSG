module

public import CFSG.Quasithin.Vol2.Ch1ModO2
public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.Quasithin.Vol2.Ch10StatementsA
public import CFSG.Quasithin.Vol2.Ch3Basic

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

structure B0KConfig (G : Type) [Group G] [Finite G] (T L I H K M₁ J : Subgroup G) (n m : ℕ) :
    Prop where
  hyp : Hyp10 G T L I
  case1 : Case10_1_1One T L I n
  hH : IsHStar T (fsuM T L) H
  hn : 1 < E1.nParam H
  hZH : ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥
  hK : K ∈ cComp H
  hHK : oTwoUpper H = conjClosure K T
  hKF : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ m ∧
    Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F)
  hM₁ : InM (Subgroup.normalizer (baum T : Set G) ⊔ H) M₁
  hJ : J ∈ cComp M₁
  hKJ : K ≤ J

@[expose] def B0KTypeB (M₁ K J : Subgroup G) : Prop :=
  A312C2 (modO2Image M₁ K) (modO2Image M₁ J) ∧
    ∃ f : ℕ, 2 ≤ f ∧ (IsPSL 3 2 f ↥(modO2Image M₁ J) ∨ IsSL3 (2 ^ f) ↥(modO2Image M₁ J) ∨
      IsPSp4 2 f ↥(modO2Image M₁ J) ∨ IsG2 2 f ↥(modO2Image M₁ J))

@[expose] def B0KTypeC (M₁ K J : Subgroup G) : Prop :=
  A312C6 (modO2Image M₁ K) (modO2Image M₁ J)

@[expose] def B0KTypeD (M₁ K J : Subgroup G) : Prop :=
  let Kb := modO2Image M₁ K
  let Jb := modO2Image M₁ J
  let OJ : Subgroup (↥M₁ ⧸ CFSG.pCore 2 ↥M₁) := (CFSG.oddCore ↥Jb).map Jb.subtype
  ⁅OJ, Jb⁆ ≠ ⊥ ∧ Jb = Kb ⊔ OJ ∧ ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ IsSL2 p (↥Jb ⧸ CFSG.oddCore ↥Jb)

@[expose] def B0KCases : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I H K M₁ J : Subgroup G) (n m : ℕ),
    B0KConfig G T L I H K M₁ J n m →
      K = J ∨ B0KTypeB M₁ K J ∨ B0KTypeC M₁ K J ∨ B0KTypeD M₁ K J

@[expose] def B0KA7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I H K M₁ J : Subgroup G) (n m : ℕ),
    B0KConfig G T L I H K M₁ J n m → B0KTypeC M₁ K J →
      B0 T L ≤ Subgroup.normalizer (K : Set G)

@[expose] def B0KLie : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I H K M₁ J : Subgroup G) (n m : ℕ),
    B0KConfig G T L I H K M₁ J n m → B0KTypeB M₁ K J →
      B0 T L ≤ Subgroup.normalizer (K : Set G)

@[expose] def B0KNonquasi : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I H K M₁ J : Subgroup G) (n m : ℕ),
    B0KConfig G T L I H K M₁ J n m → B0KTypeD M₁ K J →
      B0 T L ≤ Subgroup.normalizer (K : Set G)

end CFSG.Quasithin.Vol2.Ch10.SecB
