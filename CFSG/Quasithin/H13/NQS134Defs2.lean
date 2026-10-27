module

public import CFSG.Quasithin.H13.A6Producer134
public import CFSG.Quasithin.H13.A6Inputs13_3
public import CFSG.Quasithin.H13.U3S134Defs

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G]

@[expose] def wt6 (x : ↥(G6.coreMod 6)) : ℕ :=
  (Finset.univ.filter fun i : Fin 6 => Multiplicative.toAdd (x : G6.PermMod 6) i = 1).card

@[expose] noncomputable def wt [Finite G] {T L V : Subgroup G} (S : A6.Setting134 G T L V)
    (v : ↥V) : ℕ :=
  wt6 (S.frame.ψ v)

@[expose] def HasWtIn (K W : Subgroup G) (w : G) (k : ℕ) : Prop :=
  ∃ (R : A6.RawData6 K W) (hw : w ∈ W), wt6 (R.ψ ⟨w, hw⟩) = k

@[expose] noncomputable def h0Of [Finite G] {T L V : Subgroup G} (S : A6.Setting134 G T L V)
    (H₂ : Subgroup G) : Subgroup G :=
  (U3.l2Of S ⊔ T) ⊔ H₂

@[expose] def IsNat13410 (K W : Subgroup G) : Prop :=
  ∃ _ : IsMulCommutative ↥W,
    BinaryNaturalSL (V := ↥W) (autOn K W) ⊤ ⊥ 3 1 ∨ AlternatingNatural (V := ↥W) (autOn K W) ⊤ ⊥ 6

@[expose] def IsCore5 (K W : Subgroup G) : Prop :=
  ∃ _ : IsMulCommutative ↥W, Nat.card W = 2 ^ 5 ∧
    FFModel.Realizes (V := ↥W) (H13.altCoreModel 6) (autOn K W) ⊤ ⊥

structure NZ134 (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (z : G) where
  S : A6.Setting134 G T L V
  zV1 : z ∈ fsuV1 T V
  zL : z ∉ centralizer (L : Set G)
  zM : ¬ centralizer ({z} : Set G) ≤ normalizer (L : Set G)
  nsolv : ¬ Group.IsSolvable ↥(centralizer ({z} : Set G))

@[expose] def Stmt13_4_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (_ : A6.Setting134 G T L V) (z : G)
    (H : Subgroup G), z ∈ fsuV1 T V → z ∉ centralizer (L : Set G) → U3.InHz T L V z H →
    ¬ Group.IsSolvable ↥H →
    (∃ K : Subgroup G, K ∈ cComp H) ∧
    (∀ K ∈ cComp H,
      (quasithinIsMaximalLocal T K ∧ quasithinIsFaithfulLocal T K) ∧ H ≤ normalizer (K : Set G) ∧
      ¬ K ≤ normalizer (L : Set G) ∧ ¬ L ≤ normalizer (K : Set G) ∧
      ¬ K ≤ centralizer ((V ⊓ centralizer (L : Set G) : Subgroup G) : Set G) ∧
      K ≤ centralizer ({z} : Set G) ∧ centralizer ({z} : Set G) ≤ normalizer (K : Set G) ∧
      ⁅K, thompsonJ T⁆ = K) ∧
    (normalizer (L : Set G) = L ⊔ T ∨
      (A6.IsHatA6 L ∧ ∃ X : Subgroup G, IsCyclic ↥X ∧
        IsSylowIn 3 X (normalizer (L : Set G) ⊓ centralizer (V : Set G)) ∧
        normalizer (L : Set G) = (L ⊔ X) ⊔ T))

@[expose] def Stmt13_4_12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (z : G), NZ134 G T L V z →
    (quasithinOmegaOneCenter T = fsuV1 T V ∧ Nat.card ↥(quasithinOmegaOneCenter T) = 4 ∧
      ∀ z' ∈ quasithinOmegaOneCenter T, z' ≠ 1 →
        ¬ centralizer ({z'} : Set G) ≤ normalizer (L : Set G) → z' = z) ∧
    ∃ H₂ : Subgroup G, IsHStar T (normalizer (L : Set G)) H₂ ∧ H₂ ≤ centralizer ({z} : Set G) ∧
      ∀ X : Subgroup G, IsHStar T (normalizer (L : Set G)) X →
        X ≤ centralizer ({z} : Set G) → X = H₂

@[expose] def StmtEnd134 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (z : G), NZ134 G T L V z → False

theorem stmt13_4_10_17_of (h1332 : Stmt13_3_2) (hEnd : StmtEnd134) : A6.Stmt13_4_10_17 := by
  intro G _ _ T L V z h13 hirr hzv hz hzL hzM
  by_contra hns
  exact hEnd G T L V z
    { S := Classical.choice (A6.exists_setting134 h1332 h13 hirr hzv)
      zV1 := hz
      zL := hzL
      zM := hzM
      nsolv := hns }

end CFSG.Quasithin.H13.NQS134
