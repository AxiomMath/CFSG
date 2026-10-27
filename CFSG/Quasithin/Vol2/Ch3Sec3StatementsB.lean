module

public import CFSG.Quasithin.Vol2.Ch3Sec3Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open scoped IsMulCommutative Pointwise

variable {G : Type} [Group G]

@[expose] def permQuot6Model : FFModel where
  Gam := Equiv.Perm (Fin 6)
  Amb := G6.PermMod 6
  act σ x := G6.permAct 6 σ x
  sec := ⊤
  ker := Subgroup.zpowers (G6.allOnes 6)

@[expose] def sylowS6 : Subgroup (Equiv.Perm (Fin 6)) :=
  Subgroup.closure {Equiv.swap 0 1, Equiv.swap 0 2 * Equiv.swap 1 3, Equiv.swap 4 5}

@[expose] def aBar2 : Subgroup (Equiv.Perm (Fin 6)) :=
  Subgroup.closure {Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 4 5}

@[expose] noncomputable def preimageAut (T V : Subgroup G) (A : Subgroup (MulAut ↥V)) :
    Subgroup G :=
  T ⊓ (A.comap (conjAct V)).map (Subgroup.normalizer (V : Set G)).subtype

@[expose] def Stmt3_3_16 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    ∀ (n : ℕ) (K : Type) [Field K] [Finite K], 1 < n → Nat.card K = 2 ^ n →
      IsEmpty (↥(autOn L (vPlus L T)) ≃* ↥(StatedSL 3 K)) ∧
      IsEmpty (↥(autOn L (vPlus L T)) ≃* ↥(StatedSp 2 K)) ∧
      IsEmpty (↥(autOn L (vPlus L T)) ≃* ↥(quasithinG2 K))

@[expose] def Stmt3_3_17 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    Nonempty (↥(autOn L (vPlus L T)) ≃* alternatingGroup (Fin 7)) →
      Nat.card ↥⁅vPlus L T, L⁆ = 2 ^ 6

@[expose] def Stmt3_3_18 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    ∀ n : ℕ, (n = 4 ∨ n = 5) →
      Nonempty (↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) →
        ∃ _ : IsMulCommutative ↥(vPlus L T), ¬ ∃ k : ℕ, 1 ≤ k ∧
          DirectSumOfCopies (autOn L (vPlus L T)) (commVPlus L T L) ⊥
            (FFModel.nat (StatedSL n (ZMod 2))) k

@[expose] def Stmt3_3_19 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    IsEmpty (↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))

@[expose] def Stmt3_3_20 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D X : Subgroup G), Hyp331 G T M L D →
    oTwoUpper X = X → T ≤ Subgroup.normalizer (X : Set G) →
    Nonempty (↥(X ⊔ T) ⧸ CFSG.pCore 2 ↥(X ⊔ T) ≃* Equiv.Perm (Fin 3)) →
    ¬ D ≤ Subgroup.normalizer (pCoreOf 2 (X ⊔ T) : Set G) →
      (InH T (X ⊔ T ⊔ D) ∧ X ⊔ T ⊔ D ≤ Subgroup.normalizer (conjClosure X D : Set G) ∧
        X ⊔ T ⊔ D = conjClosure X D ⊔ T ⊔ D) ∧
      (∃ p : ℕ, p.Prime ∧ (p % 24 = 11 ∨ p % 24 = 13) ∧
        IsPSL 2 p 1 (↥(conjClosure X D ⊔ T) ⧸ CFSG.pCore 2 ↥(conjClosure X D ⊔ T))) ∧
      (pCoreOf 2 X ≤ pCoreOf 2 (conjClosure X D) ∧
        (∃ _ : ((pCoreOf 2 (conjClosure X D ⊔ T)).subgroupOf (X ⊔ T)).Normal,
          Nonempty (↥(X ⊔ T) ⧸ (pCoreOf 2 (conjClosure X D ⊔ T)).subgroupOf (X ⊔ T) ≃*
            DihedralGroup 6)) ∧
        (D ⊓ Subgroup.normalizer (X : Set G)).relIndex D = 3) ∧
      HasNoncentralTwoChief X 3 ∧
      (¬ HasNoncentralTwoChief X 5 →
        (HasNoncentralTwoChief (conjClosure X D) 1 ∧ ¬ HasNoncentralTwoChief (conjClosure X D) 2 ∧
          (∀ A B : Subgroup G, IsTwoChiefFactor (conjClosure X D) A B →
            ¬ ⁅A, conjClosure X D⁆ ≤ B → 2 ^ 10 ≤ B.relIndex A) ∧
          2 ^ 12 ≤ Nat.card T) ∧
        (frattini ↥(pCoreOf 2 X)).map (pCoreOf 2 X).subtype ≤
          (Subgroup.center ↥(conjClosure X D)).map (conjClosure X D).subtype ∧
        (Subgroup.center ↥(conjClosure X D ⊔ T) ≠ ⊥ → 2 ^ 12 < Nat.card T))

@[expose] def Stmt3_3_21 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    IsEmpty (↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))

@[expose] def Stmt3_3_22 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    IsEmpty (↥(autOn L (vPlus L T)) ≃* alternatingGroup (Fin 7))

@[expose] def Stmt3_3_23 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    IsPSL 3 2 1 ↥(autOn L (vPlus L T)) →
      (IsLnBlock L 3 ∧ D ≤ Subgroup.normalizer (preCenterAut T (vPlus L T) : Set G)) ∨
      ((HasNoncentralTwoChief L 2 ∧ ¬ HasNoncentralTwoChief L 4) ∧
        ¬ D ≤ Subgroup.normalizer (pCoreOf 2
          (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊔ T) : Set G))

@[expose] def Stmt3_3_24 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    IsAltBlockType L 6 ∨ IsHatA6Block L ∨ IsG2Block L ∨ IsLnBlock L 3

@[expose] def Stmt3_3_25 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    (IsAltBlockType L 6 ∨ IsG2Block L ∨ IsLnBlock L 3) ∧
    (tC L T ≠ ⊥ → ¬ IsPSL 3 2 1 ↥(autOn L (vPlus L T)) →
      D ≤ Subgroup.normalizer
          (oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) : Set G) ∧
      D ≤ Subgroup.normalizer (pCoreOf 2
          (oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ⊔ T) : Set G) ∧
      ∀ R₀ : Subgroup G, R₀ ≠ ⊥ → R₀ ≤ pCoreOf 2
          (oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ⊔ T) →
        L ⊔ T ≤ Subgroup.normalizer (R₀ : Set G) → ¬ D ≤ Subgroup.normalizer (R₀ : Set G)) ∧
    (tC L T = ⊥ → vPlus L T = qL L T ∨ IsAltBlockType L 6)

@[expose] def Stmt3_3_26 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    ∃ d ∈ D, d ∉ M ∧ ¬ CFSG.conjugate (vPlus L T) d ≤ qL L T

@[expose] def Stmt3_3_27 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    ∀ d ∈ D, d ∉ M → ¬ CFSG.conjugate (vPlus L T) d ≤ qL L T → tC L T ≠ ⊥ →
      tC L T ⊓ CFSG.conjugate (tC L T) d = ⊥ ∧ frattini ↥(tC L T) = ⊥ ∧
        (CFSG.conjugate (tC L T) d ≤ qL L T ∨ tC L T ≤ CFSG.conjugate (qL L T) d)

@[expose] def Stmt3_3_29 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    ¬ IsPSL 3 2 1 ↥(autOn L (vPlus L T))

@[expose] def Stmt3_3_30 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    IsAltBlockType L 6

@[expose] def Stmt3_3_31 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D → tC L T = ⊥

@[expose] def Stmt3_3_32 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    ((qL L T = vPlus L T ∧ ∃ _ : IsMulCommutative ↥(vPlus L T),
        XMod.IsIrrSec ↥(autOn L (vPlus L T)) (⊥ : Subgroup ↥(vPlus L T)) ⊤) ∨
      (∃ _ : IsMulCommutative ↥(qL L T), Nat.card ↥(qL L T) = 2 ^ 5 ∧
        permQuot6Model.Realizes (autOn (L ⊔ T) (qL L T)) ⊤ ⊥)) ∧
    Nonempty (↥(autOn (L ⊔ T) (vPlus L T)) ≃* Equiv.Perm (Fin 6)) ∧
    ∃ φ : ↥(autOn (L ⊔ T) (vPlus L T)) ≃* Equiv.Perm (Fin 6),
      ((autOn T (vPlus L T)).subgroupOf (autOn (L ⊔ T) (vPlus L T))).map φ.toMonoidHom = sylowS6 ∧
      D ≤ Subgroup.normalizer (preimageAut T (vPlus L T)
        ((aBar2.map φ.symm.toMonoidHom).map (autOn (L ⊔ T) (vPlus L T)).subtype) : Set G)

@[expose] def Stmt3_3_Close : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D → False

theorem stmt3_3_1A_of_close (h : Stmt3_3_Close) : Stmt3_3_1A :=
  stmt3_3_1A_of_false h

end CFSG.Quasithin.H13
