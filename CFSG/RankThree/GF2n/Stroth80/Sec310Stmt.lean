module

public import CFSG.RankThree.GF2n.Stroth80.Sec5Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def OmegaPlusFourNat (hc : Ctx M Q Z B) (t : G) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = Nat.card Z ∧
    NaturalRep (ι := Fin 2 ⊕ Fin 2) K (StatedOmega (StatedQuadPlus 2 K)) (Rt M (LB M Q B) t)
      (Vt M (LB M Q B) B Z t) Z (hc.CN t)

@[expose] def SympRep (k : ℕ) (hc : Ctx M Q Z B) (t : G) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = Nat.card Z ∧ ∃ m : ℕ, k ≤ m ∧
    ∃ φ : ↥(Rt M (LB M Q B) t) →* GL (Fin m ⊕ Fin m) K,
      φ.range ≤ StatedSp m K ∧ φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t) ∧
      SectionAct K (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z φ
        (fun g => (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K))

@[expose] def NatIrred {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (X : Subgroup (GL ι K)) : Prop :=
  ∀ S : Submodule K (ι → K), (∀ g ∈ X, ∀ x ∈ S, (g : Matrix ι ι K) *ᵥ x ∈ S) → S = ⊥ ∨ S = ⊤

@[expose] def GenByTransvLines {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (X : Subgroup (GL ι K)) : Prop :=
  X = Subgroup.closure {g : GL ι K | ∃ v f : ι → K, v ≠ 0 ∧ f ≠ 0 ∧ f ⬝ᵥ v = 0 ∧
    (g : Matrix ι ι K) = 1 + Matrix.vecMulVec v f ∧
    ∀ c : K, ∃ h ∈ X, (h : Matrix ι ι K) = 1 + c • Matrix.vecMulVec v f}

@[expose] def McLaughlinStatement : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (ι : Type) [Fintype ι] [DecidableEq ι]
    (X : Subgroup (GL ι K)), 2 ≤ Fintype.card ι → 4 ≤ Nat.card K → NatIrred X →
    GenByTransvLines X →
      X = CFSG.MatrixModel.slCore ι K ∨
        ∃ β : LinearMap.BilinForm K (ι → K), β.Nondegenerate ∧ (∀ x, β x x = 0) ∧
          ∀ g : GL ι K, g ∈ X ↔ ∀ x y, β ((g : Matrix ι ι K) *ᵥ x) ((g : Matrix ι ι K) *ᵥ y) = β x y

@[expose] def Stroth310SLTransvStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec5Hyp hc n t → Rt M (LB M Q B) t ≠ LB M Q B → Vt M (LB M Q B) B Z t ≤ QB B →
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = Nat.card Z ∧
        ∃ m : ℕ, 2 ≤ m ∧ ∃ φ : ↥(Rt M (LB M Q B) t) →* GL (Fin m) K,
          φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t) ∧
          SectionAct K (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z φ
            (fun g => (g : Matrix (Fin m) (Fin m) K)) ∧
          NatIrred φ.range ∧ GenByTransvLines φ.range ∧
          (∃ u : Fin m → K, u ≠ 0 ∧ ∀ l : ↥(Rt M (LB M Q B) t), (l : G) ∈ LB M Q B →
            ∀ x, ∃ c : K, (φ l : Matrix (Fin m) (Fin m) K) *ᵥ x - x = c • u) ∧
          Nat.card K ^ (m - 1) ≤
            Nat.card ↥(((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ)

@[expose] def Stroth310SLBranchStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec5Hyp hc n t → Rt M (LB M Q B) t ≠ LB M Q B → Vt M (LB M Q B) B Z t ≤ QB B → SLNat hc t

@[expose] def Stroth310SympFormStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec5Hyp hc n t → Rt M (LB M Q B) t ≠ LB M Q B → ¬ Vt M (LB M Q B) B Z t ≤ QB B →
      SympRep 1 hc t

@[expose] def Stroth310ClassifyStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec5Hyp hc n t → Rt M (LB M Q B) t ≠ LB M Q B → ¬ Vt M (LB M Q B) B Z t ≤ QB B →
      SympRep 2 hc t → SpNat hc t ∨ OmegaNat hc t ∨ OmegaPlusFourNat hc t

@[expose] def Stroth310SympBranchStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec5Hyp hc n t → Rt M (LB M Q B) t ≠ LB M Q B → ¬ Vt M (LB M Q B) B Z t ≤ QB B →
      SpNat hc t ∨ OmegaNat hc t ∨ OmegaPlusFourNat hc t

end CFSG.RankThree.GF2n.Stroth80
