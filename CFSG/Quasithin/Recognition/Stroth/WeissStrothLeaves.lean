module

public import CFSG.Quasithin.Recognition.Stroth.WeissMoufang
public import CFSG.Quasithin.EmptyFaithful.S1421Inputs
public import CFSG.Quasithin.EmptyFaithful.F112HypW
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Recognition.GoldschmidtF112RY9
public import CFSG.Quasithin.Recognition.Stroth.SliceSplit

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R

@[expose] def Str83LocTrans9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (a : ℕ),
    F112HypW L1 L2 S → 1 ≤ a → Nonempty (oTwoQuot ↥L1 ≃* Sz a) → VBig L2 → VL2 L2 →
      IsLocallyTransHat (f112Amalgam L1 L2 S) 9

@[expose] def Str83Orders : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (a : ℕ),
    F112HypW L1 L2 S → 1 ≤ a → Nonempty (oTwoQuot ↥L1 ≃* Sz a) → VBig L2 → VL2 L2 →
      IsL2Quot (2 * a + 1) (oTwoQuot ↥L2) ∧
        Nat.card (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) = (2 ^ (2 * a + 1)) ^ 10 ∧
        Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = (2 ^ (2 * a + 1)) ^ 11 ∧
        Nat.card S = (2 ^ (2 * a + 1)) ^ 12

@[expose] def Str83Kernel : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (a : ℕ),
    F112HypW L1 L2 S → 1 ≤ a → Nonempty (oTwoQuot ↥L1 ≃* Sz a) → VBig L2 → VL2 L2 →
      ¬ IsPGroup 2 ↥(((L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S)).subgroupOf
          (L1 ⊔ bigB L1 L2 S)).normalCore ∧
        ¬ IsPGroup 2 ↥(((L2 ⊔ bigB L1 L2 S) ⊓ (L1 ⊔ bigB L1 L2 S)).subgroupOf
          (L2 ⊔ bigB L1 L2 S)).normalCore

@[expose] def Str83Moufang : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (a : ℕ),
    F112HypW L1 L2 S → 1 ≤ a → Nonempty (oTwoQuot ↥L1 ≃* Sz a) → VBig L2 → VL2 L2 →
      WeissMoufangHat (f112Amalgam L1 L2 S) 8

@[expose] def Str86LocTrans5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
    F112Hyp L1 L2 S → VU3Big L1 → VBig L2 → VL2 L2 →
      IsLocallyTransHat (f112Amalgam L1 L2 S) 5

@[expose] def Str86Orders : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (k : ℕ) (F : Type) [Field F]
    [Finite F], F112Hyp L1 L2 S → 2 ≤ k → Nat.card F = (2 ^ k) ^ 2 →
    (Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F))) → VBig L2 → VL2 L2 →
      IsL2Quot (2 * k) (oTwoQuot ↥L2) ∧
        Nat.card (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) = (2 ^ k) ^ 7 ∧
        Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = (2 ^ k) ^ 8 ∧
        Nat.card S = (2 ^ k) ^ 10

@[expose] def Str86Moufang : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
    F112Hyp L1 L2 S → VU3Big L1 → VBig L2 → VL2 L2 →
      WeissMoufangHat (f112Amalgam L1 L2 S) 4

abbrev Subconst {X : Type} [Group X] (P1 P2 : Subgroup X) : Type :=
  ↥P1 ⧸ ((P1 ⊓ P2).subgroupOf P1).normalCore

@[expose] def HasNormalCopy (Y : Type) [Group Y] (H : Type) [Group H] : Prop :=
  ∃ N : Subgroup Y, N.Normal ∧ Nonempty (↥N ≃* H)

@[expose] def Weiss80Octagon : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (P1 P2 : Subgroup X) (a m : ℕ), 1 ≤ a → 2 ≤ m →
    WeissMoufangHat (RankTwoAmalgam.ofSubgroups P1 P2) 8 →
    ¬ IsPGroup 2 ↥((P1 ⊓ P2).subgroupOf P1).normalCore →
    ¬ IsPGroup 2 ↥((P2 ⊓ P1).subgroupOf P2).normalCore →
    HasNormalCopy (Subconst P1 P2) ↥(Sz a) →
    HasNormalCopy (Subconst P2 P1)
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 m)) →
    (∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P1 = 2 ^ e + 1) →
    (∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P2 = 2 ^ e + 1) →
      m = 2 * a + 1 ∧
        ∃ (D : Type) (_ : Group D), IsTwistedF4Over (2 * a + 1) D ∧ IsExtensionOfLieAmalgam D P1 P2

@[expose] def Weiss80UnitaryQuadrangle : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (P1 P2 : Subgroup X) (k m : ℕ) (F : Type) [Field F]
    [Finite F], 2 ≤ k → 3 ≤ m → Nat.card F = (2 ^ k) ^ 2 → m = 2 * k →
    WeissMoufangHat (RankTwoAmalgam.ofSubgroups P1 P2) 4 →
    HasNormalCopy (Subconst P1 P2) (StatedProj (StatedSU 3 (2 ^ k) F)) →
    HasNormalCopy (Subconst P2 P1)
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 m)) →
    (∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P1 = 2 ^ e + 1) →
    (∃ e : ℕ, 1 ≤ e ∧ (P1 ⊓ P2).relIndex P2 = 2 ^ e + 1) →
      ∃ (D : Type) (_ : Group D), IsLieOverTwo .PSU 5 k D ∧ IsExtensionOfLieAmalgam D P1 P2

end CFSG.Quasithin.Stroth
