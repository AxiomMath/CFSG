module

public import CFSG.Quasithin.Vol2.Ch3Sec3KGSylow
public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.Background.F6SQTK

public section

namespace CFSG.Quasithin.H13

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F6

@[expose] def F618L2Type (W : Type) [Group W] : Prop :=
  (∃ p e : ℕ, p.Prime ∧ 1 ≤ e ∧ e ≤ 2 ∧ IsL2 p e W ∧
      ((e = 1 ∧ (p % 24 = 11 ∨ p % 24 = 13)) ∨ p ^ e % 16 = 7 ∨ p ^ e % 16 = 9 ∨
        (e = 2 ∧ (p % 8 = 3 ∨ p % 8 = 5)))) ∨
    Nonempty (W ≃* ↥(alternatingGroup (Fin 6))) ∨ Nonempty (W ≃* ↥(alternatingGroup (Fin 7))) ∨
    IsM12 W

@[expose] def F618SimpleType (W : Type) [Group W] : Prop :=
  F618L2Type W ∨ ∃ p : ℕ, (p % 8 = 3 ∨ p % 8 = 5) ∧ F6.IsSLEps3 p W

@[expose] def InspA312F618 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (B L : Subgroup Q), B ≤ L →
    (B = L ∨ A312Case B L ∨ A312Nonquasi B L) →
    (∃ (P : Type) (_ : Group P) (W : Type) (_ : Group W) (α : P →* ↥B) (β : P →* W),
      Function.Surjective α ∧ Group.IsSolvable ↥α.ker ∧ Function.Surjective β ∧
        Group.IsSolvable ↥β.ker ∧ IsSimpleGroup W ∧ F618SimpleType W) →
    B ⊔ solvRad L = L ∨
      ∀ (W : Type) [Group W] [Finite W] (f : ↥L →* W), Function.Surjective f →
        f.ker = (solvRad L).subgroupOf L → AutOddNormCent W

@[expose] def FactAutL3Eps : Prop :=
  ∀ (W : Type) [Group W] [Finite W], IsSimpleGroup W →
    ((∃ p : ℕ, F6.IsSLEps3 p W) ∨ ∃ (s : Bool) (p : ℕ), p.Prime ∧ 2 < p ∧ IsPSLEps3 s p 1 W) →
    AutOddNormCent W

@[expose] def FactAutSylowA6 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], (IsAlt 6 Q ∨ IsL2 3 2 Q) → AutSylowSelfNorm Q

@[expose] def FactAutSylowM12 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsM12 Q → AutSylowSelfNorm Q

@[expose] def FactAutOddL2pPlus : Prop :=
  ∀ p : ℕ, p.Prime → (p % 8 = 1 ∨ p % 8 = 7) → ∀ (Q : Type) [Group Q] [Finite Q], IsL2 p 1 Q →
    AutOddNormCent Q

@[expose] def FactL2pSylowFour : Prop :=
  ∀ p : ℕ, p.Prime → (p % 8 = 3 ∨ p % 8 = 5) → ∀ (Q : Type) [Group Q] [Finite Q], IsL2 p 1 Q →
    ∀ S : Subgroup Q, IsSylowTwoOf S ⊤ → Nat.card ↥S = 4

@[expose] def FactAutL2pOuter : Prop :=
  ∀ p : ℕ, p.Prime → 3 < p → (p % 8 = 3 ∨ p % 8 = 5) → ∀ (Q : Type) [Group Q] [Finite Q],
    IsL2 p 1 Q → ∀ A S : Subgroup (MulAut Q), (MulAut.conj : Q →* MulAut Q).range ≤ A →
      A ≠ (MulAut.conj : Q →* MulAut Q).range → IsSylowTwoOf S A →
        Subgroup.normalizer (S : Set (MulAut Q)) ⊓ A ≤ S

end CFSG.Quasithin.H13
