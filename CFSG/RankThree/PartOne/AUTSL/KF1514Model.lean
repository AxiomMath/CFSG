module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.RankThree.PartOne.S12.PushingUp

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory

namespace AUTSL

abbrev OmegaMinusModel (f : ℕ) (b c : GaloisField 2 f) : Type :=
  ↥(projOmegaMinus 3 (GaloisField 2 f) b c)

@[expose] def ModelCong (r p f : ℕ) : Prop :=
  match r with
  | 3 => p ∣ 2 ^ f - 1
  | 4 => p ∣ 2 ^ f + 1
  | _ => False

@[expose] def KF1514PModel (r : ℕ) : Prop :=
  ∀ (p f : ℕ) (b c : GaloisField 2 f), p.Prime → 5 ≤ p → 1 ≤ f → ModelCong r p f →
    (∀ s : GaloisField 2 f, s ^ 2 + b * s + c ≠ 0) →
    ∀ U A₀ : Subgroup (OmegaMinusModel f b c),
      IsSylowOf 2 U ⊤ → IsElementaryAbelian p ↥A₀ → Nat.card ↥A₀ = p ^ 3 →
      (∃ h : OmegaMinusModel f b c, ∃ B : Subgroup (OmegaMinusModel f b c), B ≤ A₀ ∧
        Nat.card ↥A₀ ≤ p * Nat.card ↥B ∧
        B.map (MulAut.conj h).toMonoidHom ≤ Subgroup.normalizer (pushingUpS U : Set _)) ∧
      (∃ x ∈ omegaOneCenterIn U, x ≠ 1 ∧
        ∃ h : OmegaMinusModel f b c, ∃ B : Subgroup (OmegaMinusModel f b c), B ≤ A₀ ∧
        Nat.card ↥A₀ ≤ p * Nat.card ↥B ∧
        B.map (MulAut.conj h).toMonoidHom ≤ Subgroup.centralizer ({x} : Set _))

end AUTSL

end CFSG.RankThree.PartOne
