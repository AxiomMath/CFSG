module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiSLOn

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

@[expose] def IsL3Case417 (L A : Subgroup G) : Prop :=
  (∃ (p : ℕ) (_ : Fact p.Prime), 3 < p ∧
    ∃ e : ℕ, 1 ≤ e ∧ (IsSLThreePiAt ↥L (p ^ e) ∨ IsoLThreePi ↥L p e)) ∨
  ((∃ n : ℕ, 0 < n ∧ Even n ∧
      ((Nonempty (L ≃* projSL 3 (GaloisField 2 n)) ∧ IsTypeCOn A L) ∨
        (IsSLThreePiAt ↥L (2 ^ n) ∧ IsTypeCOnSL A L))) ∧
    Nonempty (autIn L A ≃* Equiv.Perm (Fin 3)))

@[expose] def Step430L3 :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → partTwoE G = partTwoF G →
    aschbacherSolvableCore 3 G = ⊥ → ∀ A : Subgroup G, Late.IsE27 A →
    ∀ L : Subgroup G, IsComponent L → ∀ a : G,
      A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers a → orderOf a = 3 →
    ∀ c ∈ A, c ∉ Subgroup.zpowers a → ∀ B : Subgroup G,
      Subgroup.zpowers c ⊔ B = A → Subgroup.zpowers c ⊓ B = ⊥ →
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (B : Set G) →
    ∀ R ∈ invariantPiSubgroups L A (piOf 2), R ≠ ⊥ → ⁅R, Subgroup.zpowers c⁆ = R →
      IsL3Case417 L A →
      (∃ x ∈ A, InducesStdKind L x .field ∨ InducesStdKind L x .graphField) ∨
        Nonempty (L ≃* NativeSporadic.M12) ∨ Nonempty (L ≃* NativeSporadic.J2)

end CFSG.RankThree.PartTwo.Sec4
