module

public import CFSG.RankThree.PartTwo.Sec11.Item119

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)

@[expose] def IsList119 (X : Type) [Group X] : Prop :=
  (∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.G2 q).Valid),
      Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)) ∨
    (∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
      Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) ∨
    (∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧
      ((p ^ e % 3 = 1 ∧ Nonempty (X ≃* projSL 3 (GaloisField p e))) ∨
        (p ^ e % 3 = 2 ∧ Nonempty (X ≃* projSU 3 p e)))) ∨
    (∃ (π : Bool) (p f : ℕ) (K : Type) (_ : Field K), Sec4.PiField π p f K ∧
      Sec4.ModThree π (p ^ f) ∧ Nonempty (X ≃* projImage (Sec4.glPi π 3 (p ^ f) K))) ∨
    Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M24) ∨
    Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.He)

@[expose] def CentBound119 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y K : Subgroup G) (c t : G),
    (∃ (X : Type) (_ : Group X), IsList119 X ∧
      Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* _root_.commutator X)) →
    c ∈ Subgroup.normalizer (Y : Set G) → c ^ 3 = 1 →
    K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({c} : Set G)) →
    IsType424 (K ⧸ aschbacherSolvableCore 3 K) →
    t ∈ Subgroup.normalizer (Y : Set G) → (∃ k : ℕ, t ^ 3 ^ k = 1) → t * c = c * t →
    (∀ k ∈ K, t * k * t⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) K) →
      t ^ (3 ^ (Nat.card K).factorization 3) ∈ Sec4.thetaQuotCentralizer Y

end CFSG.RankThree.PartTwo.Sec11
