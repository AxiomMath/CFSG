module

public import CFSG.RankThree.PartTwo.Sec4.Statements423
public import CFSG.RankThree.PartTwo.Sec8.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)

@[expose] def IsList424 (X : Type) [Group X] : Prop :=
  (∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.G2 q).Valid),
      Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)) ∨
    (∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
      Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) ∨
    (∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧
      ((p ^ e % 3 = 1 ∧ Nonempty (X ≃* projSL 3 (GaloisField p e))) ∨
        (p ^ e % 3 = 2 ∧ Nonempty (X ≃* projSU 3 p e)))) ∨
    (∃ (π : Bool) (p f : ℕ) (K : Type) (_ : Field K), PiField π p f K ∧
      ModThree π (p ^ f) ∧ Nonempty (X ≃* projImage (glPi π 3 (p ^ f) K))) ∨
    Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M24) ∨
    Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.He)

@[expose] def Item4_24Used : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → ∀ A : Subgroup G,
    Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A → Nat.card A = 27 →
    partTwoE G = partTwoF G →
    ∀ L ∈ thetaComponents 3 G, ∀ a : G, orderOf a = 3 → a ∈ Subgroup.center G →
    Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers a : Set G) →
    ∀ c ∈ A, c ∉ Subgroup.zpowers a →
    ∀ K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer ({c} : Set G)),
      ((∃ n : ℕ, 1 ≤ n ∧
          Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* projSL 2 (GaloisField 2 n))) ∨
        (∃ (p n : ℕ) (_ : Fact p.Prime), 3 < p ∧ 1 ≤ n ∧
          Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* projSL 2 (GaloisField p n))) ∨
        ∃ n : ℕ, 1 ≤ n ∧ Sec8.IsoLThreeMinusPi (K ⧸ aschbacherSolvableCore 3 K) 2 n) →
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer ((A ⊓ K : Subgroup G) : Set G) →
        (Nonempty (autIn L A ≃* Equiv.Perm (Fin 3)) ∨
            Nonempty (autIn L A ≃* DihedralGroup 6)) ∧
          (KFacts.InducesStdKind L c .field ∨
            ∃ (X : Type) (_ : Group X), IsList424 X ∧
              Nonempty (thetaImage (L ⊔ A) ≃* Multiplicative (ZMod 3) × X))

end CFSG.RankThree.PartTwo.Sec4
