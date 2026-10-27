module

public import CFSG.RankThree.PartTwo.Sec16.Notation
public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
public import CFSG.RankThree.PartTwo.Sec15.HypR
public import CFSG.RankThree.PartTwo.Sec15.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec16
  CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Item171 (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y₀ ∈ scriptY0Star A LB, ∀ B : Subgroup G, IsHyperplane A B →
    Y₀ ≤ ⨆ (b : G) (_ : b ∈ B) (_ : b ≠ 1),
      ⁅pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)), A⁆ ⊔
        oPrimeResidualOf 3 (delta A LB (Subgroup.centralizer ({b} : Set G)))

@[expose] def Item172 (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y₀ ∈ scriptY0Star A LB, ∃ Q ∈ scriptQ A LB, ¬ Q ≤ Subgroup.normalizer (Y₀ : Set G)

@[expose] noncomputable def Item174 (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ X : Subgroup G, X = delta A LB X → ¬ 3 ∣ Nat.card X → Group.IsSolvable ↥X

@[expose] def Item175 (A : Subgroup G) (c : G) : Prop :=
  omegaA A = {Subgroup.zpowers c} →
    ∀ g : G, (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom ≤
        Subgroup.normalizer (Subgroup.zpowers c : Set G) →
      (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers c

@[expose] noncomputable def Item176 (A : Subgroup G) (LB : Subgroup G → Subgroup G) (c : G)
    (L : Subgroup G) : Prop :=
  omegaA A = {Subgroup.zpowers c} →
    (∀ K : Subgroup G, K ≠ ⊤ → c ∈ K → CFSG.Open.pRank 3 (normalClosureIn K c) = 1) ∧
      (∀ Q ∈ scriptQ A LB,
        Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
        ∀ d ∈ A, d ≠ 1 → IsThreeCentralIn L d →
        ∀ r ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
            Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G),
          Q.map (MulAut.conj r).toMonoidHom ∈ invariantPiSubgroups ⊤ A (piCompl 3) →
            Q.map (MulAut.conj r).toMonoidHom ∈ scriptQ A LB)

@[expose] noncomputable def Item177 (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y₀ ∈ scriptY0Star A LB, ∀ V : Subgroup G,
    Maximal (fun V : Subgroup G => V ≤ Subgroup.normalizer (Y₀ : Set G) ∧
      Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (V : Set G) ∧
      CFSG.Assembly.IsElemAbelian 2 V) V →
    ⁅Y₀ ⊔ A, V⁆ ≠ ⊥ ∧ ∃ U ∈ fourGroupsMinus A, U ∈ scriptQPi A LB V (piOf 2)

@[expose] def Item179 (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y₀ ∈ scriptY0Star A LB,
    (∃ U ∈ fourGroupsMinus A,
      U ∈ collectionIn (scriptQ A LB)
        (CFSG.Open.pCoreOf 2 (Subgroup.normalizer (Y₀ : Set G)))) ∧
    ∀ U ∈ fourGroupsMinus A,
      U ∈ collectionIn (scriptQ A LB) (CFSG.Open.pCoreOf 2 (Subgroup.normalizer (Y₀ : Set G))) →
        ∀ Y ∈ scriptY3Star A LB, U ≤ CFSG.Open.pCoreOf 2 Y

@[expose] noncomputable def Item1710 (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y₀ ∈ scriptY0Star A LB, ∀ Y : Subgroup G,
    Y = inSubgroup (oResidual 2) (deltaZero A LB Y) → ¬ Y ≤ Subgroup.normalizer (Y₀ : Set G) →
      ∀ Y₁ ∈ scriptY3Star A LB, ∀ Y₂ ∈ scriptY3Star A LB, Y ≤ Y₁ → Y ≤ Y₂ → Y₁ = Y₂

@[expose] noncomputable def Item1711 (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y₀ ∈ scriptY0Star A LB, ∀ a ∈ A, a ≠ 1 → ∀ Y ∈ scriptY3Star A LB,
    delta A LB (Subgroup.centralizer ({a} : Set G)) ≤ Y →
    ∀ b ∈ A, b ≠ 1 → ∀ U ∈ fourGroups A, U = ⁅U, Subgroup.zpowers a⁆ →
      U ∈ collectionIn (scriptQ A LB)
        (CFSG.Open.pCoreOf 2 (Subgroup.normalizer (Y₀ : Set G)) ⊓
          Subgroup.centralizer ({b} : Set G)) →
        delta A LB (Subgroup.centralizer ({b} : Set G)) ∈ scriptY3 A LB

@[expose] noncomputable def Item1712 (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∃ B : Subgroup G, IsHyperplane A B ∧
    (∀ b ∈ B, b ≠ 1 → delta A LB (Subgroup.centralizer ({b} : Set G)) ∈ scriptY3 A LB) ∧
    ∃ a ∈ A, a ∉ B ∧ ∃ Y ∈ scriptY3 A LB, delta A LB (Subgroup.centralizer ({a} : Set G)) ≤ Y

@[expose] def Item1713 (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y₀ ∈ scriptY0Star A LB, ∃ Y ∈ scriptY3 A LB, ¬ Y ≤ Subgroup.normalizer (Y₀ : Set G)

@[expose] noncomputable def Item1714 (L : Subgroup G) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ¬ Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 n

@[expose] def Item1730 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → partTwoS G = ∅ →
    ∀ A ∈ partTwoE G, A ∉ partTwoT G → ∀ c : G, Subgroup.zpowers c ∈ omegaA A →
      ∀ L ∈ lA A c,
        ¬ HypR A ∧ IsEmpty (↥L ⧸ CFSG.pCore 2 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)

end CFSG.RankThree.PartTwo.Sec17
