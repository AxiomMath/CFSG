module

public import CFSG.RankThree.PartTwo.Sec4.StatementsComponents

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def IsHeisSLThreeFour (X : Type) [Group X] : Prop :=
  ∃ U V : Subgroup X, U ⊔ V = ⊤ ∧ (∀ u ∈ U, ∀ v ∈ V, u * v = v * u) ∧ IsHeisThree U ∧
    Nonempty (V ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) ∧
    Nat.card (U ⊓ V : Subgroup X) = 3

@[expose] def IsZ3L34OrHeisSL34 (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* Multiplicative (ZMod 3) × projSL 3 (GaloisField 2 2)) ∨ IsHeisSLThreeFour X

@[expose] def IsLieTypeSimple (X : Type) [Group X] : Prop :=
  ∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ), Blueprint.LieModel X t n p f

noncomputable abbrev starQuot (G : Type) [Group G] : G →* G ⧸ CFSG.pPrimeCore 3 G :=
  QuotientGroup.mk' (CFSG.pPrimeCore 3 G)

@[expose] def Concl434 {G : Type} [Group G] [Finite G] (A Q : Subgroup G) : Prop :=
  IsZ3L34OrHeisSL34 (A ⊔ layer G : Subgroup G) ∧ Nat.card Q = 2 ∧
    ∀ q ∈ Q, q ≠ 1 → InducesStdKind (layer G) q .graphField

@[expose] def Item4_34 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M Q : Subgroup G), Ctx434 G A M Q → Concl434 A Q

@[expose] def Concl4442 {G : Type} [Group G] [Finite G] (A M H : Subgroup G) (s : G) : Prop :=
  s ∈ CFSG.Open.pCoreOf 2 (H ⊓ M) ∧ s ∈ Subgroup.centralizer (A : Set G) ∧
    InducesStdKind (inSubgroup perfectResidual H) s .graphField ∧
    ∃ hs : s ∈ H, ∃ X : Subgroup (H ⧸ CFSG.pCore 2 H), X.Normal ∧ IsZ3L34OrHeisSL34 X ∧
      X ⊔ Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 H) (⟨s, hs⟩ : H)) = ⊤ ∧
      QuotientGroup.mk' (CFSG.pCore 2 H) (⟨s, hs⟩ : H) ∉ X

@[expose] def Item4_44_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M : Subgroup G), Ctx444 G A M → ⊤ ∈ Late.scriptH₀ A M →
    ∃ s : G, Concl4442 A M ⊤ s

@[expose] def Concl4443 {G : Type} [Group G] [Finite G] (M H : Subgroup G) : Prop :=
  ∃ L ∈ oTwoComponents G, ¬ L ≤ M ∧
    (L = inSubgroup perfectResidual H ⊔ inSubgroup (CFSG.pCore 2) L ∨
      (Nonempty (inSubgroup perfectResidual H ⧸ CFSG.pCore 2 (inSubgroup perfectResidual H) ≃*
          projSL 3 (GaloisField 2 2)) ∧
        ∃ J ∈ oTwoComponents G, ⁅inSubgroup perfectResidual H, ⊤⁆ = L ⊔ J ∧
          Nonempty (L ⧸ CFSG.pCore 2 L ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) ∧
          ((∃ n : ℕ, 1 ≤ n ∧ Nonempty (J ⧸ CFSG.pCore 2 J ≃*
              Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 (2 * n)))) ∨
            IsExtOf (J ⧸ CFSG.pCore 2 J) Blueprint.NativeSporadic.M22 (Multiplicative (ZMod 3)))))

theorem item4_44_3_iff : Item4_44_3 ↔ ∀ (G : Type) [Group G] [Finite G] (A M : Subgroup G),
    Ctx444 G A M → ∀ H ∈ Late.scriptH₀ A M, Concl4443 M H :=
  Iff.rfl

structure Ctx4443 (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (s : G) : Prop where
  ctx444 : Ctx444 G A M
  mem_scriptH₀ : H ∈ Late.scriptH₀ A M
  concl4442 : Concl4442 A M H s

structure Choice450 {G : Type} [Group G] [Finite G] (M H : Subgroup G) (s : G) (L : Subgroup G) :
    Prop where
  mem : L ∈ thetaComponents 3 G
  mem_normalizer : s ∈ Subgroup.normalizer (L : Set G)
  commutator_eq : ⁅L, Subgroup.zpowers s⁆ = L
  not_le : ¬ L ≤ M
  commutator_eq_perfectResidual : ⁅L, inSubgroup perfectResidual H⁆ = L

@[expose] def Concl451 {G : Type} [Group G] [Finite G] (A Q L : Subgroup G) : Prop :=
  IsZ3L34OrHeisSL34 ((A ⊔ L).map (starQuot G)) ∧
    (Subgroup.centralizer (L.map (starQuot G) : Set (G ⧸ CFSG.pPrimeCore 3 G))).relIndex
      (Q.map (starQuot G)) = 2 ∧
    ∀ q ∈ Q.map (starQuot G),
      q ∉ Subgroup.centralizer (L.map (starQuot G) : Set (G ⧸ CFSG.pPrimeCore 3 G)) →
      InducesStdKind (L.map (starQuot G)) q .graphField

@[expose] def Item4_49 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (s : G), Ctx4443 G A M H s →
    (inSubgroup perfectResidual H).map (starQuot G) ≤ layer (G ⧸ CFSG.pPrimeCore 3 G)

@[expose] def Item4_50_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (s : G), Ctx4443 G A M H s →
    ∃ L : Subgroup G, Choice450 M H s L

structure Ctx461 (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (s : G) (L : Subgroup G) :
    Prop where
  ctx4443 : Ctx4443 G A M H s
  choice450 : Choice450 M H s L
  not_concl4443 : ¬ Concl4443 M H
  layer_eq : layer (G ⧸ CFSG.pPrimeCore 3 G) =
    ⁅layer (G ⧸ CFSG.pPrimeCore 3 G), (inSubgroup perfectResidual H).map (starQuot G)⁆

structure Ctx457 (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (s : G) (L J : Subgroup G) :
    Prop extends Ctx461 G A M H s L where
  mem : J ∈ thetaComponents 3 G
  not_le : ¬ J.map (starQuot G) ≤ L.map (starQuot G)

@[expose] def Item4_57 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (s : G) (L J : Subgroup G),
    Ctx457 G A M H s L J → ¬ IsSimpleGroup (J.map (starQuot G))

@[expose] def Item4_60 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (s : G) (L J : Subgroup G),
    Ctx457 G A M H s L J → J ∈ oTwoComponents G

end CFSG.RankThree.PartTwo.Sec4
