module

public import CFSG.RankThree.PartTwo.Sec18.Statements
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.Foundations

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

@[expose] def Hyp201One (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) : Prop :=
  Hyp201 G A M L N c ∧
    ∃ H ∈ scriptHStar A M, CFSG.Open.pCoreOf 2 H ≠ ⊥ ∧ L = inSubgroup perfectResidual H ∧
      N = Subgroup.normalizer (L : Set G) ∧
      (CFSG.Open.pCoreOf 2 (Subgroup.centralizer {c}) ≠ ⊥ →
        Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤ N)

@[expose] def Item201Contra1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G), ¬ Hyp201One G A M L N c

noncomputable abbrev kTwenty {G : Type} [Group G] (M : Subgroup G) (c : G) : Subgroup G :=
  normalClosureIn M c

noncomputable abbrev zTwenty {G : Type} [Group G] (T : Subgroup G) : Subgroup G :=
  Sec18.fourChar T 0

noncomputable abbrev vTwenty {G : Type} [Group G] (M : Subgroup G) (c : G) (T : Subgroup G) :
    Subgroup G :=
  ⁅zTwenty T, kTwenty M c⁆

structure Ctx20 (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G)
    (T : Subgroup G) : Prop extends Hyp201 G A M L N c where
  sylow : CFSG.ABGLocalTools.IsSylowOf 2 T M
  sylow_centralizer : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ Subgroup.centralizer {c})
    (M ⊓ Subgroup.centralizer {c})

@[expose] def IsNaturalL3Module {G : Type} [Group G] (K V : Subgroup G) (n : ℕ) : Prop :=
  V ≤ K ∧ ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
    ∃ α : K →* Matrix.SpecialLinearGroup (Fin 3) F, Function.Surjective α ∧
      α.ker = V.subgroupOf K ∧
    ∃ β : V ≃* Multiplicative (Fin 3 → F),
      ∀ (k : K) (v w : V), (w : G) = k * v * (k : G)⁻¹ →
        Multiplicative.toAdd (β w) =
          (α k : Matrix (Fin 3) (Fin 3) F).mulVec (Multiplicative.toAdd (β v))

@[expose] def Item202 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G), Hyp201 G A M L N c →
    scriptM ((A ⊔ kTwenty M c : Subgroup G) : Set G) = {M}

@[expose] def Item203 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G), Hyp201 G A M L N c →
    M ≤ Subgroup.normalizer (((A ⊓ L) ⊔ CFSG.Open.pCoreOf 2 M : Subgroup G) : Set G) ∧
      Sec4.HasSection (Sec4.autIn M (A ⊓ L)) (QuaternionGroup 2)

@[expose] def Item204 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20 G A M L N c T → scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G) = {M}

@[expose] def Item205 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20 G A M L N c T →
      ¬ CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ ∧
      (∀ C : Subgroup T, C.Characteristic → C ≠ ⊥ →
        ¬ kTwenty M c ⊔ T ≤ Subgroup.normalizer ((C.map T.subtype : Subgroup G) : Set G)) ∧
      (∃ n : ℕ, Odd n ∧ Nonempty (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c) ≃*
        CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n))) ∧
      ¬ 2 ∣ (M ⊓ N).relIndex M ∧
      ∃ T' : Subgroup G, Ctx20 G A M L N c T' ∧ T' ≤ N

@[expose] def Item206 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20 G A M L N c T → T ≤ N → ⁅vTwenty M c T, A ⊓ L⁆ = ⊥

@[expose] def Item207 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20 G A M L N c T → T ≤ N →
      kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N

@[expose] def Item208 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20 G A M L N c T → T ≤ N →
      IsBlock M (kTwenty M c) ∧ vTwenty M c T = CFSG.Open.pCoreOf 2 (kTwenty M c) ∧
        ∃ n : ℕ, Odd n ∧ IsNaturalL3Module (kTwenty M c) (vTwenty M c T) n

@[expose] def Item209 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20 G A M L N c T → T ≤ N → ⁅L, vTwenty M c T⁆ = ⊥

end CFSG.RankThree.PartTwo.Sec20
