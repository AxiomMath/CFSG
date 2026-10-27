module

public import CFSG.OddTranspositions.PartThree.EightOne.Defs
public import CFSG.OddTranspositions.PartThree.EightEight.Statement
public import CFSG.OddTranspositions.PartThree.Nine.ThreeSplit
public import CFSG.OddTranspositions.SevenThreeTransitive
public import CFSG.Timmesfeld.Bridge.Asc72Defs
public import CFSG.OddTranspositions.PartThree.EightFive.Holds
public import CFSG.OddTranspositions.PartFour.Line
public import CFSG.OddTranspositions.SixNineUnconditional
public import CFSG.OddTranspositions.PartThree.Eleven.OneThree.Below
public import CFSG.OddTranspositions.PartThree.EightFive.QNotCentralCore

public section

namespace CFSG.OddTranspositions.PartThree.ElevenThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ
open CFSG.OddTranspositions.PartFour

variable {G : Type} [Group G] [Finite G] {D : Set G}

structure MainHyp (hC : HypothesisC D) : Prop where
  rad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥
  not_three : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)
  not_o4 : ¬ O4PairData G D
  not_wreath : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n)
  not_central : ¬ CFSG.oddCore (Halpha D hC.alpha ⧸ CFSG.pCore 2 (Halpha D hC.alpha)) ≤
    Subgroup.center (Halpha D hC.alpha ⧸ CFSG.pCore 2 (Halpha D hC.alpha))

abbrev EightOneShape (X : Type) [Group X] [Finite X] : Prop :=
  Nonempty (X ⧸ EightOne.twoOddCore X ≃*
      Multiplicative (ZMod 2) × CFSG.Theory.Comparator.PSL2Model 2) ∨
    Nonempty (X ⧸ EightOne.twoOddCore X ≃*
      Multiplicative (ZMod 2) × ↥(CFSG.Theory.Comparator.PSU3Model 2))

@[expose] def kBlock (D γ : Set G) : Subgroup G :=
  (EightOne.twoOddCore (Halpha D γ)).map (Halpha D γ).subtype

@[expose] def kOrbit (D γ δ : Set G) : Set (Set G) :=
  (fun k => cimg k δ) '' (kBlock D γ : Set G)

@[expose] def rBlock (D ε : Set G) : Subgroup G :=
  (CFSG.oddCore (Halpha D ε)).map (Halpha D ε).subtype

@[expose] def lineGroup (D α ε : Set G) : Subgroup G :=
  Subgroup.closure (DalphaStar D α ∩ DalphaStar D ε)

@[expose] def oddLineImage (hC : HypothesisC D) (ε : Set G) :
    Subgroup (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) :=
  ((rBlock D ε ⊓ lineGroup D hC.alpha ε).subgroupOf (Halpha D hC.alpha)).map
    (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))

end CFSG.OddTranspositions.PartThree.ElevenThree
