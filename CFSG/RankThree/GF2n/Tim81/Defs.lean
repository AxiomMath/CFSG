module

public import CFSG.Timmesfeld.Transvection.Statement
public import CFSG.CGT.Timmesfeld75.Defs
public import CFSG.Foundations.Catalog

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.LieType CFSG.LieType.Universal CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G]

structure Hyp (M V : Subgroup G) : Prop where
  o2 : pCore 2 G = ⊥
  maxLocal : IsMaximalTwoLocal M
  fitting : generalizedFitting M = pCore 2 M
  maxAb : Maximal (fun U : Subgroup G => U ≤ M ∧ M ≤ Subgroup.normalizer (U : Set G) ∧
    IsMulCommutative U) V
  elem : Assembly.IsElemAbelian 2 V
  ti : IsTI V

abbrev Pc (M V : Subgroup G) : Subgroup G :=
  inSubgroup (pCore 2) M ⊓ Subgroup.centralizer (V : Set G)

@[expose] def IsHMember (M V H : Subgroup G) : Prop :=
  inSubgroup (pCore 2) H ≠ ⊥ ∧ Pc M V ≤ H ∧ ¬ H ≤ M

@[expose] def UnitaryConclusion (V : Subgroup G) : Prop :=
  ∃ f : ℕ, ∃ hf : 2 ≤ f, Nat.card V = 2 ^ f ∧
    Subgroup.normalClosure (V : Set G) = generalizedFitting G ∧
    ∃ m : ℕ, ∃ hm : 4 ≤ m,
      ∃ Φ : Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) m →* G,
        Φ.range = Subgroup.normalClosure (V : Set G) ∧ Φ.ker = Subgroup.center _ ∧
        ∀ U : Subgroup G, (∃ g : G, U = conjSubgroup g V) ↔
          ∃ x, U = (conjSub ((Unitary.rootDatum (card_galoisField_two_mul (by omega : 1 ≤ f))
            m).rootGroup (unitaryLongRoot m (by omega))) x).map Φ

@[expose] def Theorem1Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V : Subgroup G), Hyp M V → 4 ≤ Nat.card V →
    WeaklyClosedIn V (inSubgroup (pCore 2) M) →
    WeaklyClosedIn V M ∨ UnitaryConclusion V ∨ ∀ H : Subgroup G, ¬ IsHMember M V H

@[expose] def Sec8Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    IsKProper G → IsCharacteristicPType G 2 →
    ∀ M V : Subgroup G, Hyp M V → 4 ≤ Nat.card V →
      WeaklyClosedIn V (inSubgroup (pCore 2) M) → ¬ WeaklyClosedIn V M →
      ∃ H : Subgroup G, IsHMember M V H

end CFSG.RankThree.GF2n.Tim81
