module

public import CFSG.Sporadic.B
public import CFSG.Sporadic.Co2
public import CFSG.Sporadic.HN
public import Certificates.Certificate16014

public section

namespace CFSG.Monster.Existence.Compat

open CFSG CFSG.Open CFSG.Blueprint

structure TwoARemaining : Prop where
  b_card : Nat.card NativeSporadic.B = monsterBabyOrder
  fi23_simple : IsSimpleGroup NativeSporadic.Fi23
  fi23_card : Nat.card NativeSporadic.Fi23 = monsterFi23Order
  th_simple : IsSimpleGroup NativeSporadic.Th
  th_card : Nat.card NativeSporadic.Th = monsterThOrder
  mcl_simple : IsSimpleGroup NativeSporadic.McL
  mcl_card : Nat.card NativeSporadic.McL = monsterMcLOrder
  fi22_simple : IsSimpleGroup NativeSporadic.Fi22
  fi22_card : Nat.card NativeSporadic.Fi22 = monsterFi22Order
  e6_simple : ∀ (X : Type) [Group X], LieModel X .twistedE6 0 2 1 → IsSimpleGroup X
  e6_card : ∀ (X : Type) [Group X], LieModel X .twistedE6 0 2 1 → Nat.card X = ordTwistedE6 2
  f4_simple : ∀ (X : Type) [Group X], LieModel X .F4 0 2 1 → IsSimpleGroup X
  f4_card : ∀ (X : Type) [Group X], LieModel X .F4 0 2 1 → Nat.card X = ordF4 2
  u62_card : ∀ (X : Type) [Group X], LieModel X .PSU 6 2 1 → Nat.card X = ordTwistedA 5 2

theorem TwoARemaining.toFacts
    (R : TwoARemaining) :
    TwoAFacts where
  b_simple := CFSG.Sporadic.B.fam_b_simplicity
  b_card := R.b_card
  co2_simple := CFSG.Sporadic.Co2.isSimpleGroup_Co2
  co2_card := CFSG.Sporadic.Co2.card_Co2.trans (by exact Certificates.certificate16014.1)
  fi23_simple := R.fi23_simple
  fi23_card := R.fi23_card
  th_simple := R.th_simple
  th_card := R.th_card
  mcl_simple := R.mcl_simple
  mcl_card := R.mcl_card
  hn_simple := CFSG.Sporadic.HN.isSimpleGroup_HN
  hn_card := CFSG.Sporadic.HN.card_HN.trans (by exact Certificates.certificate16014.2)
  fi22_simple := R.fi22_simple
  fi22_card := R.fi22_card
  e6_simple := R.e6_simple
  e6_card := R.e6_card
  f4_simple := R.f4_simple
  f4_card := R.f4_card
  u62_card := R.u62_card

end CFSG.Monster.Existence.Compat
