module

public import CFSG.Quasithin.H13.NQCoreP134Inputs
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddOut
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddAbel
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddEven
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddSz
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddJ1

public section

namespace CFSG.Quasithin.H13.NQCore

@[expose] def Facts134OddNormal : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (p : ℕ) [Fact p.Prime] (L P T : Subgroup A),
    5 ≤ p → OddConfig p L P T → OddOutcome p L P T

theorem facts134Odd_of_normal
    (hN : Facts134OddNormal) : Facts134Odd where
  outCyclic := facts134Odd_outCyclic
  normal := hN
  outAbelian := facts134Odd_outAbelian
  psl2Borel := facts134Odd_psl2Borel
  psl2Even := facts134Odd_psl2Even
  szLocal := facts134Odd_szLocal
  j1Local := facts134Odd_j1Local

end CFSG.Quasithin.H13.NQCore
