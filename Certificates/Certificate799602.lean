module

public import Certificates.Kernel.F4Syl3.Final

@[expose] public section

open CFSG.RankThree.PartTwo.Sec21.FF81.F4 CFSG.RankThree.PartTwo.Sec21.FF79 CFSG.LieType.Ree

public section

namespace Certificates

open CFSG.RankThree.PartTwo.Sec21.FF81.F4 CFSG.RankThree.PartTwo.Sec21.FF79 CFSG.LieType.Ree in
theorem certificate799602 :     ∃ P : Subgroup F42C, Nat.card P = 3 ^ 6 ∧ Subgroup.closure (Set.range sE) ≤ P ∧
      IsElemAb 3 4 (Subgroup.closure (Set.range sE)) ∧
      (∀ B ≤ P, IsElemAb 3 4 B → B = Subgroup.closure (Set.range sE)) ∧
      (∀ x ∈ P, x * zE = zE * x) ∧
      (∀ x ∈ P, x ≠ 1 → x ^ 3 = 1 → IsConj x rAE ∨ IsConj x rBE ∨ IsConj x zE) ∧
      (∃ LA LB : Finset (Subgroup F42C), LA.card ≤ 12 ∧ LB.card ≤ 12 ∧
        ∀ d ∈ Subgroup.closure (Set.range sE), d ≠ 1 →
          (IsConj d rAE ∧ Subgroup.zpowers d ∈ LA) ∨ (IsConj d rBE ∧ Subgroup.zpowers d ∈ LB) ∨
            IsConj d zE) ∧
      IsConj (ReeTag.F4.finiteExceptionalAut (ZMod 2) rAE) rBE ∧
      ∀ t ∈ [tE, uE, tuE, vE], ∀ ρ ∈ [rAE, rBE], ∃ c : F42C, c * ρ * c⁻¹ * t = t * (c * ρ * c⁻¹) :=
  CFSG.KC.F4Syl3.syl3_facts

end Certificates
