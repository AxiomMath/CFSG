module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.gorenstein_5_4_15

namespace CFSG
end CFSG
open CFSG

/-! # Lemma 4.13 from BG Section 4 -/

section Main

public theorem CFSG.lemma_4_13 {R : Type*} [Group R] [Finite R] {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpodd : p ≠ 2) [Fact (IsPGroup p R)]
    (hA3 : selfCentralizingAbelianSubgroupsAtLeast R 3 = ∅)
    (hqAut : q ∣ Nat.card (MulAut R)) (hq_ne : q ≠ p) :
    q ∣ (p ^ 2 - 1) ∧ q < p := by
  exact gorenstein_theorem_5_4_15_prime_dvd_aut
    (R := R) (p := p) (q := q) hpodd (Fact.out : IsPGroup p R) hA3 hqAut hq_ne
