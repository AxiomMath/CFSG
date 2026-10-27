module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma23Core

namespace CFSG
end CFSG
open CFSG

/-!
# Section 2 lemma 2.3 applications (wrapper)

The paper's Lemma 2.3 is cited wholesale from Bender [1, §1.6/7] ("On groups
with abelian Sylow 2-subgroups", Math. Z. 117 (1970), 164–176;
`books/bender-abelian-sylow2.pdf`).  With the [1]-facts module
(`Section2/Bender1970.lean`: `bender1970_1_6_maximalSubgroups_pGroups` =
Statement 1.6, `bender1970_1_7_i_oddCoreDisjoint` = Statement 1.7(i)) the
provable applications are carried out in the LOWER module
`Section2/Lemma23Core.lean` (imported above), which sits below
`Section2.Basic` so that the per-theorem Section-2 modules can consume them
without a landing cycle:

* `lemma_2_3_ii_inverts_of_core_disjoint` — the second conjunct of
  Lemma 2.3(ii);
* `lemma_2_3_equalityAlternative_of_Fstar_contained` — the equality
  alternative of Lemma 2.3(iii) from [1, 1.6];
* `lemma_2_3_ii_coreDisjoint_prime_of_Fstar_le` and
  `lemma_2_3_ii_coreDisjoint_prime_of_controlCore` — the first conjunct of
  Lemma 2.3(ii) for primes outside `π(F(Ĥ))` from [1, 1.7(i)].

This wrapper is kept for backward compatibility (it also re-exports
`Section2.Basic`).  The same-prime gap (`q ∈ π(F(Ĥ))` needs the paper's
Lemma 2.4, Glauberman [6] Theorems A/B) and the control-core-bridge notes
are documented in `Lemma23Core.lean`'s header and in
`node_graph/section2/lemma_2_3.md`.
-/
