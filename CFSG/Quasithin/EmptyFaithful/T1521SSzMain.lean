module

public import CFSG.Quasithin.EmptyFaithful.T1521SSzN
public import CFSG.Quasithin.EmptyFaithful.T1521SSzW

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

theorem dich1521Sz_of
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) : Dich1521Sz := by
  intro G _ _ X S L hStd hcomp hZ hSz
  refine Or.inl ?_
  have hL : SzComponent1521 L := SzComponent1521.of_cases hcomp.2.2 hZ hSz
  have hS : ∀ m ∈ S, ∃ k : ℕ, m ^ 2 ^ k = 1 := by
    intro m hm
    obtain ⟨k, hk⟩ := hStd.sylow.2.1 ⟨m, hm⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have horb := a3Orbits_of_a37_a38 (G := G) h37 h38 X S L hStd.sqtk hStd.sylow hStd.comp
  rcases horb.2 with hnorm | ⟨t, htS, htN, hpair, -, hint, -⟩
  · exact nrm1521_of_sz_normal hL hStd.sylowL hS hnorm
  · exact nrm1521_of_sz_wreath
      ⟨le_of_mem_cComp hStd.comp, htS, hStd.sylow.1 htS, htN, horb.1, hpair, hint⟩ hL
      hStd.sylowL hS

end CFSG.Quasithin
