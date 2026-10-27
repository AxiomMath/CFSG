module

public import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofSplit
public import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofCharThree
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemTitsLocal
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG.Sporadic.Schreier.Tits

namespace Item228Census4Proof

theorem orderOf_ne_fifteen_titsD
    (g : titsD) : orderOf g ≠ 15 := by
  intro h
  have h3 : orderOf (g ^ 5) = 3 := by
    rw [orderOf_pow' g (by norm_num), h]
    norm_num
  have h5 : orderOf (g ^ 3) = 5 := by
    rw [orderOf_pow' g (by norm_num), h]
    norm_num
  exact Sec4.Item434RemTits.mul_ne_mul_of_orderOf h3 (Or.inl rfl) h5
    (Commute.pow_pow_self g 5 3).eq

theorem noL2Normal228_titsD :
    NoL2Normal228 titsD := by
  have : IsSimpleGroup titsD := titsD_simple
  refine Item228CensusProof.noL2Normal228_of_no15 ?_ orderOf_ne_fifteen_titsD
  rw [card_titsD]
  norm_num

end Item228Census4Proof

open Item228Census4Proof

theorem census228Tits_holds :
    Census228Tits := by
  rintro Y _ _ ⟨f, hf⟩
  obtain ⟨e⟩ := titsModelEquiv Y 2 f hf
  exact Or.inr (Item228CensusProof.noL2Normal228_of_mulEquiv e noL2Normal228_titsD)

end CFSG.RankThree.PartTwo.Sec21
