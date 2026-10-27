module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight103FourKeyAbstract
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUModel
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight103FourKeyMono
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight103FourKeyU5Mono
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight103FourKeyU5Syl3
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight103FourKeyU5Field

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K]

theorem u45KeyDvdConcl_statedSU_five (h : UnitaryFieldData 2 2 K) :
    U45KeyDvdConcl (StatedProj (StatedSU 5 (2 ^ 2) K)) 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [h.card]; positivity)
  obtain ⟨Q, T, D, hQ, hQi, -, hTi, hTy, -, hkD, hDi, hDd⟩ := exists_u5_monomial h
  obtain ⟨S, hS, hSi, hSf⟩ := exists_u5_sylow_three_fix h
  refine u45KeyDvdConcl_of_monomial (uConjAut h (n := 5) (by norm_num))
    (fun α hα => mem_range_uConjAut_five_of_pow_eq_one h hα) (card_ker_uConjAut_five h) hQ hQi
    hTi hTy hkD hDi hS hSi ?_
  intro A hA s hs
  obtain ⟨d, hd, h01, h23⟩ := hDd A hA
  exact hSf A d hd h01 h23 s hs

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
