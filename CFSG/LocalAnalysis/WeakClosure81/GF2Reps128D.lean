module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128D2
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128D3
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128D4
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128D6

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo Subgroup

theorem w4Lem6_3Swap_holds : W4Lem6_3Swap := by
  intro W _ _ hW L t hLq ht2 hmove hcomm hirr hdiag
  obtain ⟨n, hn, ⟨e⟩⟩ := exists_sl2_equiv hW hLq ht2 hcomm hirr hdiag
  have hd : dMinDeg ↥L = 2 * n := dMinDeg_eq_of_mulEquiv_sl2 hn e
  rcases tensor_or_two_mul_le hW ht2 hmove hcomm hirr hdiag hn e with h | ⟨hrk, K, _, _, hK, hT⟩
  · left
    rw [hd]
    exact h
  · right
    exact ⟨n, isNaturalO4Plus_of_isMatTensor2 hW ht2 hK hn hT hrk, hrk, hd,
      fun s hs2 hLs hrks => mem_sup_zpowers_of_swap hW ht2 hK hn hT hrk hs2 hLs hrks⟩

end CFSG.LocalAnalysis.WeakClosure81
