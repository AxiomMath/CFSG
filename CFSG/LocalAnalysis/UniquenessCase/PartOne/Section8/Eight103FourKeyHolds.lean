module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight103FourKFact
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight103FourKeyU4
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight103FourKeyU5

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open

theorem kU45KeyDvd_holds : KU45KeyDvd := by
  intro X _ _ n hX p hp hp2 hp3 hpn R hR
  rcases hX with ⟨hU5, rfl⟩ | ⟨hU4, hn⟩
  · obtain rfl : p = 5 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 (by simpa using hpn)
    obtain ⟨⟨h2, hn1, -⟩, K, hfield, hfinite, hK, ⟨e⟩⟩ :=
      hU5.statedClassicalModel_of_ne_zero (by norm_num)
    let fieldK : Field K := hfield
    let finiteK : Finite K := hfinite
    have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 2 K :=
      ⟨h2, hn1, by rw [hK, ← pow_mul, mul_comm]⟩
    exact (u45KeyDvdConcl_statedSU_five h).of_mulEquiv e R hR
  · obtain ⟨⟨h2, hn1, -⟩, K, hfield, hfinite, hK, ⟨e⟩⟩ :=
      hU4.statedClassicalModel_of_ne_zero (by norm_num)
    let fieldK : Field K := hfield
    let finiteK : Finite K := hfinite
    have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K :=
      ⟨h2, hn1, by rw [hK, ← pow_mul, mul_comm]⟩
    have hX' : UC22.IsU4 (StatedProj (StatedSU 4 (2 ^ n) K)) n :=
      CFSG.Blueprint.LieModel.of_mulEquiv e hU4
    exact (u45KeyDvdConcl_statedSU_four h hn hX' hp hp2 hp3 hpn).of_mulEquiv e R hR

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
