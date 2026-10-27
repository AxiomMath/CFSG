module

public import CFSG.RankThree.PartOne.SRC.Split
public import CFSG.RankThree.PartOne.SRC.ModelL4Nine
import CFSG.Adapters.LinearCatalog

public section

namespace CFSG.RankThree.PartOne.SRC

open TauCeti CFSG.RankThree.PartOne.N143

theorem noHardL4Nine : NoLowTwoRankSectionFor IsHardL4NineIndex := by
  refine noLowTwoRankSectionFor_of_rankFourCover fun i hi => ?_
  rcases i with ⟨p, hp⟩ | ⟨n, hn⟩ | ⟨⟨li, hv⟩⟩ | ⟨s⟩
  · exact (hi : False).elim
  · exact (hi : False).elim
  · cases li <;> first | exact (hi : False).elim | skip
    obtain ⟨hr, h9⟩ := hi
    subst hr
    rename_i q
    have hcard : q.p ^ q.exponent = 9 := by rw [← PrimePower.card_def]; exact h9
    have hp3 : q.p = 3 := by
      have hd : q.p ∣ 3 ^ 2 := by
        have : q.p ∣ q.p ^ q.exponent := dvd_pow_self q.p q.exponent_pos.ne'
        rw [hcard] at this
        exact this
      exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).mp
        (q.prime_p.dvd_of_dvd_pow hd)
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    have hF9 : Nat.card (GaloisField q.p q.exponent) = 9 := by
      rw [GaloisField.card _ _ q.exponent_pos.ne', hcard]
    have hch : CharP (GaloisField q.p q.exponent) 3 := CharP.congr q.p hp3
    exact ⟨3, Nat.prime_three, by norm_num, rankFourCover_of_mulEquiv
      (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 3 q hv)
      (rankFourCover_psl4_nine (F := GaloisField q.p q.exponent) hF9)⟩
  · exact (hi : False).elim

end CFSG.RankThree.PartOne.SRC
