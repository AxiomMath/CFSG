module

public import CFSG.OddTranspositions.PartFour.Statements
public import CFSG.OddTranspositions.PartFour.RankOneFamilies
import CFSG.OddTranspositions.PartFour.RootMeetsSqU
import CFSG.OddTranspositions.PartFour.OrthMeetsSq
import CFSG.OddTranspositions.PartFour.OrthFiveMeetsSq
import CFSG.OddTranspositions.PartFour.WreathLine

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Bridge.OddTransp


theorem theorem5_of_partThree (h87 : PartThree.Theorem8_7)
    (h89 : PartThree.Lemma8_9) (h113 : PartThree.Theorem11_3) : Theorem5 := by
  intro G _ _ D hC hrad hW hE hMZ
  rcases hE with ⟨s, hs, m, f, hm, hf, hsp | hut | hor⟩ | ⟨n, hn, b, hsym, hnd, hM⟩ |
      ⟨s, hs, f, m, hm, hsw⟩ | ⟨f, hSz⟩
  · obtain ⟨k, rfl, -⟩ := id hsp
    rcases Nat.lt_or_ge k 2 with hk | hk
    · obtain rfl : k = 1 := by omega
      exact meetsSq_of_isSymplecticTransvection_two_imageClass h87 h89 h113 hC hrad hW hMZ
        hf hsp
    · exact meetsSq_of_isSymplecticTransvection_imageClass h89 h113 hC hrad hW hMZ hs hk hf hsp
  · rcases Nat.lt_or_ge m 4 with hd | hd
    · interval_cases m
      · exact meetsSq_of_isUnitaryTransvection_two_imageClass h87 h89 h113 hC hrad hW hMZ
          hf hut
      · exact meetsSq_of_isUnitaryTransvection_three_imageClass h87 h89 h113 hC hrad hW
          hMZ hs hf hut
    · exact meetsSq_of_isUnitaryTransvection_imageClass h89 h113 hC hrad hW hMZ hs hd hf hut
  · exact meetsSq_of_isOrthReflection_imageClass h89 h113 hC hrad hW hMZ hs hf hor
  · exact meetsSq_of_fischerCentralQuotientModel_five_imageClass h89 h113 hC hrad hW hMZ hn hsym
      hnd hM
  · exact (false_of_isWreathTransposition h89 h113 hC hrad hW hMZ hs (by omega) hsw).elim
  · exact meetsSq_of_isSz_imageClass h87 h89 h113 hC hrad hW hMZ hSz

end CFSG.OddTranspositions.PartFour
