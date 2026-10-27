module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExc5
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTvE7E8
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExc3Slot
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExc4Slot

public section

namespace CFSG.Yardstones.M3f9567aba59d

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.TableBExcTwoTB

theorem exc5_of_exc5Tv (p : ℕ) (lab : LargeEvenLabel)
    (h : (GGRemTableBLExc5TvLabel p lab ∧ ¬ GGE7TwoThreeLabel p lab) ∧
      ¬ GGE8TwoThreeLabel p lab) :
    GGRemTableBLExc5Label p lab := by
  obtain ⟨⟨⟨ht, hn, hp⟩, h7⟩, h8⟩ := h
  rcases ht with ht | ht | ht
  · exact (h7 ⟨ht, hn, hp⟩).elim
  · exact (h8 ⟨ht, hn, hp⟩).elim
  · exact ⟨ht, hn, hp⟩

end CFSG.Yardstones.M3f9567aba59d
