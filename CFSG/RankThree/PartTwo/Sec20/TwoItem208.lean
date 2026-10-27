module

public import CFSG.RankThree.PartTwo.Sec20.TwoItem207
public import CFSG.RankThree.PartTwo.Sec20.Item208C134M
public import CFSG.RankThree.PartTwo.Sec20.Item20Res2ProofXAut

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

section Holds


theorem item208Two_of
    (h1912 : Item1912) (h194 : Sec19.Item194UsedWide3) (h23 : Item1923)
    (h204 : Item204Two) (h205 : Item205Two) : Item208Two := by
  intro G _ _ A M L N c T hT hyp hTN
  have hA : Alt20 G A M L N c := alt20_of_hyp1921 h1912 h194 h23 hyp hT.centralizer_eq
  obtain ⟨-, h2, h3, -, -⟩ := h205 G A M L N c T hT hyp
  exact item208One_core CFSG.Quasithin.MS93.c134Weak_holds.toM Sec3.Sims321.item321Split_holds hT
    hA.eq_normalizer hA.le_normalizer hA.quotient_iso
    (Sec18.commutator_eq_of_mem_oTwoComponentsIn hyp.mem_oTwoComponentsIn) hA.not_le
    hA.pCoreOf_le hA.relIndex_inf hA.K_mem hA.K_not_le hA.K_type hTN (h204 G A M L N c T hT hyp)
    h2 h3 (item207Two_of h1912 h194 h23 h204 h205 G A M L N c T hT hyp hTN)

theorem item209Two_of
    (h1912 : Item1912) (h194 : Sec19.Item194UsedWide3) (h23 : Item1923)
    (h204 : Item204Two) (h205 : Item205Two) : Item209Two := by
  intro G _ _ A M L N c T hT hyp hTN
  have hA : Alt20 G A M L N c := alt20_of_hyp1921 h1912 h194 h23 hyp hT.centralizer_eq
  exact item209One_core hT hA.eq_normalizer hA.le_normalizer hA.quotient_iso
    (Sec18.commutator_eq_of_mem_oTwoComponentsIn hyp.mem_oTwoComponentsIn) hA.not_le
    hA.pCoreOf_le hTN (item207Two_of h1912 h194 h23 h204 h205 G A M L N c T hT hyp hTN)
    (item208Two_of h1912 h194 h23 h204 h205 G A M L N c T hT hyp hTN)

end Holds

end CFSG.RankThree.PartTwo.Sec20
