module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSixPointGenAux

public section

namespace CFSG.StandardType.QTwo.SixPoint

private theorem qTwoSixGensGen_bitset345 :
    CFSG.Decide.bitsetNodup (qTwoSixGen_pattern.map (fun p =>
      qTwoSixGen_matKey 3 4 5 (evalNative (qTwoSixGen_word 16 17 p)))) = true := by
  decide +kernel

theorem qTwoSixGensGen_nodup345 :
    (qTwoSixGen_pattern.map (fun p => evalNative (qTwoSixGen_word 16 17 p))).Nodup :=
  CFSG.Decide.nodup_of_bitsetNodup (qTwoSixGen_matKey 3 4 5) qTwoSixGensGen_bitset345

end CFSG.StandardType.QTwo.SixPoint

end
