module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.WordSub
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.SylowData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.AData
import Certificates.Kernel.HN1408.SylSGlue

public section

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.HaradaModel

namespace Certificates

theorem certificate441664 : ∀ B : Subgroup ↥P1408, B ≤ wordSubgroupP sWords → CFSG.Open.IsElemAbelian 2 B →
    Nat.card B = 64 → ∃ y : ↥P1408, B = (wordSubgroupP uWords).map (MulAut.conj y).toMonoidHom :=
  fun _ hBS he h64 => CFSG.KD.HN1408.SylSG.conj_of_le_S hBS he h64

theorem certificate441664.card_S : Nat.card ↥(wordSubgroupP sWords) = 2 ^ 11 :=
  CFSG.KD.HN1408.SylSG.card_S

end Certificates
