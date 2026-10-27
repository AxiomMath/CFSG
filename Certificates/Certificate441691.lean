module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.WordSub
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.SylowData
import Certificates.Kernel.HN1408.SylCen441691Glue

public section

open CFSG.EvenSporadicStandard.HNRecog.HaradaModel

namespace Certificates

theorem certificate441691 : Nat.card ↥(wordSubgroup sWords ⊓
    Subgroup.centralizer (wordSubgroup sWords : Set (Equiv.Perm (Fin 1408)))) = 4 :=
  CFSG.KD.HN1408.SylSG.card_center_S

theorem certificate441691.card_S : Nat.card ↥(wordSubgroup sWords) = 2 ^ 11 :=
  CFSG.KD.HN1408.SylSG.card_wordSubgroup_S

end Certificates
