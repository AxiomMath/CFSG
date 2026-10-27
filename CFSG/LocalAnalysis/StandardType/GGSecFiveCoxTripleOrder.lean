module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCoxTripleGramCases
import CFSG.LocalAnalysis.StandardType.GGSecFiveCoxTripleOrderK

public section

namespace CFSG.StandardType.CoxTriple

theorem card_gramReflGroup_dvd_48_of_mem {N : Matrix (Fin 3) (Fin 3) ℤ} (h : N ∈ admList) :
    Nat.card ↥(gramReflGroup N) ∣ 48 :=
  OrderK.card_dvd_of_mem_admList h

theorem card_gramReflGroup_dvd_48 {N : Matrix (Fin 3) (Fin 3) ℤ} (h : AdmGram N) :
    Nat.card ↥(gramReflGroup N) ∣ 48 :=
  card_gramReflGroup_dvd_48_of_mem (admGram_mem_admList h)

end CFSG.StandardType.CoxTriple

end
