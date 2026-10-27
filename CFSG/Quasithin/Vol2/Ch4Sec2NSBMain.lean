module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBDefs

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.CosetGraph
open scoped commutatorElement Pointwise

theorem conf4212NoSumBig_of_parts (h324 : Lemma324One) (hNC : NotCriticalPair)
    (hNK : NotLeKernelAt) : Conf4212NoSumBig := by
  rw [conf4212NoSumBig_iff]
  intro G _ _ T M L Mm I H K m k hd
  obtain ⟨hd', -⟩ := h324 G T M L Mm I H K m k hd
  obtain ⟨H', K', hch⟩ := lemma_3_24_two hd'
  have hIV : I ⊓ Subgroup.normalizer (vV T L : Set G) ≤ Subgroup.normalizer (vV T L : Set G) :=
    inf_le_right
  rcases le_kernelAt_or_exists_isCriticalPair
      (graph322 T M L (I ⊓ Subgroup.normalizer (vV T L : Set G)) K')
      (zAt (K' ⊔ pCoreOf 2 (I ⊓ Subgroup.normalizer (vV T L : Set G)))
        (gammaZero T M L (I ⊓ Subgroup.normalizer (vV T L : Set G)))
        (uZero (I ⊓ Subgroup.normalizer (vV T L : Set G)) K'))
      (typeOne T M L (I ⊓ Subgroup.normalizer (vV T L : Set G)) K') with
    hb | ⟨δ, ε, hc⟩
  · exact hNK G T M L Mm _ H' K' m k hch hIV hb
  · exact hNC G T M L Mm _ H' K' m k hch hIV δ ε hc

end CFSG.Quasithin.H13.Ch4.NSB
