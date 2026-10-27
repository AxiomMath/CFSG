module

public import CFSG.LocalAnalysis.StandardType.GGTBTorRest
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmall
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggTBTorG2_holds :
    GGTBTorG2 := by
  intro p hp _hp2 lab hlab ht hpq
  have hs : LargeEvenSplit p lab := Or.inl ⟨by rw [ht]; trivial, hpq⟩
  refine LargeEvenLabelAll.mono (fun R _ I _ hX => ?_)
    (TableBExc.largeEvenLabelAll_card_lt_G2 hp hlab ht hs)
  intro L' _ _ ψ A hTB
  exfalso
  obtain ⟨hψ, hker, hperf, hA, hcomp, -, hp3, -⟩ := hTB
  have hXI : (TypeA.inducedSub ψ A : Set (MulAut R)) ⊆ I := by
    rintro φ ⟨a, ha, hφ⟩
    obtain ⟨φ', hφ'I, hφ'⟩ := hcomp a ha
    rw [TypeA.induced_unique ψ hψ hφ hφ']
    exact hφ'I
  have hcard := TypeA.card_inducedSub hψ hker hperf
    (fun a ha => (hcomp a ha).imp fun _ h => h.2)
  have hlt := hX _ hXI (TypeA.isElemAbelian_inducedSub hψ hA)
  omega

end CFSG.StandardType
