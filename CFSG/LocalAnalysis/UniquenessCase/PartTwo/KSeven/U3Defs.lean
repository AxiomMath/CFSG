module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

abbrev U3 {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) : Type :=
  primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)

noncomputable abbrev u3Field {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (σ : K ≃+* K) : MulAut (U3 h) :=
  primeFormFieldHom h (isPrimeFormGram_one (n := 3)) σ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven
