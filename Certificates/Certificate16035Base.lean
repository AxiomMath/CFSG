
module

public import CFSG.Monster.B.TwoA.Base.Space34AInputs
public import CFSG.Monster.B.TwoA.Base.WCls

@[expose] public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.Code CFSG.Monster.Lifts
  CFSG.Monster.Visible CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Sporadic.Mathieu

public section


open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.Code CFSG.Monster.Lifts
  CFSG.Monster.Visible CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Sporadic.Mathieu

namespace CertificateChecks.Batch16035

private theorem dec_v0_0 : rowCheck (pairN (0 : Fin 24) (1 : Fin 24)) 12288 = true := by
  decide +kernel

private theorem rCoord_check_1 :
    ∀ i : Fin 7, rowCheck (pairN (pa7 i) (pb7 i)) (rCoord i) = true := by
  decide +kernel

private theorem sCoord_act_2 : ∀ i : Fin 7,
    Native.actD 22 Native.quotientBasis (sCoord i) = rCoord i ∨
      Native.actD 22 Native.quotientBasis (sCoord i) = rCoord i ^^^ 12288 := by
  decide +kernel

private theorem xsel4_cases_3 :
    ∀ c : Fin 4 → ZMod 2, xsel4 c = 0 ∨ xsel4 c = 31 ∨
    ∃ i : Fin 7, ∃ b : ZMod 2, xsel4 c = sCoord i ^^^ sel b 31 := by
  decide +kernel

private theorem xsel4_exists_4 :
    ∀ (i : Fin 7) (b : ZMod 2), ∃ c : Fin 4 → ZMod 2,
    xsel4 c = sCoord i ^^^ sel b 31 := by
  decide +kernel

private theorem xsel3_cases_5 : ∀ c : Fin 3 → ZMod 2,
    xsel3 c = 0 ∨
      xsel3 c = 31 ∨
      ∃ i : Fin 7, (i : ℕ) < 3 ∧ ∃ b : ZMod 2,
        xsel3 c = sCoord i ^^^ sel b 31 := by
  decide +kernel

private theorem xsel3_exists_6 :
    ∀ (i : Fin 7), (i : ℕ) < 3 → ∀ b : ZMod 2, ∃ c : Fin 3 → ZMod 2,
    xsel3 c = sCoord i ^^^ sel b 31 := by
  decide +kernel

private theorem linearIndependent_gen4_h1_7 : ∀ c : Fin 4 → ZMod 2, xsel4 c < 2 ^ 22 := by
  decide +kernel

private theorem linearIndependent_gen4_h3_8 :
    ∀ c : Fin 4 → ZMod 2, xsel4 c = 0 → c = 0 := by
  decide +kernel

private theorem linearIndependent_gen3_h1_9 : ∀ c : Fin 3 → ZMod 2, xsel3 c < 2 ^ 22 := by
  decide +kernel

private theorem linearIndependent_gen3_h3_10 :
    ∀ c : Fin 3 → ZMod 2, xsel3 c = 0 → c = 0 := by
  decide +kernel

end CertificateChecks.Batch16035

namespace Certificates

end Certificates
