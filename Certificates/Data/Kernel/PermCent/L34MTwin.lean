
module

public import Certificates.Data.Kernel.PermCent.CV
public import CFSG.GH74.Uniqueness.SU.KI1r4F61L34MInputs
public import CFSG.Certificates.Kernel.Common.StrLitChunks

public section

namespace CFSG.Certificates.Kernel.PkCV.L34MT

open CFSG.GH74.Uniqueness.SU.K.R4.L34M CFSG.GH74.KGroups.L34

#str_lit_chunks CFSG.Certificates.Kernel.PkCV.L34MT.W1 CFSG.GH74.Uniqueness.SU.K.R4.L34M.words1
  2000 400000 2048
#str_lit_chunks CFSG.Certificates.Kernel.PkCV.L34MT.W2 CFSG.GH74.Uniqueness.SU.K.R4.L34M.words2
  2000 400000 2048
#str_lit_chunks CFSG.Certificates.Kernel.PkCV.L34MT.W3 CFSG.GH74.Uniqueness.SU.K.R4.L34M.words3
  2000 400000 2048
#str_lit_chunks CFSG.Certificates.Kernel.PkCV.L34MT.W4 CFSG.GH74.Uniqueness.SU.K.R4.L34M.words4
  2000 400000 2048

@[expose] def dvalC : List Char → Nat → Nat
  | [], a => a
  | c :: cs, a => dvalC cs (10 * a + (c.toNat - 48))

@[expose] def charsOK (cs : List Char) : Bool := cs.all fun c => c.isDigit || c == ';' || c == ' '

@[expose] def splC (c : Char) : List Char → List Char → List (List Char)
  | [], acc => [acc.reverse]
  | d :: cs, acc => if d = c then acc.reverse :: splC c cs [] else splC c cs (d :: acc)

@[expose] def wordsC (cs : List Char) : List (List ℤ) :=
  (splC ';' cs []).map fun w => (splC ' ' w []).filterMap fun t =>
    if t.isEmpty then none else some (dvalC t 0 : ℤ)

@[expose] noncomputable def evCodesC (S : List (CV 42)) : List ℤ → CV 42
  | [] => 1
  | z :: w => (if 0 < z then S.getD (z.toNat - 1) 1 else (S.getD ((-z).toNat - 1) 1)⁻¹) *
      evCodesC S w

@[expose] noncomputable def clC (r : Equiv.Perm (Fin 42)) (cs : List Char) : List (CV 42) :=
  let S := [PA, PB, sg0, sg1, sg2].map cOf
  let rc := cOf r
  (wordsC cs).map fun w => evCodesC S w * rc * (evCodesC S w)⁻¹

@[expose] noncomputable def coverC (L1 L2 L3 L4 : List (CV 42)) : Bool :=
  (elemsC QA).all fun g => !powOneC g 2 || decide (g = 1) || decide (g ∈ L1) ||
    decide (g ∈ L2) || decide (g ∈ L3) || decide (g ∈ L4)

end CFSG.Certificates.Kernel.PkCV.L34MT

end
