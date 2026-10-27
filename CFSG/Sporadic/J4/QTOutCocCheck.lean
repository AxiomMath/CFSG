module

public import CFSG.Sporadic.J4.QTOutCocNative
public meta import CFSG.Sporadic.J4.QTOutCocNative
public import CFSG.Sporadic.J4.QTRankCheck
public import CFSG.Sporadic.J4.QTOutActCheck
public import Certificates.Certificate4020

public section

namespace CFSG.Sporadic.J4.QT

theorem rel_tables : ∀ r ∈ rel01 ++ rel02 ++ relMix, wordT r = idT :=
  Certificates.certificate4020.1

theorem rel_letters :
    ∀ r ∈ rel01 ++ rel02 ++ relMix, ∀ ℓ ∈ r, ℓ ∈ letters :=
  Certificates.certificate4020.2.1

theorem rel01_letters :
    ∀ r ∈ rel01, ∀ ℓ ∈ r, ℓ = 1 ∨ ℓ = -1 ∨ ℓ = 2 ∨ ℓ = -2 :=
  Certificates.certificate4020.2.2.1

theorem rel02_letters :
    ∀ r ∈ rel02, ∀ ℓ ∈ r, ℓ = 1 ∨ ℓ = -1 ∨ ℓ = 3 ∨ ℓ = -3 :=
  Certificates.certificate4020.2.2.2.1

theorem stage1_eq : stage1 = [0, 1373] :=
  Certificates.certificate4020.2.2.2.2.1

theorem stage2_eq : stage2 = [0, 689] :=
  Certificates.certificate4020.2.2.2.2.2.1

theorem relAll_cases :
    relAll 0 0 = true ∧ relAll 1373 689 = true ∧ relAll 0 689 = false ∧
    relAll 1373 0 = false :=
  Certificates.certificate4020.2.2.2.2.2.2.1

theorem t0_surj :
    ∀ e < 2 ^ 11, ∃ v < 2 ^ 11, v ^^^ actT (letterTab 1) v = e :=
  Certificates.certificate4020.2.2.2.2.2.2.2

end CFSG.Sporadic.J4.QT
