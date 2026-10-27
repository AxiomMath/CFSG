module

public import CFSG.Sporadic.Schreier.J4SNCharData
public meta import CFSG.Sporadic.Schreier.J4SNCharData
public import CFSG.Sporadic.Schreier.J4SKCent
public meta import CFSG.Sporadic.Schreier.J4SKCent
public import Certificates.Certificate2174

public section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.SmallF2.Native

theorem uClasses_check : uClasses.length = 25 ∧ uWitness.length = 25 ∧
    (∀ c < 25, classForestOK uClasses[c]! = true ∧ classWitOK uClasses[c]! uWitness[c]! = true) ∧
    ∀ e < 1024, e ≠ 0 → quadSelf e = true → ∃ c < 25, e ∈ (uClasses[c]!).map Prod.fst :=
  Certificates.certificate2174.1

theorem genInv_size : ∀ i < 4, ∀ j < 11, (genInvColumns[i]!)[j]! < 2048 :=
  Certificates.certificate2174.2.1

theorem uSpecial_check : fixCount elementColumns[118]! = 128 ∧
    fixCount elementColumns[448]! = 128 ∧ fixCount elementColumns[502]! = 128 ∧
    comp11 elementColumns[448]! elementColumns[502]! = elementColumns[118]! ∧
    comp11 elementColumns[118]! elementColumns[448]! = elementColumns[502]! ∧
    comp11 elementColumns[118]! elementColumns[118]! = idRows 11 ∧
    comp11 elementColumns[448]! elementColumns[448]! = idRows 11 ∧
    (∀ i < 4, (conjTab[i]!)[118]! = 118) ∧
    (∀ i < 4, (conjTab[i]!)[448]! = 448 ∨ (conjTab[i]!)[448]! = 502) ∧
    (∀ i < 4, (conjTab[i]!)[502]! = 448 ∨ (conjTab[i]!)[502]! = 502) ∧
    (∃ i < 4, (conjTab[i]!)[448]! = 502) ∧
    ((Finset.range 2048).filter fun a =>
      app11 elementColumns[118]! a = a ∧ app11 elementColumns[448]! a = a).card = 32 ∧
    (∀ c ∈ [0, 118, 448, 502], ∀ c' ∈ [0, 118, 448, 502], ∀ v < 2048, quadAt c c' v = true) ∧
    (∀ c ∈ [0, 118, 448, 502], ∀ c' ∈ [0, 118, 448, 502], ∃ d ∈ [0, 118, 448, 502],
      comp11 elementColumns[c]! elementColumns[c']! = elementColumns[d]!) ∧
    (∀ c ∈ [118, 448, 502], comp11 elementColumns[c]! elementColumns[c]! = elementColumns[0]!) ∧
    (∀ i < 4, (conjTab[i]!)[448]! ≠ (conjTab[i]!)[502]!) ∧
    ((Finset.range 2048).filter fun a => app11 elementColumns[118]! a = a).card = 128 :=
  Certificates.certificate2174.2.2

end CFSG.Sporadic.J4Schreier
