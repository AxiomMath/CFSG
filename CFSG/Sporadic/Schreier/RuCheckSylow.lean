
module

public import CFSG.Sporadic.Schreier.RuCheckSylowBase

public import CFSG.Sporadic.Schreier.RuCheckChains
public import CFSG.Sporadic.Schreier.RuEnum
public meta import CFSG.Sporadic.Schreier.RuCheckChains
public meta import CFSG.Sporadic.Schreier.RuEnum
public import CFSG.Sporadic.Schreier.RuCheckSylowInputs
public import Certificates.Certificate2258

public section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem ruSylow_check :
    (∀ j < 4, isInvA 1920 (ruSF j) (invCand 1920 (ruSF j)) = true) ∧
    (∀ i < 5, ∀ j < 4, ruSift 1920 (ruField1920 4) ruRBase
      (compA 1920 (compA 1920 (ruSF j) (ruRF i)) (invCand 1920 (ruSF j))) = true) ∧
    (∀ i < 4, ∀ j < 4, ruSift 1920 (ruField1920 4) ruRBase
      (ruCommA 1920 (ruSF i) (ruSF j)) = true) ∧
    (∀ i < 4, ruSift 1920 (ruField1920 4) ruRBase (compA 1920 (ruSF i) (ruSF i)) = true) ∧
    ruSift 1920 (ruField1920 4) ruRBase (ruSF 1) = true ∧
    all2 1920 (rawLevels 1920 (ruField1920 1) (ruBaseArr 1920 ruSBase)) (fun g =>
      !(ruCommutesS g) || eqA 1920 g (idA 1920) || eqA 1920 g ruZF) = true :=
  Certificates.certificate2258

end CFSG.Sporadic.RuSchreier
