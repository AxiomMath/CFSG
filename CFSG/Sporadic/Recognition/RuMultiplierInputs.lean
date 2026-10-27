module

public import CFSG.LieType.Multipliers.TitsCheckInputs
public import CFSG.Sporadic.Presentation.RuExactInputs
public import Certificates.Data.CFSGNative.Bridge.SurjD
public import CFSG.Sporadic.Recognition.RuMultiplierData
public import CFSG.Certificates.WordSubgroup

public section

namespace CFSG.Sporadic.Recognition.RuMultiplier

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Presentation.Ru.Exact
  CFSG.Sporadic.Bridge.SurjD.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Tits
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.LieType.Multipliers.Tits

abbrev ruW (c : List ℕ) : List (Fin gc × Bool) := wordOfCodes gc c

@[expose] def ruCommCodes : ℕ → List (List ℕ × List ℕ)
  | 0 => [([4, 0, 0, 4, 1, 4, 0], [4, 1]), ([4, 0, 4, 0, 0, 4, 1], [4, 0, 0, 4, 0, 4, 0, 0])]
  | 1 => [([0], [2, 1, 2, 1, 2]), ([0, 2, 1], [1, 2])]
  | _ => [([0], [4, 1, 4, 0, 4, 1, 4]), ([0, 4, 1, 4, 0, 4, 1], [1, 4, 0, 4, 1, 4, 0])]

@[expose] def ruCommWord (i : Fin gc) : List (Fin gc × Bool) :=
  commWords ((ruCommCodes i.val).map fun p => (ruW p.1, ruW p.2))

abbrev ruCover : List (List (Fin gc × Bool)) := coverWords W0 ruCommWord

@[expose] def ruA : List (Fin gc × Bool) := ruW [0, 0]

@[expose] def ruB : List (Fin gc × Bool) := ruW [4, 1, 2, 0, 2, 1, 2, 0, 2, 0, 2, 1, 2, 4]

@[expose] def ruC : List (Fin gc × Bool) :=
  ruA ++ ruB ++ ruA ++ ruB ++ ruA ++ FreeGroup.invRev ruB ++ ruA

@[expose] def ruAbc : List (List (Fin gc × Bool)) := [ruA, ruB, ruC]

@[expose] def ruUInAbc : List (Fin 3 × Bool) := wordOfCodes 3 [5, 3, 0, 2, 0, 4, 2, 5, 2]

@[expose] def ruTInAbc : List (Fin 3 × Bool) :=
  wordOfCodes 3 [3, 0, 5, 3, 4, 2, 0, 3, 4, 3, 5, 2, 0, 5]

@[expose] def natWord (w : List (Fin gc × Bool)) : List (ℕ × Bool) := w.map fun l => (l.1.val, l.2)

@[expose] def ruTabWords : List (List (Fin gc × Bool)) :=
  (List.finRange gc).map (fun i => (i, false) :: ruCommWord i) ++
    titsOneWords.map (substWord ruAbc) ++
    [ruW [1] ++ substWord ruAbc ruUInAbc, ruW [5] ++ substWord ruAbc ruTInAbc]

@[noinline, expose] def ruTabCheck : Bool :=
  let D := CFSG.Sporadic.Ru.Native.ruData
  let O := D.orbit ()
  let G := #[O.alpha, invT D.n O.alpha, O.beta, invT D.n O.beta]
  let I := ruSpec.imgWords.map (wordT D.n (baseLetter G))
  let Iv := I.map (invT D.n)
  ruTabWords.all fun w => wordT D.n (imgLetter I Iv) ((natWord w).map letterOf) == idT D.n

@[expose] def ruRhoArrs : Array (Array ℕ) :=
  #[hexTable 4 16240 0 ruRhoText, hexTable 4 16240 16240 ruRhoText,
    hexTable 4 16240 32480 ruRhoText]

@[expose] def ruP0 : List (Fin gc × Bool) := toLetters gc ruSpec.surjWords[0]!

@[noinline, expose] def ruRhoCheck : Bool :=
  allPermsOK 16240 ruRhoArrs &&
    ruCover.all (fun w => lettersOK gc (zword w) &&
      eqA 16240 (wordArr 16240 ruRhoArrs (zword w)) (idA 16240)) &&
    lettersOK gc (zword (ruP0 ++ ruP0)) &&
    !eqA 16240 (wordArr 16240 ruRhoArrs (zword (ruP0 ++ ruP0))) (idA 16240)

end CFSG.Sporadic.Recognition.RuMultiplier
