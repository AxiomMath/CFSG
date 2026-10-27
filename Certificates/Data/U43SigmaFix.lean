module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Inputs
public import Certificates.Data.CatFactsL4U4P1U43Defs
public import Certificates.Data.CFSGNative.SmallOddCore.Check
public import Certificates.Data.E4QuatArr

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E3S3O.U4M

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.SmallOddCore.Native
open CFSG.EvenSporadicStandard.M24Std.CU43 CFSG.ComponentClassification.HarrisLit.P1.U43
open CFSG.ClassicalInvolution.Q3.TL4.E4A

@[expose] def tabC (k : ℕ) : Array ℕ := natArr (tu k false)

@[expose] def codeR0 : ℕ := 1235367713451450

@[expose] def codeU0 : ℕ := 411785751150849

@[expose] def codeV0 : ℕ := 137354898085743

@[expose] def codeU1 : ℕ := 617683856755249

@[expose] def codeV1 : ℕ := 617683856676543

@[expose] def codeS01 : ℕ := 7625740974300

@[expose] def codeW0 : ℕ := 848452467420

@[expose] def codeY0 : ℕ := 1189732679211162

@[expose] def gamCodes : List ℕ :=
  [22908173855782, 45784966415719, 68661758713216, 137292136288051, 45784966028581,
    22908173521140]

@[expose] def r0A (_ : Unit := ()) : Array ℕ := tabC codeR0

@[expose] def u0A (_ : Unit := ()) : Array ℕ := tabC codeU0

@[expose] def v0A (_ : Unit := ()) : Array ℕ := tabC codeV0

@[expose] def u1A (_ : Unit := ()) : Array ℕ := tabC codeU1

@[expose] def v1A (_ : Unit := ()) : Array ℕ := tabC codeV1

@[expose] def twW (a b : Array ℕ) (w : List (Array ℕ)) : Bool :=
  allLt 820 fun i => evR w a[i]! == b[evR w i]!

end CFSG.ClassicalInvolution.Q3.TL4.E3S3O.U4M
