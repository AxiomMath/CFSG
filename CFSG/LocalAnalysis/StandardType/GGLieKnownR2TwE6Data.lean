module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6Rad
public import CFSG.LieType.Steinberg.Minuscule.CertInputs

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.Blueprint.Chevalley
  CFSG.LieType.Steinberg.Minuscule
open scoped commutatorElement

@[expose] def twE6Lift : Fin 8 → (Fin (Tag.rank .E6) → ℤ) :=
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 1], ![0, 0, 0, 1, 1, 1], ![0, 0, 1, 1, 1, 1],
    ![0, 1, 0, 1, 1, 1], ![0, 1, 1, 1, 1, 1], ![0, 1, 1, 2, 1, 1], ![0, 1, 1, 2, 2, 1]]

@[expose] def twE6Gamma : Fin 8 → (Fin (Tag.rank .F4) → ℤ) :=
  ![![0, 0, 0, 1], ![0, 0, 1, 1], ![0, 1, 1, 1], ![0, 1, 2, 1], ![1, 1, 1, 1], ![1, 1, 2, 1],
    ![1, 2, 2, 1], ![1, 2, 3, 1]]

@[expose] def twE6Long : Fin 12 → (Fin (Tag.rank .E6) → ℤ) :=
  ![![0, -1, -1, -2, -1, 0], ![0, -1, -1, -1, -1, 0], ![0, -1, 0, -1, 0, 0],
    ![0, -1, 0, 0, 0, 0], ![0, 0, -1, -1, -1, 0], ![0, 0, 0, -1, 0, 0], ![0, 0, 0, 1, 0, 0],
    ![0, 0, 1, 1, 1, 0], ![0, 1, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0], ![0, 1, 1, 1, 1, 0],
    ![0, 1, 1, 2, 1, 0]]

@[expose] def twE6Delta : Fin 12 → (Fin (Tag.rank .F4) → ℤ) :=
  ![![-1, -2, -2, 0], ![-1, -1, -2, 0], ![-1, -1, 0, 0], ![-1, 0, 0, 0], ![0, -1, -2, 0],
    ![0, -1, 0, 0], ![0, 1, 0, 0], ![0, 1, 2, 0], ![1, 0, 0, 0], ![1, 1, 0, 0], ![1, 1, 2, 0],
    ![1, 2, 2, 0]]

@[expose] def twE6Shift (j : Fin 12) (i : Fin 8) : Option (Fin 8) :=
  (List.finRange 8).find? fun i' => decide (twE6Lift i + twE6Long j = twE6Lift i')

@[expose] def twE6Perm : Fin 8 → Fin 8 := ![1, 0, 3, 2, 5, 4, 7, 6]

@[expose] def twE6ShortNode : Fin (Tag.rank .F4) := ⟨2, by decide⟩

@[expose] def twE6Exp2 : Fin 8 → ℤ := ![0, 0, -1, 1, -1, 1, 0, 0]

@[expose] def twE6Exp4 : Fin 8 → ℤ := ![-1, 1, 0, 0, 0, 0, -1, 1]

@[expose] def memE6 (v : Fin (Tag.rank .E6) → ℤ) : Bool :=
  (Tag.stringData .E6).memDec (Tag.rootCertificate .E6) v

@[expose] def memF4 (v : Fin (Tag.rank .F4) → ℤ) : Bool :=
  (Tag.stringData .F4).memDec (Tag.rootCertificate .F4) v

@[expose] def twE6DataCheck : Bool :=
  (List.finRange 8).all (fun i =>
    memE6 (twE6Lift i) && decide (rho (twE6Lift i) ≠ twE6Lift i) &&
      decide (proj (twE6Lift i) = twE6Gamma i) && memF4 (twE6Gamma i) &&
      decide (twE6Gamma i twE6Last = 1)) &&
  (List.finRange 8).all (fun i => (List.finRange 8).all fun i' =>
    decide (i = i') || decide (twE6Gamma i ≠ twE6Gamma i')) &&
  (List.range (Tag.rootCertificate .F4).roots.length).all (fun m =>
    decide ((Tag.rootCertificate .F4).root m twE6Last ≠ 1) ||
      (List.finRange 8).any fun i => decide (twE6Gamma i = (Tag.rootCertificate .F4).root m)) &&
  (List.finRange 12).all (fun j =>
    memE6 (twE6Long j) && decide (rho (twE6Long j) = twE6Long j) &&
      decide (proj (twE6Long j) = twE6Delta j) && memF4 (twE6Delta j) &&
      decide (twE6Delta j twE6Last = 0)) &&
  (List.finRange 12).all (fun j => (List.finRange 8).all fun i =>
    (memE6 (twE6Lift i + twE6Long j) == (twE6Shift j i).isSome) &&
      (memF4 (twE6Gamma i + twE6Delta j) == (twE6Shift j i).isSome) &&
      (!(twE6Shift j i).isSome ||
        (memE6 (twE6Lift i + rho (twE6Lift i) + twE6Long j) &&
          decide (rho (twE6Lift i + rho (twE6Lift i) + twE6Long j) =
            twE6Lift i + rho (twE6Lift i) + twE6Long j)))) &&
  (List.finRange 8).all (fun i =>
    decide (twE6Gamma i + twE6Gamma i.rev = twE6Alpha) &&
      memE6 (twE6Lift i + rho (twE6Lift i.rev)) && !memE6 (twE6Lift i + twE6Lift i.rev)) &&
  (List.finRange 8).all (fun i =>
    decide (reflect .E6 (nd 2) (reflect .E6 (nd 4) (twE6Lift i)) = twE6Lift (twE6Perm i)) &&
      decide (MinData.toWeight (twE6Lift i) (nd 2) = twE6Exp2 i) &&
      decide (MinData.toWeight (twE6Lift i) (nd 4) = twE6Exp4 i))

theorem twE6DataCheck_eq : twE6DataCheck = true := by
  decide +kernel

end CFSG.StandardType.LieKnownR2.Short
