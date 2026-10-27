module

public import Certificates.Data.E64Aut

public section

namespace Certificates.E64Facts

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
  CFSG.ClassicalInvolution.Q3.E64Data Certificates.AE117 Certificates.E64Aut

@[expose] def memS (ℓ : Finset (Fin 7)) : List (Wr 7) := memAtL ℓᶜ true ++ memAtL ℓᶜ false

@[expose] def centLC (p q r : Fin 7) (α : List (Fin 7)) : List (Wr 7) :=
  [[], [p, q], [p, r], [q, r]].flatMap fun s => [⟨indL s, 1⟩, ⟨indL (α ++ s), 1⟩]

@[expose] def centAt (ℓ : Finset (Fin 7)) : List (Wr 7) :=
  match ℓ.sort (· ≤ ·) with
  | [p, q, r] => centLC p q r (ℓᶜ.sort (· ≤ ·))
  | _ => []

@[expose] def commAll (S : List (Wr 7)) (x : Wr 7) : Bool := S.all fun s => eqPi (x * s) (s * x)

@[expose] def centOK (Lc : Finset (Equiv.Perm (Fin 7))) (Ev : Finset (Fin 7 → ZMod 2))
    (S C : List (Wr 7)) : Bool :=
  C.all (fun c => inM c && commAll S c) &&
    finAll Lc fun τ => !(S.all fun s => decide (τ * s.perm = s.perm * τ)) ||
      finAll Ev fun v => !(commAll S ⟨v, τ⟩) || C.any fun c => eqPi ⟨v, τ⟩ c

@[expose] def distinctPi (C : List (Wr 7)) : Bool := decide (C.Pairwise fun c d => eqPi c d = false)

@[expose] def a7 (_ : Unit := ()) : List (Wr 7) :=
  (List.finRange 7).map fun i => ⟨fun j => if j = i then 0 else 1, 1⟩

@[expose] def g1Check (_ : Unit := ()) : Bool :=
  let Lc := l32Fin ()
  let Ev := evenFin ()
  fanoLines.all fun ℓ =>
    let C := centAt ℓ
    centOK Lc Ev (memS ℓ) C && decide (C.length = 8) && distinctPi C &&
      C.all (fun c => decide (c * c = 1)) && C.all fun c => C.all fun d => decide (c * d = d * c)

@[expose] def g2Check (_ : Unit := ()) : Bool :=
  let A := a7 ()
  (fanoLines.all fun ℓ => fanoLines.all fun ℓ' => decide (ℓ = ℓ') ||
    (centAt ℓ).all fun c => !commAll (memS ℓ') c || eqPi c 1 || A.any (eqPi c)) &&
  distinctPi A &&
  A.all fun a => inM a && decide (a * a = 1) && !eqPi a 1 &&
    decide ((fanoLines.filter fun ℓ => commAll (memS ℓ) a).length = 3)

@[expose] def a7Conj (_ : Unit := ()) : List (Equiv.Perm (Fin 7)) :=
  [cycPerm [], cycPerm [[0, 1], [2, 5]], cycPerm [[0, 2], [1, 5]], cycPerm [[0, 3], [2, 4]],
    cycPerm [[0, 4], [1, 6]], cycPerm [[0, 5], [1, 2]], cycPerm [[0, 6], [1, 4]]]

@[expose] def conjCheck (_ : Unit := ()) : Bool :=
  let A := a7 ()
  let G := a7Conj ()
  (List.range 7).all fun k =>
    let g := ofPerm (G.getD k 1)
    inM g && eqPi (g * A.getD 0 1 * g⁻¹) (A.getD k 1)

end Certificates.E64Facts
