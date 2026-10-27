module

public import CFSG.LocalAnalysis.StandardType.GGK0NormalForm
public import CFSG.LocalAnalysis.StandardType.GGK0RowOrbits

public section

namespace CFSG.StandardType.GGK0LQ

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.GGK0MarkedKacIface1587

variable {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
  {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}

@[expose] def lqNodes (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length) : List ℕ :=
  (P.orbitNodes j).headD []

@[expose] def lqTw (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length) : ℕ :=
  let D := k0DiagOf A.row.T
  let orb := P.orbitNodes j
  let c := orb.headD []
  let ct := k0CompType D c
  let o := k0AutOrder c (k0pPow A.row.rho orb.length)
  if A.row.d = 2 ∧ orb.length % 2 = 1 ∧ k0Tau0Of ct.1 ct.2 then
    (if o = 1 then 2 else if o = 2 then 1 else o)
  else o

end CFSG.StandardType.GGK0LQ

end
