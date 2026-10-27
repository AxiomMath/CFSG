module

public import Certificates.Data.CFSGNative.SporLat.Build
public import Certificates.Data.E68Spor.Gr

public section

namespace CFSG.Quasithin.E6.Spor

open CFSG.QuasithinUnique.Ch1.SporLat

@[expose] def idTab' (n : Nat) : Array Nat := Array.range n

@[expose] def lettersLt (m : Nat) (w : List Nat) : Bool := w.all fun l => decide (l < m)

@[expose] def classChk (n : Nat) (ta tb zT : Array Nat) (s : Nat) : Bool :=
  let Δ := grLabel n zT
  let O := (buildOmega (grAct n) #[ta, tb] Δ (s + 1)).1
  (List.range n).all (fun p => decide (zT.getD p 0 < n)) &&
    decide (OmegaSpec (grAct n) #[ta, tb] Δ O) && (O.lbl.size == s)

variable {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab]

@[expose] def rChk (n : Nat) (act : Array Nat → Lab → Lab) (Δ : Lab) (sTabs : List (Array Nat))
    (ta tb zT : Array Nat) (uWords : List (List Nat)) (yw nw : List Nat) (r m : Nat) : Bool :=
  let uTabs := uWords.map (wordTabA #[ta, tb] n)
  let OH := (buildOmega act (sTabs ++ uTabs).toArray Δ (m + 1)).1
  let yT := wordTabA (sTabs ++ uTabs).toArray n yw
  let nT := wordTabA sTabs.toArray n nw
  uWords.all (lettersLt 2) && lettersLt (sTabs.length + uWords.length) yw &&
    lettersLt sTabs.length nw &&
    decide (OmegaSpec act (sTabs ++ uTabs).toArray Δ OH) && (OH.lbl.size == m) &&
    uTabs.all (fun uT => wordTabA #[uT, zT] n [0, 1] == wordTabA #[uT, zT] n [1, 0]) &&
    (wordTabA #[yT] n (List.replicate r 0) == idTab' n) && (yT != idTab' n) &&
    (wordTabA #[yT, zT] n [0, 1] == wordTabA #[yT, zT] n [1, 0]) &&
    (List.range OH.lbl.size).all (fun i => decide (act nT OH.lbl[i]! = OH.lbl[i]!)) &&
    (wordTabA #[yT, nT] n [0, 1] != wordTabA #[yT, nT] n [1, 0])

@[expose] def ncChk (n : Nat) (ta zT : Array Nat) : Bool :=
  wordTabA #[ta, zT] n [0, 1] != wordTabA #[ta, zT] n [1, 0]

end CFSG.Quasithin.E6.Spor
