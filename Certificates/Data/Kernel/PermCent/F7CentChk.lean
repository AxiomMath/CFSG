module

public import Certificates.Data.Kernel.PermCent.F7Cent
public import CFSG.GH74.GLS.C3.Layer2.NumMoved

public section

namespace CFSG.Certificates.Kernel.PkCV

@[expose] noncomputable def invP (x : CV 7 × CV 4) (n : Nat) : Bool :=
  decide (((x.1 * x.1 = 1 ∧ x.2 * x.2 = 1) ∧ ¬ (x.1 = 1 ∧ x.2 = 1)) ∧
    CFSG.GH74.GLS.C3.Layer2.numMoved (ev x.1) + CFSG.GH74.GLS.C3.Layer2.numMoved (ev x.2) = n)

@[expose] noncomputable def commP (x y : CV 7 × CV 4) : Bool :=
  eq22C x.1 y.1 y.1 x.1 && eq22C x.2 y.2 y.2 x.2

@[expose] noncomputable def cntP (L : List (CV 7 × CV 4)) (y : CV 7 × CV 4) : Nat :=
  L.countP fun x => commP x y

@[expose] noncomputable def powP (x y : CV 7 × CV 4) (n : Nat) (z : CV 7 × CV 4) : Bool :=
  decide ((x.1 * y.1) ^ n = z.1 ∧ (x.2 * y.2) ^ n = z.2)

@[expose] noncomputable def f7InvChk (Lf Lg : List (CV 7 × CV 4)) : Bool :=
  forceQL (Lf.filter fun x => invP x 4) fun X =>
  forceQL (Lf.filter fun x => invP x 8) fun Y =>
  forceQL (Lg.filter fun x => invP x 8) fun Yg =>
    (X.all fun x => Y.all fun y => powP x y 12 1) &&
    decide ((X ×ˢ Y).countP (fun p => (List.range 12).any fun n =>
      powP p.1 p.2 n (1, cOf CFSG.GH74.GLS.C3.Layer2.Model.x4)) = 27) &&
    decide (Y.countP (fun y => decide (cntP Lf y = 96)) = 3) &&
    decide (Y.countP (fun y => decide (cntP Lf y = 48)) = 6) &&
    (Y.all fun y => decide (cntP Lf y = 96 ∨ cntP Lf y = 48)) &&
    (Yg.all fun y => decide (cntP Lg y = 12))

@[expose] noncomputable def f7InvChkAt (ρ σ : CV 7) : Bool :=
  forceQL (CF7 ρ) fun Lf => forceQL (CF7 σ) fun Lg => f7InvChk Lf Lg

end CFSG.Certificates.Kernel.PkCV

end
