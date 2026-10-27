module

public import CFSG.RankThree.PartOne.KS.ONPwInputs
public import CFSG.Sporadic.Schreier.ONPermArr
public import CFSG.Sporadic.ONOddCore.FirstDiscovery

public section

namespace CFSG.RankThree.PartOne.ONPw

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native CFSG.Sporadic.ONOddCore

abbrev PermN : Type := Equiv.Perm (Fin nPts)

structure Env where
  evalS : List ℤ → PermN
  prep : ∀ {w : List ℤ}, plettersOK 7 w = true → PRep nPts (wArr w) (evalS w)
  Pv : Subgroup PermN
  L : Subgroup PermN
  L_le : L ≤ Pv
  L_closure : L = Subgroup.closure {g | g ∈ CFSG.ONSchreier.Data.LWords.toList.map evalS}
  sep : ∀ g ∈ Pv, ∀ h ∈ Pv, (∀ p : Fin nPts, p.val ∈ baseA.toList → g p = h p) → g = h

@[expose] def evalFP (als kps : ℕ → PermN) (w : List ℕ) : PermN :=
  (w.map fun l => if l < 3 then als l else kps (l - 3)).prod

namespace Env

variable (E : Env)

@[expose] def bP : PermN := E.evalS bW
@[expose] def zP : PermN := E.evalS zW
@[expose] def y0P : PermN := E.evalS y0W
@[expose] def x0P : PermN := E.evalS x0W
@[expose] def kP (j : ℕ) : PermN := E.evalS (kW j)
@[expose] def yP : PermN := E.bP⁻¹ * E.y0P * E.bP
@[expose] def xP : PermN := E.bP⁻¹ * E.x0P * E.bP
@[expose] def kpP (j : ℕ) : PermN := E.bP⁻¹ * E.kP j * E.bP
@[expose] def hP : List PermN := CFSG.ONSchreier.Data.MWords.toList.map E.evalS
@[expose] def liftImgP (q j : ℕ) : PermN := evalPos E.hP ((liftWords[q]!)[j]!)
@[expose] def liftImgsP (q : ℕ) : List PermN := (List.range 3).map (E.liftImgP q)
@[expose] def byP (q : ℕ) : PermN := evalPos (E.liftImgsP q) yLetters

end Env

structure Facts (E : Env) : Prop where
  b_conj : E.bP * E.zP * E.bP⁻¹ = E.y0P ^ 14
  y_word : E.yP = evalPos E.hP yLetters
  x_comm : ∀ j < 4, E.xP * E.kpP j = E.kpP j * E.xP
  z_ncomm : ∃ j < 4, E.zP * E.kpP j ≠ E.kpP j * E.zP
  x0_pow : E.x0P ^ 7 = 1
  x_pow : E.xP ^ 7 = 1
  filt_orig : evalFP (fun j => E.hP.getD j 1) E.kpP wF ^ 8 = 1
  surv : ∀ q < nLifts, ∀ l ∈ E.L, l * E.byP q * l⁻¹ = E.yP →
    (∃ i < 7, ∀ j < 3, l * E.liftImgP q j * l⁻¹ = E.xP ^ i * E.hP.getD j 1 * (E.xP ^ i)⁻¹) ∨
      evalFP (fun j => l * E.liftImgP q j * l⁻¹) E.kpP wF ^ 8 ≠ 1

end CFSG.RankThree.PartOne.ONPw
