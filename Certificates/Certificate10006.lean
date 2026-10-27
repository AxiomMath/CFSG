module

public import CFSG.LieType.Multipliers.O73DataInputs
import Certificates.Kernel.Misc.O73Bridge
public import Certificates.Certificate10103

public section

namespace Certificates

open CFSG.LieType CFSG.LieType.Multipliers CFSG.LieType.Multipliers.O73 CFSG.YGroups
  CFSG.YGroups.ModelNative CFSG.Monster.B.Co2.Native Matrix in
theorem certificate10006 :
    (∀ x : Fin 2187, code (dec x) = x)
    ∧ ((∀ i : Fin 8, q3 (vecs i) = 2) ∧ tTabs.size = 8 ∧ rTabs.size = 8 ∧
      (∀ i : Fin 8, tMat (vecs i) * tMat (vecs i) = 1 ∧ rMat (vecs i) * rMat (vecs i) = 1) ∧
      permsOK 2187 tTabs = true ∧ permsOK 2187 rTabs = true ∧
      (∀ i : Fin 8, ∀ x : Fin 2187, q3 (tMat (vecs i) *ᵥ dec x) = q3 (dec x)))
    ∧ (relatorsOK 2187 tTabs (yRels 3 2 2 ++ eWords) = true ∧
      relatorsOK 2187 rTabs (yRels 3 2 2) = true ∧
      liftArrs.size = 8 ∧ permsOK 1134 liftArrs = true ∧
      relatorsOK 1134 liftArrs eWords = true ∧
      eqA 1134 (evalW 1134 liftArrs spW) (idA 1134) = false)
    ∧ (betaArr.size = 728 ∧ (∀ x : Fin 728, betaArr[x.val]! < 2187) ∧
      (∀ x y : Fin 728, betaArr[x.val]! = betaArr[y.val]! → x = y) ∧
      ∀ i : Fin 8, ∀ x : Fin 728,
      (rTabs[i.val]!)[betaArr[x.val]!]! = betaArr[(y322Arrays[i.val]!)[x.val]!]!) := CFSG.KD.Misc.O73.facts

end Certificates
