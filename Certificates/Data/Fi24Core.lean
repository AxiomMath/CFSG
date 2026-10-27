module

public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Sporadic.Fi24.RRefSpec
public import Certificates.Data.CFSGNative.Fi24.Certificate
public import Certificates.Data.Kernel.Spor.Fi24OrbL

public section

namespace CFSG.Sporadic.Fi24

open Native CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi23.Native Matrix

noncomputable abbrev mA : Matrix (Fin 781) (Fin 781) (ZMod 3) :=
  Blueprint.NativeSporadic.decode 3 781 1 Blueprint.NativeSporadic.Fi24primeSeed1

noncomputable abbrev mB : Matrix (Fin 781) (Fin 781) (ZMod 3) :=
  Blueprint.NativeSporadic.decode 3 781 1 Blueprint.NativeSporadic.Fi24primeSeed2

noncomputable abbrev mF : Matrix (Fin 781) (Fin 781) (ZMod 3) := matW 781 781 matF

noncomputable abbrev ptSub (k : ℕ) : Submodule (ZMod 3) (Fin 781 → ZMod 3) :=
  rowSpan 253 (formAt gensT orb rootForm k).rows

@[expose] def ChainOrbit (L : Array Table) (lv : Array ℕ) (y c : ℕ) : Prop :=
  ∃ P : Finset ℕ, P.card = c ∧ y ∈ P ∧ (∀ x ∈ P, x < 306936) ∧
    (∀ x ∈ P, ∀ l ∈ lv, ap L[l]! x ∈ P) ∧
    ∀ x ∈ P, ∃ w : List ℕ, (∀ l ∈ w, l ∈ lv) ∧ w.foldr (fun l z => ap L[l]! z) x = y

@[expose] def chainSizes : List ℕ := [306936, 275264, 218400, 93312, 243, 3]

structure CoreFacts : Prop where
  A_sq : mA * mA = 1
  B_cube : mB * (mB * mB) = 1
  AB_pow : (mA * mB) ^ 29 = 1
  A_ne : mA ≠ 1
  B_ne : mB ≠ 1
  AB_ne : mA * mB ≠ 1
  A_form : mAᵀ * mF * mA = mF
  B_form : mBᵀ * mF * mB = mF
  card : Nat.card (Subgroup.closure {g : GL (Fin 781) (ZMod 3) | g.val = mA ∨ g.val = mB}) =
    1255205709190661721292800
  alpha : ∀ k < 306936, ap orb.alpha k < 306936 ∧
    (ptSub k).map (Matrix.mulVecLin mA) = ptSub (ap orb.alpha k)
  beta : ∀ k < 306936, ap orb.beta k < 306936 ∧
    (ptSub k).map (Matrix.mulVecLin mB) = ptSub (ap orb.beta k)
  inj : ∀ i < 306936, ∀ j < 306936, ptSub i = ptSub j → i = j
  tree : ∀ k < 306936, 0 < k → ap orb.par k < k ∧
    ((ap orb.lab k = 1 ∧ ap orb.alpha (ap orb.par k) = k) ∨
      (ap orb.lab k = 2 ∧ ap orb.beta (ap orb.par k) = k))
  beta_inv : ∀ k < 306936, ap (invT 306936 orb.beta) (ap orb.beta k) = k
  slp_ok : slpOK chainWords = true
  letters_size : (chainLetters orb).size = 26
  letters : ∀ j < 13, ∀ x < 306936, ap (chainLetters orb)[2 * j]! x < 306936 ∧
    ap (chainLetters orb)[2 * j + 1]! (ap (chainLetters orb)[2 * j]! x) = x
  orbits : ∀ i < 6, ChainOrbit (chainLetters orb) (levelLetters (chainLetters orb) chainBase i)
    chainBase[i]! chainSizes[i]!
  sub_orbit : ChainOrbit (chainLetters orb) (levelLetters (chainLetters orb) chainBase 1) 1 31671

end CFSG.Sporadic.Fi24
