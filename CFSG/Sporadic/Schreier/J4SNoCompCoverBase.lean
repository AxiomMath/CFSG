
module

public import CFSG.Sporadic.Schreier.J4SNoCompCheckBase
public import CFSG.Sporadic.Schreier.J4SKernelBase
public import CFSG.Sporadic.Schreier.J4SOddLocalBase
public import CFSG.Sporadic.Schreier.J4SFormBase
public import CFSG.Sporadic.J4.PrimSpec
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SFormData
public import CFSG.Sporadic.Schreier.J4SNoCompData
public meta import CFSG.Sporadic.Schreier.J4SNoCompData
public import CFSG.Sporadic.Schreier.J4SOrbitsBase
public meta import CFSG.Sporadic.Schreier.J4SOrbitsBase
public import CFSG.Sporadic.J4.Local

@[expose] public noncomputable section

namespace CFSG.Sporadic.J4Schreier.NoComp

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2
open CFSG.Sporadic.SmallF2.Native CFSG.SectionRank.Native MulAction
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem unMats_get (j : Fin 11) : unMats[j.val]! = (Un j).1 := by
  unfold unMats
  rw [getElem!_pos _ j.val (by simp), Array.getElem_ofFn]

@[expose] def mRep (l : ℕ) : J := signedWord a b repWords[l]!

theorem mRep_zero : mRep 0 = 1 := rfl

theorem repVecs_get {l : ℕ} (hl : l < 7) : repVecs[l]! = O.vmul rootBits (repPair l).1 := by
  unfold repVecs
  rw [getElem!_pos _ l (by simpa using hl), Array.getElem_ofFn]

@[expose] def fixCard (w : Row) : ℕ := Nat.card (N ⊓ stabilizer J w : Subgroup J)

theorem toVecD_injOn {x y : ℕ} (h : toVecD 112 x = toVecD 112 y) (hx : x = y ∨ O.vne x y = true) :
    x = y := by
  rcases hx with hx | hx
  · exact hx
  · exact absurd h (Sp.toVec_ne hx)

@[expose] def bilV (w : Row) : ZMod 2 := ofRow v ⬝ᵥ (formF *ᵥ ofRow w)

theorem dot_toVecD (x : Fin 112 → ZMod 2) (V : ℕ) :
    x ⬝ᵥ toVecD 112 V = (x ᵥ* rowsMatrix 112 (colRows V)) 0 := by
  have hcol : ∀ i : Fin 112, rowsMatrix 112 (colRows V) i 0 = toVecD 112 V i := by
    intro i
    have e : (colRows V)[i.val]?.getD 0 = if V.testBit i.val then 1 else 0 := by
      unfold colRows
      rw [Array.getElem?_ofFn, dite_eq_left i.isLt, Option.getD_some]
    rw [SmallF2.rowsMatrix_apply, e, toVecD_apply, toVecD_apply]
    by_cases hb : V.testBit i.val
    · simp [hb]
    · simp [hb]
  simp only [Matrix.vecMul, dotProduct, hcol]

theorem vmul_eq (u : ℕ) (X : Array ℕ) : O.vmul u X = vecMulN 112 X u := rfl

theorem ofRow_toRow (w : Fin 112 → ZMod 2) : ofRow (toRow w) = w := rfl

theorem toVecD_zero_apply (n : ℕ) : toVecD 112 n 0 = if n.testBit 0 then 1 else 0 := rfl

theorem bilV_toRow (V : ℕ) :
    bilV (toRow (toVecD 112 V)) = if bilB rootBits V then 1 else 0 := by
  unfold bilV bilB
  rw [vmul_eq, vmul_eq, ← toVecD_zero_apply, toVecD_vecMulN, toVecD_vecMulN, ← dot_toVecD,
    Matrix.dotProduct_mulVec, v, ofRow_toRow, ofRow_toRow, formF]

theorem pathElt_eq_signedWord : ∀ p : List ℕ, (∀ l ∈ p, l = 1 ∨ l = 2) →
    CFSG.Sporadic.J4.QT2.pathElt p = CFSG.Sporadic.GLQ.signedWord a b (p.map Int.ofNat)
  | [], _ => rfl
  | l :: ls, h => by
    have ih := pathElt_eq_signedWord ls fun x hx => h x (List.mem_cons_of_mem _ hx)
    unfold CFSG.Sporadic.GLQ.signedWord at ih ⊢
    rw [CFSG.Sporadic.J4.QT2.pathElt, ih, List.map_cons, List.map_cons, List.prod_cons]
    congr 1
    rcases h l List.mem_cons_self with rfl | rfl
    · simp [CFSG.Sporadic.J4.QT2.letterElt, CFSG.Sporadic.GLQ.letter]
    · simp [CFSG.Sporadic.J4.QT2.letterElt, CFSG.Sporadic.GLQ.letter]

theorem pathElt_eq_mRep {l : ℕ} (hl : l < 7) :
    CFSG.Sporadic.J4.QT2.pathElt (CFSG.Sporadic.J4.QT2.repPaths.getD l []) = mRep l := by
  rw [pathElt_eq_signedWord _ (CFSG.Sporadic.J4.QT2.repPaths_letters l hl), mRep]
  congr 1
  interval_cases l <;> rfl

theorem repCounts_cases : ∀ l m : Fin 7, repCounts[m.val]! = repCounts[l.val]! →
    (l.val = 2 → m.val = 3 → False) → (l.val = 3 → m.val = 2 → False) → l = m := by
  decide

theorem conjTab_get {l : ℕ} (hl : l < 7) (j : Fin 11) :
    (conjTab[l]!)[j.val]! = (conjPair l j).1 := by
  unfold conjTab
  rw [getElem!_pos _ l (by simpa using hl), Array.getElem_ofFn,
    getElem!_pos _ j.val (by simp), Array.getElem_ofFn]
