module

public import CFSG.Sporadic.J4.F2Spec
public import CFSG.Sporadic.J4.ParSpec
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.J4.Cert
import all Certificates.Data.CFSGNative.J4.F2
import all Certificates.Data.CFSGNative.J4.Data
import all Certificates.Data.CFSGNative.J4.Cert
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Sporadic.J4

open Native Matrix

noncomputable abbrev matA : Matrix (Fin 112) (Fin 112) (ZMod 2) :=
  Blueprint.NativeSporadic.decode 2 112 1 Blueprint.NativeSporadic.J4Seed1

noncomputable abbrev matB : Matrix (Fin 112) (Fin 112) (ZMod 2) :=
  Blueprint.NativeSporadic.decode 2 112 1 Blueprint.NativeSporadic.J4Seed2

private theorem seedA_eq' : seedA = Blueprint.NativeSporadic.J4Seed1 := rfl

private theorem seedB_eq' : seedB = Blueprint.NativeSporadic.J4Seed2 := rfl

theorem rowsMatrix_rowsA : rowsMatrix rowsA = matA := by
  rw [rowsA, rowsMatrix_rowsOf, seedA_eq']

theorem rowsMatrix_rowsB : rowsMatrix rowsB = matB := by
  rw [rowsB, rowsMatrix_rowsOf, seedB_eq']

@[expose] def wordProd {G : Type*} [Group G] (gs : ℕ → G) (w : List ℤ) : G :=
  (w.map fun l => if 0 < l then gs (l.toNat - 1) else (gs ((-l).toNat - 1))⁻¹).prod

theorem wordProd_mem {G : Type*} [Group G] (K : Subgroup G) {gs : ℕ → G} (h : ∀ m, gs m ∈ K)
    (w : List ℤ) : wordProd gs w ∈ K := by
  unfold wordProd
  induction w with
  | nil => exact K.one_mem
  | cons l w ih =>
    rw [List.map_cons, List.prod_cons]
    refine K.mul_mem ?_ ih
    split_ifs
    · exact h _
    · exact K.inv_mem (h _)

theorem rowsMatrix_wordRows {mats invs : Array (Array V2)} {gs : ℕ → GL (Fin 112) (ZMod 2)}
    (hm : ∀ m, rowsMatrix (mats[m]?.getD idRows) = ((gs m : GL (Fin 112) (ZMod 2)) :
      Matrix (Fin 112) (Fin 112) (ZMod 2)))
    (hi : ∀ m, rowsMatrix (invs[m]?.getD idRows) = (((gs m)⁻¹ : GL (Fin 112) (ZMod 2)) :
      Matrix (Fin 112) (Fin 112) (ZMod 2)))
    (w : List ℤ) :
    rowsMatrix (wordRows mats invs w) =
      ((wordProd gs w : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) := by
  unfold wordRows wordProd
  suffices ∀ (acc : Array V2) (g : GL (Fin 112) (ZMod 2)),
      rowsMatrix acc = (g : Matrix (Fin 112) (Fin 112) (ZMod 2)) →
      rowsMatrix (w.foldl (fun acc l => mulRows acc (if 0 < l then mats[l.toNat - 1]?.getD idRows
        else invs[(-l).toNat - 1]?.getD idRows)) acc) =
        ((g * (w.map fun l => if 0 < l then gs (l.toNat - 1) else (gs ((-l).toNat - 1))⁻¹).prod :
          GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) by
    simpa using this idRows 1 (by rw [rowsMatrix_idRows]; rfl)
  induction w with
  | nil => intro acc g h; simpa using h
  | cons l w ih =>
    intro acc g h
    rw [List.foldl_cons, List.map_cons, List.prod_cons, ← mul_assoc]
    apply ih
    rw [rowsMatrix_mulRows, h, Units.val_mul]
    congr 1
    split_ifs
    · exact hm _
    · exact hi _

structure MatFacts : Prop where
  baseInv : invsOK baseMats baseInvs = true
  locInv : invsOK (locMats ()) (locInvs ()) = true
  locSize : (locMats ()).size = 3
  stabSize : (stabMats ()).size = 6
  locFix : (locMats ()).all (fun M => (frApply (frTable M) rootV).beq rootV) = true
  a2 : eqRows (powRows rowsA 2) idRows = true
  a1 : eqRows rowsA idRows = false
  b4 : eqRows (powRows rowsB 4) idRows = true
  b2 : eqRows (powRows rowsB 2) idRows = false
  ab37 : eqRows (powRows (mulRows rowsA rowsB) 37) idRows = true
  ab1 : eqRows (mulRows rowsA rowsB) idRows = false
  cinv : eqRows (mulRows conjRows (invRows conjRows)) idRows = true
  z43 : eqRows (powRows zRows 43) idRows = true
  z1 : eqRows zRows idRows = false
  formA : eqRows (mulRows (mulRows rowsA formRows) (transposeRows rowsA)) formRows = true
  formB : eqRows (mulRows (mulRows rowsB formRows) (transposeRows rowsB)) formRows = true

private theorem false_of_not {b : Bool} (h : (!b) = true) : b = false := by
  cases b <;> simp_all

theorem matFacts_of (h : matChecks = true) : MatFacts := by
  unfold matChecks at h
  obtain ⟨h, h16⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨h, h15⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨h, h14⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨h, h13⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨h, h12⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨h, h11⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨h, h10⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨h, h9⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨h, h8⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨h, h7⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨h, h6⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨h, h5⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨h, h4⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨h, h3⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
  exact ⟨h1, h2, beq_iff_eq.mp h3, beq_iff_eq.mp h4, h5, h6, false_of_not h7, h8,
    false_of_not h9, h10, false_of_not h11, h12, h13, false_of_not h14, h15, h16⟩

theorem rowsMatrix_ne_of_eqRows_false {X Y : Array V2} (hX : X.size = 112) (hY : Y.size = 112)
    (hXw : ∀ x ∈ X, x.wf = true) (hYw : ∀ y ∈ Y, y.wf = true) (h : eqRows X Y = false) :
    rowsMatrix X ≠ rowsMatrix Y := by
  intro e
  apply Bool.false_ne_true
  rw [← h, eqRows_iff]
  refine Array.ext (by rw [hX, hY]) fun i h1 h2 => ?_
  apply V2.eq_of_toVec_eq (hXw _ (Array.getElem_mem h1)) (hYw _ (Array.getElem_mem h2))
  funext j
  have := congrFun (congrFun e ⟨i, by omega⟩) j
  rwa [rowsMatrix_apply, rowsMatrix_apply, Array.getElem?_eq_getElem h1,
    Array.getElem?_eq_getElem h2, Option.getD_some, Option.getD_some] at this

end CFSG.Sporadic.J4
