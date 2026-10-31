
module

public import CFSG.Sporadic.Th.BaseBase
public import CFSG.Sporadic.Th.Max3.DataBase
public import CFSG.Sporadic.ThSchreier.Text
public meta import Certificates.Data.CFSGNative.Th.Base
public import CFSG.Sporadic.ThSchreier.RowInputs
public import Certificates.Data.CFSGNative.Th.Base
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Matrix Pointwise

def RowV : Type := Fin 248 → ZMod 2

instance : AddCommGroup RowV := inferInstanceAs (AddCommGroup (Fin 248 → ZMod 2))

instance : Module (ZMod 2) RowV := inferInstanceAs (Module (ZMod 2) (Fin 248 → ZMod 2))

instance : DecidableEq RowV := inferInstanceAs (DecidableEq (Fin 248 → ZMod 2))

instance : Fintype RowV := inferInstanceAs (Fintype (Fin 248 → ZMod 2))

def toRow (v : Fin 248 → ZMod 2) : RowV := v

def ofRow (v : RowV) : Fin 248 → ZMod 2 := v

@[simp] theorem ofRow_toRow (v : Fin 248 → ZMod 2) : ofRow (toRow v) = v := rfl

@[simp] theorem toRow_ofRow (v : RowV) : toRow (ofRow v) = v := rfl

theorem toRow_add (u v : Fin 248 → ZMod 2) : toRow (u + v) = toRow u + toRow v := rfl

theorem toRow_zero : toRow 0 = 0 := rfl

theorem span_pair_eq {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (u v : M) :
    (Submodule.span (ZMod 2) {u, v} : Set M) = {0, u, v, u + v} := by
  ext w
  simp only [SetLike.mem_coe, Submodule.mem_span_pair, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  have hz : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  constructor
  · rintro ⟨s, t, rfl⟩
    rcases hz s with rfl | rfl <;> rcases hz t with rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, 0, by simp⟩
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
    · exact ⟨1, 1, by simp⟩

theorem linearIndependent_pair_of_ne {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] {u v : M}
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) : LinearIndependent (ZMod 2) ![u, v] := by
  rw [LinearIndependent.pair_iff]
  have hz : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  intro s t hst
  rcases hz s with rfl | rfl <;> rcases hz t with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · simp at hst; exact absurd hst hv
  · simp at hst; exact absurd hst hu
  · simp only [one_smul] at hst
    exact absurd (eq_neg_of_add_eq_zero_left hst |>.trans (ZModModule.neg_eq_self v)) huv

theorem finrank_span_pair_of_ne {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] {u v : M}
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {u, v}) = 2 := by
  have h := finrank_span_eq_card (linearIndependent_pair_of_ne hu hv huv)
  rw [Fintype.card_fin] at h
  rwa [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union] at h

def rowPlane (k : Key) : Set RowV :=
  {0, toRow k.u.toVec, toRow k.v.toVec, toRow k.u.toVec + toRow k.v.toVec}

theorem rowPlane_eq_image (k : Key) : rowPlane k = toRow '' keyPlane k := by
  simp only [rowPlane, keyPlane, Set.image_insert_eq, Set.image_singleton]
  rfl

theorem keyPlane_eq_image (k : Key) : keyPlane k = ofRow '' rowPlane k := by
  rw [rowPlane_eq_image, Set.image_image]
  simp [ofRow, toRow]

theorem rowPlane_canon (p q : V4) :
    rowPlane (canon p q) = {0, toRow p.toVec, toRow q.toVec, toRow p.toVec + toRow q.toVec} := by
  rw [rowPlane_eq_image, keyPlane_canon]
  simp only [Set.image_insert_eq, Set.image_singleton]
  rfl

theorem rowPlane_eq_span (k : Key) :
    rowPlane k = (Submodule.span (ZMod 2) {toRow k.u.toVec, toRow k.v.toVec} : Set RowV) := by
  rw [span_pair_eq]
  rfl

theorem eq_of_rowPlane_eq {k k' : Key} (hk : k.isCanonical = true) (hk' : k'.isCanonical = true)
    (h : rowPlane k = rowPlane k') : k = k' :=
  eq_of_keyPlane_eq hk hk' (by rw [keyPlane_eq_image, keyPlane_eq_image, h])

theorem frApply_frTable_vecMul (R : Array V4) (v : V4) :
    (frApply (frTable R) v).toVec = Matrix.vecMul v.toVec (rowsMatrix R) := by
  rw [frApply_frTable_toVec]
  funext i
  simp only [Matrix.vecMul, dotProduct, rowsMatrix_apply]

noncomputable abbrev formFInv : Matrix (Fin 248) (Fin 248) (ZMod 2) := rowsMatrix formInvRows

noncomputable def psi (u : V) : RowV := toRow (formF *ᵥ u)

theorem psi_add (u v : V) : psi (u + v) = psi u + psi v := by
  simp only [psi, Matrix.mulVec_add]
  rfl

theorem psi_zero : psi 0 = 0 := by
  simp only [psi, Matrix.mulVec_zero]
  rfl

def rowKeyOf (k : Key) : Key := imageKey (frTable (transposeRows fcRows)) k

theorem rowPlane_rowKeyOf (k : Key) : rowPlane (rowKeyOf k) = psi '' keyPlane k := by
  rw [rowPlane_eq_image, rowKeyOf, keyPlane_imageKey, Set.image_image]
  rfl

end CFSG.Sporadic.ThSchreier
