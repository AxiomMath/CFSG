module

public import CFSG.RankThree.PartOne.LIT.FiveRecords
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.RankThree.PartOne.LIT

open Matrix

@[expose] def aM : M3 := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

@[expose] def bM : M3 := !![1, 1, 2; 4, 3, 4; 3, 4, 4]

theorem aM_orth : aMᵀ * aM = 1 := by decide

theorem bM_orth : bMᵀ * bM = 1 := by decide

@[expose] def orthGL (A : M3) (h : Aᵀ * A = 1) : GL (Fin 3) (ZMod 5) :=
  ⟨A, Aᵀ, mul_eq_one_comm.mp h, h⟩

@[simp] theorem val_orthGL (A : M3) (h : Aᵀ * A = 1) : (orthGL A h : M3) = A := rfl

@[simp] theorem val_inv_orthGL (A : M3) (h : Aᵀ * A = 1) :
    ((orthGL A h)⁻¹ : GL (Fin 3) (ZMod 5)).val = Aᵀ := rfl

@[expose] def aGL : GL (Fin 3) (ZMod 5) := orthGL aM aM_orth

@[expose] def bGL : GL (Fin 3) (ZMod 5) := orthGL bM bM_orth

@[expose] def Kfive : Subgroup (GL (Fin 3) (ZMod 5)) := Subgroup.closure {aGL, bGL}

@[expose] def aR : R3 := ⟨0, 0, 1, 1, 0, 0, 0, 1, 0⟩

@[expose] def bR : R3 := ⟨1, 1, 2, 4, 3, 4, 3, 4, 4⟩

theorem ofM_aM : R3.ofM aM = aR := by decide +kernel

theorem ofM_bM : R3.ofM bM = bR := by decide +kernel

@[expose] def genR (b : Bool) : R3 := if b then bR else aR

@[expose] def foldR (w : List Bool) (r : R3) : R3 := w.foldl (fun acc b => R3.mul acc (genR b)) r

@[expose] def evalR (w : List Bool) : R3 := foldR w R3.one

@[expose] def Lwords : List (List Bool) :=
  [[],
   [false],
   [true],
   [false, false],
   [false, true],
   [true, false],
   [true, true],
   [false, false, true],
   [false, true, false],
   [false, true, true],
   [true, false, false],
   [true, false, true],
   [true, true, false],
   [true, true, true],
   [false, false, true, false],
   [false, false, true, true],
   [false, true, false, false],
   [false, true, false, true],
   [false, true, true, true],
   [true, false, false, true],
   [true, false, true, false],
   [true, false, true, true],
   [true, true, false, false],
   [true, true, false, true],
   [true, true, true, false],
   [true, true, true, true],
   [false, false, true, false, false],
   [false, false, true, false, true],
   [false, true, false, false, true],
   [false, true, false, true, false],
   [false, true, false, true, true],
   [false, true, true, true, false],
   [false, true, true, true, true],
   [true, false, false, true, true],
   [true, false, true, false, false],
   [true, false, true, false, true],
   [true, false, true, true, true],
   [true, true, false, false, true],
   [true, true, true, false, true],
   [true, true, true, true, false],
   [false, false, true, false, true, false],
   [false, false, true, false, true, true],
   [false, true, false, false, true, true],
   [false, true, false, true, false, false],
   [false, true, false, true, true, true],
   [false, true, true, true, false, true],
   [true, false, true, false, false, true],
   [true, false, true, false, true, true],
   [true, false, true, true, true, false],
   [true, false, true, true, true, true],
   [true, true, true, true, false, true],
   [false, false, true, false, true, true, true],
   [false, true, false, true, false, false, true],
   [false, true, false, true, true, true, false],
   [false, true, false, true, true, true, true],
   [true, false, true, false, false, true, true],
   [true, false, true, false, true, true, true],
   [false, false, true, false, true, true, true, false],
   [false, false, true, false, true, true, true, true],
   [false, true, false, true, false, false, true, true]]

@[expose] def Lr : List R3 := Lwords.map evalR

theorem Lr_nodup : Lr.Nodup := by decide +kernel

theorem Lr_length : Lr.length = 60 := by decide +kernel

theorem one_mem_Lr : R3.one ∈ Lr := by decide +kernel

theorem Lr_mul_a : ∀ r ∈ Lr, R3.mul r aR ∈ Lr := by decide +kernel

theorem Lr_mul_b : ∀ r ∈ Lr, R3.mul r bR ∈ Lr := by decide +kernel

theorem Lr_mul_aT : ∀ r ∈ Lr, R3.mul r aR.transpose ∈ Lr := by decide +kernel

theorem Lr_mul_bT : ∀ r ∈ Lr, R3.mul r bR.transpose ∈ Lr := by decide +kernel

theorem ofM_aMT : R3.ofM aMᵀ = aR.transpose := by rw [R3.ofM_transpose, ofM_aM]

theorem ofM_bMT : R3.ofM bMᵀ = bR.transpose := by rw [R3.ofM_transpose, ofM_bM]

theorem ofM_mem_Lr {x : GL (Fin 3) (ZMod 5)} (hx : x ∈ Kfive) : R3.ofM (x : M3) ∈ Lr := by
  induction hx using Subgroup.closure_induction_right with
  | one =>
    rw [Units.val_one, R3.ofM_one]
    exact one_mem_Lr
  | mul_right g hg y hy ih =>
    rcases hy with rfl | rfl
    · rw [Units.val_mul, R3.ofM_mul]
      have h := Lr_mul_a _ ih
      rwa [← ofM_aM] at h
    · rw [Units.val_mul, R3.ofM_mul]
      have h := Lr_mul_b _ ih
      rwa [← ofM_bM] at h
  | mul_inv_cancel g hg y hy ih =>
    rcases hy with rfl | rfl
    · rw [Units.val_mul, R3.ofM_mul]
      have h := Lr_mul_aT _ ih
      rwa [← ofM_aMT] at h
    · rw [Units.val_mul, R3.ofM_mul]
      have h := Lr_mul_bT _ ih
      rwa [← ofM_bMT] at h

@[expose] def genGL (b : Bool) : GL (Fin 3) (ZMod 5) := if b then bGL else aGL

@[expose] def foldGL (w : List Bool) (acc : GL (Fin 3) (ZMod 5)) : GL (Fin 3) (ZMod 5) :=
  w.foldl (fun acc b => acc * genGL b) acc

@[expose] def evalGL (w : List Bool) : GL (Fin 3) (ZMod 5) := foldGL w 1

theorem genGL_mem (b : Bool) : genGL b ∈ Kfive := by
  cases b
  · exact Subgroup.subset_closure (Or.inl rfl)
  · exact Subgroup.subset_closure (Or.inr rfl)

theorem foldGL_mem (w : List Bool) : ∀ acc : GL (Fin 3) (ZMod 5), acc ∈ Kfive →
    foldGL w acc ∈ Kfive := by
  induction w with
  | nil => exact fun acc h => h
  | cons b w ih => exact fun acc h => ih (acc * genGL b) (Kfive.mul_mem h (genGL_mem b))

theorem ofM_genGL (b : Bool) : R3.ofM (genGL b : M3) = genR b := by
  cases b
  · exact ofM_aM
  · exact ofM_bM

theorem foldGL_ofM (w : List Bool) : ∀ (acc : GL (Fin 3) (ZMod 5)) (r : R3),
    R3.ofM (acc : M3) = r → R3.ofM (foldGL w acc : M3) = foldR w r := by
  induction w with
  | nil => exact fun acc r h => h
  | cons b w ih =>
    intro acc r h
    refine ih (acc * genGL b) (R3.mul r (genR b)) ?_
    rw [Units.val_mul, R3.ofM_mul, h, ofM_genGL]

theorem ofM_evalGL (w : List Bool) : R3.ofM (evalGL w : M3) = evalR w :=
  foldGL_ofM w 1 R3.one (by rw [Units.val_one, R3.ofM_one])

theorem evalGL_mem (w : List Bool) : evalGL w ∈ Kfive := foldGL_mem w 1 (one_mem _)

theorem natCard_Kfive : Nat.card Kfive = 60 := by
  let f : Kfive → R3 := fun x => R3.ofM (x.1 : M3)
  have hinj : Function.Injective f := fun x y h => Subtype.ext (Units.ext (R3.ofM_inj h))
  have hrange : Set.range f = {r | r ∈ Lr} := by
    ext r
    constructor
    · rintro ⟨x, rfl⟩
      exact ofM_mem_Lr x.2
    · intro hr
      obtain ⟨w, -, rfl⟩ := List.mem_map.mp hr
      exact ⟨⟨evalGL w, evalGL_mem w⟩, ofM_evalGL w⟩
  have hfin : {r | r ∈ Lr} = ((Lr.toFinset : Finset R3) : Set R3) := by
    ext r
    simp
  calc Nat.card Kfive = Nat.card (Set.range f) := Nat.card_congr (Equiv.ofInjective f hinj)
    _ = Nat.card ((Lr.toFinset : Finset R3) : Set R3) := by rw [hrange, hfin]
    _ = Lr.toFinset.card := Nat.card_coe_set_eq _ ▸ Set.ncard_coe_finset _
    _ = 60 := by rw [List.toFinset_card_of_nodup Lr_nodup, Lr_length]

end CFSG.RankThree.PartOne.LIT
