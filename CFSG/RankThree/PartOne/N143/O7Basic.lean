module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.RankThree.PartOne.N143.O7

open Matrix CFSG.Assembly.LowTwoRank
open scoped commutatorElement

abbrev Idx : Type := Fin 3 ⊕ Fin 3 ⊕ Unit

@[expose] def qf (v : Idx → ZMod 3) : ZMod 3 :=
  v (.inl 0) * v (.inr (.inl 0)) + v (.inl 1) * v (.inr (.inl 1)) +
    v (.inl 2) * v (.inr (.inl 2)) + v (.inr (.inr ())) ^ 2

theorem qf_eq_stated : qf = StatedQuadOdd 3 (ZMod 3) := by
  funext v
  simp [qf, StatedQuadOdd, Fin.sum_univ_three]

@[expose] def gv (v : Idx → ZMod 3) : Idx → ZMod 3
  | .inl k => v (.inr (.inl k))
  | .inr (.inl k) => v (.inl k)
  | .inr (.inr _) => 2 * v (.inr (.inr ()))

@[expose] def gramM : Matrix Idx Idx (ZMod 3) :=
  Matrix.of fun a b => match a, b with
    | .inl i, .inr (.inl j) => if i = j then 1 else 0
    | .inr (.inl i), .inl j => if i = j then 1 else 0
    | .inr (.inr _), .inr (.inr _) => 2
    | _, _ => 0

@[expose] def reflM (v : Idx → ZMod 3) : Matrix Idx Idx (ZMod 3) :=
  Matrix.of fun a b => (if a = b then 1 else 0) - qf v * v a * gv v b

theorem qf_eq_gram (x : Idx → ZMod 3) : qf x = 2 * (x ⬝ᵥ (gramM *ᵥ x)) := by
  simp only [qf, dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Fin.sum_univ_three,
    Finset.univ_unique, Finset.sum_singleton, gramM, Matrix.of_apply]
  simp
  generalize x (Sum.inl 0) = a0
  generalize x (Sum.inl 1) = a1
  generalize x (Sum.inl 2) = a2
  generalize x (Sum.inr (Sum.inl 0)) = b0
  generalize x (Sum.inr (Sum.inl 1)) = b1
  generalize x (Sum.inr (Sum.inl 2)) = b2
  generalize x (Sum.inr (Sum.inr PUnit.unit)) = c
  revert a0 a1 a2 b0 b1 b2 c
  decide +kernel

theorem dot_mulVec_left (A : Matrix Idx Idx (ZMod 3)) (x u : Idx → ZMod 3) :
    (A *ᵥ x) ⬝ᵥ u = x ⬝ᵥ (Aᵀ *ᵥ u) := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem isom_of_gram {A : Matrix Idx Idx (ZMod 3)} (h : Aᵀ * gramM * A = gramM)
    (x : Idx → ZMod 3) : qf (A *ᵥ x) = qf x := by
  have e1 : (A *ᵥ x) ⬝ᵥ (gramM *ᵥ (A *ᵥ x)) = x ⬝ᵥ (gramM *ᵥ x) := by
    rw [dot_mulVec_left, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]
  calc qf (A *ᵥ x) = 2 * ((A *ᵥ x) ⬝ᵥ (gramM *ᵥ (A *ᵥ x))) := qf_eq_gram _
    _ = 2 * (x ⬝ᵥ (gramM *ᵥ x)) := by rw [e1]
    _ = qf x := (qf_eq_gram x).symm

@[expose] def Iso : Subgroup (GL Idx (ZMod 3)) :=
  Subgroup.closure {A : GL Idx (ZMod 3) | ∀ v, qf ((A : Matrix Idx Idx (ZMod 3)) *ᵥ v) = qf v}

@[expose] def Om : Subgroup (GL Idx (ZMod 3)) := ⁅Iso, Iso⁆

theorem om_eq_stated : Om = StatedOmega (StatedQuadOdd 3 (ZMod 3)) := by
  rw [← qf_eq_stated]
  rfl

structure RefVec where
  v : Idx → ZMod 3
  mul_self : reflM v * reflM v = 1
  gram : (reflM v)ᵀ * gramM * reflM v = gramM

@[expose] def reflGL (r : RefVec) : GL Idx (ZMod 3) :=
  ⟨reflM r.v, reflM r.v, r.mul_self, r.mul_self⟩

theorem reflGL_val (r : RefVec) : ((reflGL r : GL Idx (ZMod 3)) : Matrix Idx Idx (ZMod 3)) = reflM r.v := rfl

theorem reflGL_mul_self (r : RefVec) : reflGL r * reflGL r = 1 := Units.ext r.mul_self

theorem reflGL_inv (r : RefVec) : (reflGL r)⁻¹ = reflGL r :=
  inv_eq_of_mul_eq_one_right (reflGL_mul_self r)

theorem reflGL_mem_iso (r : RefVec) : reflGL r ∈ Iso :=
  Subgroup.subset_closure (isom_of_gram r.gram)

theorem pair_mem_omega (a b y : RefVec)
    (h : reflM a.v * reflM y.v * reflM a.v * reflM y.v = reflM a.v * reflM b.v) :
    reflGL a * reflGL b ∈ Om := by
  have h' : reflGL a * reflGL y * reflGL a * reflGL y = reflGL a * reflGL b :=
    Units.ext (by simpa only [Units.val_mul, reflGL_val] using h)
  have hc : ⁅reflGL a, reflGL y⁆ = reflGL a * reflGL b := by
    rw [commutatorElement_def, reflGL_inv a, reflGL_inv y]
    exact h'
  rw [← hc]
  exact Subgroup.commutator_mem_commutator (reflGL_mem_iso a) (reflGL_mem_iso y)

theorem om_le_iso : Om ≤ Iso := by
  refine Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => ?_
  rw [commutatorElement_def]
  exact Iso.mul_mem (Iso.mul_mem (Iso.mul_mem h₁ h₂) (Iso.inv_mem h₁)) (Iso.inv_mem h₂)

theorem mem_om_of_inverted {g h : GL Idx (ZMod 3)} (hg : g ∈ Iso) (hh : h ∈ Iso)
    (hi : h * g = g * g * h) : g ∈ Om := by
  have hc : ⁅h, g⁆ = g := by
    rw [commutatorElement_def]
    have h1 : h * g * h⁻¹ = g * g := by rw [mul_inv_eq_iff_eq_mul]; exact hi
    rw [h1]
    exact mul_inv_cancel_right g g
  rw [← hc]
  exact Subgroup.commutator_mem_commutator hh hg

theorem mem_iso_of_gram {A : GL Idx (ZMod 3)} (h : (A : Matrix Idx Idx (ZMod 3))ᵀ * gramM * A = gramM) :
    A ∈ Iso :=
  Subgroup.subset_closure (isom_of_gram h)

end CFSG.RankThree.PartOne.N143.O7
