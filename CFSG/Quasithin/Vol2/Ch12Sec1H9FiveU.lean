module

public import Certificates.Certificate7109
public import CFSG.Quasithin.Vol2.Ch12Sec1H9Lin

public section

namespace CFSG.Quasithin.H13.H9FiveU

open scoped Matrix

@[expose] def fixVecS (S : Subgroup (GL (Fin 5) (ZMod 2))) : Set (Fin 5 → ZMod 2) :=
  {v | ∀ g ∈ S, (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ v = v}

@[expose] def fixVecTS (S : Subgroup (GL (Fin 5) (ZMod 2))) : Set (Fin 5 → ZMod 2) :=
  {v | ∀ g ∈ S, (g : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ *ᵥ v = v}

@[expose] def commVecS (S : Subgroup (GL (Fin 5) (ZMod 2))) :
    Subgroup (Multiplicative (Fin 5 → ZMod 2)) :=
  Subgroup.closure {w | ∃ g ∈ S, ∃ v : Fin 5 → ZMod 2,
    w = Multiplicative.ofAdd ((g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ v - v)}

theorem dot_mulVec_left (A : Matrix (Fin 5) (Fin 5) (ZMod 2)) (x w : Fin 5 → ZMod 2) :
    (A *ᵥ x) ⬝ᵥ w = x ⬝ᵥ (Aᵀ *ᵥ w) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm, Matrix.mulVec_transpose]

theorem eq_zero_of_dot (d : Fin 5 → ZMod 2) (h : ∀ z : Fin 5 → ZMod 2, z ⬝ᵥ d = 0) : d = 0 := by
  funext i
  have := h (Pi.single i 1)
  simpa using this

theorem card_comm_mul_card_fixT (S : Subgroup (GL (Fin 5) (ZMod 2))) :
    Nat.card (commVecS S) * Nat.card (fixVecTS S) = 2 ^ 5 := by
  let C : AddSubgroup (Fin 5 → ZMod 2) :=
    { carrier := {x | Multiplicative.ofAdd x ∈ commVecS S}
      add_mem' := fun {a b} ha hb => by
        show Multiplicative.ofAdd (a + b) ∈ commVecS S
        rw [ofAdd_add]
        exact (commVecS S).mul_mem ha hb
      zero_mem' := by
        show Multiplicative.ofAdd 0 ∈ commVecS S
        rw [ofAdd_zero]
        exact (commVecS S).one_mem
      neg_mem' := fun {a} ha => by
        show Multiplicative.ofAdd (-a) ∈ commVecS S
        rw [ofAdd_neg]
        exact (commVecS S).inv_mem ha }
  have hcardC : Nat.card C = Nat.card (commVecS S) := Nat.card_congr
    { toFun := fun x => ⟨Multiplicative.ofAdd x.1, x.2⟩
      invFun := fun w => ⟨Multiplicative.toAdd w.1, w.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hiff : ∀ y, y ∈ fixVecTS S ↔ ∀ x ∈ C, x ⬝ᵥ y = 0 := by
    intro y
    constructor
    · intro hy x hx
      have key : ∀ w ∈ commVecS S, Multiplicative.toAdd w ⬝ᵥ y = 0 := by
        intro w hw
        induction hw using Subgroup.closure_induction with
        | mem w hw =>
          obtain ⟨g, hg, v, rfl⟩ := hw
          rw [toAdd_ofAdd, sub_dotProduct, dot_mulVec_left, hy g hg, sub_self]
        | one => simp
        | mul a b _ _ ha hb => rw [toAdd_mul, add_dotProduct, ha, hb, add_zero]
        | inv a _ ha =>
          rw [toAdd_inv, neg_dotProduct, ha]
          exact neg_zero
      exact key _ hx
    · intro hy g hg
      have h1 : ∀ v : Fin 5 → ZMod 2,
          v ⬝ᵥ ((g : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ *ᵥ y - y) = 0 := by
        intro v
        have h2 := hy ((g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ v - v)
          (show Multiplicative.ofAdd ((g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ v - v) ∈
            commVecS S from Subgroup.subset_closure ⟨g, hg, v, rfl⟩)
        rw [sub_dotProduct, dot_mulVec_left] at h2
        rw [dotProduct_sub]
        exact h2
      exact sub_eq_zero.mp (eq_zero_of_dot _ h1)
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff), ← hcardC]
  exact H9Coord.card_mul_card_orth C

theorem gl5_large {S : Subgroup (GL (Fin 5) (ZMod 2))}
    (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (hsq : ∀ x ∈ S, x * x = 1)
    (h32 : 2 ^ 5 ≤ Nat.card S) :
    (Nat.card (commVecS S) = 4 ∧ Nat.card (fixVecS S) = 4) ∨
      (Nat.card (commVecS S) = 8 ∧ Nat.card (fixVecS S) = 8) := by
  have hD := card_comm_mul_card_fixT S
  rcases Certificates.certificate7109.1 S hcomm hsq h32 with ⟨h4, h8⟩ | ⟨h8, h4⟩
  · have h8' : Nat.card (fixVecTS S) = 8 := h8
    rw [h8'] at hD
    exact Or.inl ⟨by omega, h4⟩
  · have h4' : Nat.card (fixVecTS S) = 4 := h4
    rw [h4'] at hD
    exact Or.inr ⟨by omega, h8⟩

theorem gl5_noForm {S : Subgroup (GL (Fin 5) (ZMod 2))}
    (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (hsq : ∀ x ∈ S, x * x = 1)
    (h16 : 2 ^ 4 ≤ Nat.card S) {P : Matrix (Fin 5) (Fin 5) (ZMod 2)} (hP : Pᵀ = P)
    (hdet : P.det ≠ 0) :
    ∃ g ∈ S, (↑g : Matrix (Fin 5) (Fin 5) (ZMod 2)) * P *
      (↑g : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ ≠ P :=
  Certificates.certificate7109.2 S hcomm hsq h16 P hP hdet

end CFSG.Quasithin.H13.H9FiveU
