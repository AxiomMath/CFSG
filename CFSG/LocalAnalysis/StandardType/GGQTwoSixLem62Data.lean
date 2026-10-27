module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSixPointGenAux

public section

namespace CFSG.StandardType.QTwo.SixPoint

open Matrix CFSG.GH74.Uniqueness.SU.SU5

abbrev qTwoSixLem62_Mat := Matrix (Fin 3) (Fin 3) F4c

@[expose] def qTwoSixLem62_g0 : qTwoSixLem62_Mat :=
  !![1, F4c.w2, F4c.w2; F4c.w, F4c.w2, F4c.w; F4c.w, F4c.w, F4c.w2]

@[expose] def qTwoSixLem62_g1 : qTwoSixLem62_Mat :=
  !![1, F4c.w2, F4c.w; 1, 1, 1; 1, F4c.w, F4c.w2]

@[expose] def qTwoSixLem62_word (i : Fin 216) : List Bool := qTwoSixGen_pattern[i.val]!

@[expose] def qTwoSixLem62_eval (A B : qTwoSixLem62_Mat) (w : List Bool) :
    qTwoSixLem62_Mat := (w.map fun b => if b then B else A).prod

@[expose] def qTwoSixLem62_element (i : Fin 216) : qTwoSixLem62_Mat :=
  qTwoSixLem62_eval qTwoSixLem62_g0 qTwoSixLem62_g1 (qTwoSixLem62_word i)

@[expose] def qTwoSixLem62_support (J : Finset (Fin 3)) (A : qTwoSixLem62_Mat) : Prop :=
  ∀ i j : Fin 3, (i ∉ J ∨ j ∉ J) → A i j = if i = j then 1 else 0

instance qTwoSixLem62_decidableSupport (J : Finset (Fin 3)) (A : qTwoSixLem62_Mat) :
    Decidable (qTwoSixLem62_support J A) :=
  @Nat.decidableForallFin 3 _ (fun i =>
    @Nat.decidableForallFin 3 _ (fun j => inferInstance))

@[expose] def qTwoSixLem62_nodes (A B : qTwoSixLem62_Mat) : Prop :=
  let a := qTwoSixLem62_eval A B (qTwoSixLem62_word 85)
  let p := qTwoSixLem62_eval A B (qTwoSixLem62_word 153)
  let b := qTwoSixLem62_eval A B (qTwoSixLem62_word 75)
  let q := qTwoSixLem62_eval A B (qTwoSixLem62_word 3)
  qTwoSixLem62_support {0, 1} a ∧ a ^ 3 = 1 ∧ a ≠ 1 ∧
  qTwoSixLem62_support {0, 1} p ∧ p ^ 2 = 1 ∧ p ≠ 1 ∧
  qTwoSixLem62_support {1, 2} b ∧ b ^ 3 = 1 ∧ b ≠ 1 ∧
  qTwoSixLem62_support {1, 2} q ∧ q ^ 2 = 1 ∧ q ≠ 1

instance qTwoSixLem62_decidableNodes (A B : qTwoSixLem62_Mat) :
    Decidable (qTwoSixLem62_nodes A B) := by
  unfold qTwoSixLem62_nodes
  infer_instance

@[expose] def qTwoSixLem62_unitVal : Fin 3 → F4c := ![1, F4c.w, F4c.w2]

@[expose] def qTwoSixLem62_frob : F4c ≃+* F4c where
  toFun := F4c.sg
  invFun := F4c.sg
  left_inv := F4c.sg_sg
  right_inv := F4c.sg_sg
  map_mul' := F4c.sg_mul
  map_add' := F4c.sg_add

@[expose] def qTwoSixLem62_field (b : Bool) : F4c ≃+* F4c :=
  if b then qTwoSixLem62_frob else RingEquiv.refl _

@[expose] def qTwoSixLem62_action (a b : Fin 3) (σ : Bool) (A : qTwoSixLem62_Mat) :
    qTwoSixLem62_Mat :=
  diagonal ![qTwoSixLem62_unitVal a, qTwoSixLem62_unitVal b, 1] *
    A.map (qTwoSixLem62_field σ) *
    diagonal ![(qTwoSixLem62_unitVal a)⁻¹, (qTwoSixLem62_unitVal b)⁻¹, 1]

set_option maxHeartbeats 8000000 in
theorem qTwoSixLem62_pair_classification : ∀ i j : Fin 216,
    let A := qTwoSixLem62_element i
    let B := qTwoSixLem62_element j
    A ^ 4 = 1 → A ^ 2 ≠ 1 →
    B ^ 12 = 1 → B ^ 6 ≠ 1 → B ^ 4 ≠ 1 →
    qTwoSixLem62_nodes A B →
    ∃ a b : Fin 3, ∃ σ : Bool,
      A = qTwoSixLem62_action a b σ qTwoSixLem62_g0 ∧
      B = qTwoSixLem62_action a b σ qTwoSixLem62_g1 := by
  decide +kernel

end CFSG.StandardType.QTwo.SixPoint

end
