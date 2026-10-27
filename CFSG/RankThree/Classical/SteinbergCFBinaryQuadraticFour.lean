module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticNormalForms

public section

namespace CFSG.RankThree.Classical

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open Module QuadraticMap

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def binaryPlusForm (x : Fin 4 → ZMod 2) : ZMod 2 := x 0 * x 1 + x 2 * x 3

@[expose] def binaryMinusForm (x : Fin 4 → ZMod 2) : ZMod 2 :=
  x 0 ^ 2 + x 0 * x 1 + x 1 ^ 2 + x 2 * x 3

theorem card_zero_eq_of_basis (q : QuadraticForm (ZMod 2) V) (b : Basis (Fin 4) (ZMod 2) V)
    (f : (Fin 4 → ZMod 2) → ZMod 2) (hb : ∀ x, q (∑ i, x i • b i) = f x) :
    Nat.card {v : V // q v = 0} = Nat.card {x : Fin 4 → ZMod 2 // f x = 0} := by
  refine (Nat.card_congr (Equiv.subtypeEquiv b.equivFun.symm.toEquiv fun x => ?_)).symm
  rw [LinearEquiv.coe_toEquiv, Basis.equivFun_symm_apply, hb]

theorem card_binaryPlusForm_zero : Nat.card {x : Fin 4 → ZMod 2 // binaryPlusForm x = 0} = 10 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_binaryMinusForm_zero :
    Nat.card {x : Fin 4 → ZMod 2 // binaryMinusForm x = 0} = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem zmod_two_eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact absurd rfl h
  · rfl

theorem exists_basis_plus (q : QuadraticForm (ZMod 2) V) (b : Basis (Fin 2 ⊕ Fin 2) (ZMod 2) V)
    (hb : ∀ x y : Fin 2 → ZMod 2,
      q (∑ i, x i • b (.inl i) + ∑ i, y i • b (.inr i)) = ∑ i, x i * y i) :
    ∃ b' : Basis (Fin 4) (ZMod 2) V, ∀ x, q (∑ i, x i • b' i) = binaryPlusForm x := by
  let e : Fin 4 ≃ Fin 2 ⊕ Fin 2 :=
    { toFun := ![.inl 0, .inr 0, .inl 1, .inr 1]
      invFun := Sum.elim ![0, 2] ![1, 3]
      left_inv := by decide
      right_inv := by decide }
  refine ⟨b.reindex e.symm, fun x => ?_⟩
  have h := hb ![x 0, x 2] ![x 1, x 3]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at h
  simp only [Basis.reindex_apply, Equiv.symm_symm, Fin.sum_univ_four, binaryPlusForm]
  have e0 : e 0 = .inl 0 := rfl
  have e1 : e 1 = .inr 0 := rfl
  have e2 : e 2 = .inl 1 := rfl
  have e3 : e 3 = .inr 1 := rfl
  rw [e0, e1, e2, e3]
  rw [show x 0 • b (.inl 0) + x 1 • b (.inr 0) + x 2 • b (.inl 1) + x 3 • b (.inr 1) =
    x 0 • b (.inl 0) + x 2 • b (.inl 1) + (x 1 • b (.inr 0) + x 3 • b (.inr 1)) by abel, h]

theorem exists_basis_minus (q : QuadraticForm (ZMod 2) V)
    (b : Basis (Fin 1 ⊕ Fin 1 ⊕ Fin 2) (ZMod 2) V)
    (hb : ∀ (x y : Fin 1 → ZMod 2) (s t : ZMod 2),
      q (∑ i, x i • b (.inl i) + ∑ i, y i • b (.inr (.inl i)) + s • b (.inr (.inr 0)) +
        t • b (.inr (.inr 1))) = ∑ i, x i * y i + s ^ 2 + 1 * s * t + 1 * t ^ 2) :
    ∃ b' : Basis (Fin 4) (ZMod 2) V, ∀ x, q (∑ i, x i • b' i) = binaryMinusForm x := by
  let e : Fin 4 ≃ Fin 1 ⊕ Fin 1 ⊕ Fin 2 :=
    { toFun := ![.inr (.inr 0), .inr (.inr 1), .inl 0, .inr (.inl 0)]
      invFun := Sum.elim ![2] (Sum.elim ![3] ![0, 1])
      left_inv := by decide
      right_inv := by decide }
  refine ⟨b.reindex e.symm, fun x => ?_⟩
  have h := hb ![x 2] ![x 3] (x 0) (x 1)
  simp only [Fin.sum_univ_one, Matrix.cons_val_zero, one_mul] at h
  simp only [Basis.reindex_apply, Equiv.symm_symm, Fin.sum_univ_four, binaryMinusForm]
  have e0 : e 0 = .inr (.inr 0) := rfl
  have e1 : e 1 = .inr (.inr 1) := rfl
  have e2 : e 2 = .inl 0 := rfl
  have e3 : e 3 = .inr (.inl 0) := rfl
  rw [e0, e1, e2, e3]
  rw [show x 0 • b (.inr (.inr 0)) + x 1 • b (.inr (.inr 1)) + x 2 • b (.inl 0) +
      x 3 • b (.inr (.inl 0)) = x 2 • b (.inl 0) + x 3 • b (.inr (.inl 0)) +
      x 0 • b (.inr (.inr 0)) + x 1 • b (.inr (.inr 1)) by abel, h]
  ring

theorem polar_eq_add_add (q : QuadraticForm (ZMod 2) V) (v w : V) :
    polar q v w = q (v + w) + q v + q w := by
  rw [polar, sub_sub, sub_eq_add_neg, ZMod.neg_eq_self_mod_two, add_assoc]

theorem binary_quadratic_four_normal_forms (hV : finrank (ZMod 2) V = 4)
    (q : QuadraticForm (ZMod 2) V) (hq : ∀ v : V, (∀ w : V, q (v + w) + q v + q w = 0) → v = 0) :
    Xor
      ((∃ b : Basis (Fin 4) (ZMod 2) V, ∀ x : Fin 4 → ZMod 2,
          q (∑ i, x i • b i) = x 0 * x 1 + x 2 * x 3) ∧
        Nat.card {v : V // q v = 0} = 10)
      ((∃ b : Basis (Fin 4) (ZMod 2) V, ∀ x : Fin 4 → ZMod 2,
          q (∑ i, x i • b i) = x 0 ^ 2 + x 0 * x 1 + x 1 ^ 2 + x 2 * x 3) ∧
        Nat.card {v : V // q v = 0} = 6) := by
  have : FiniteDimensional (ZMod 2) V := Module.finite_of_finrank_pos (by omega)
  have hnd : (polarBilin q).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_of_forall fun v hv =>
      hq v fun w => by rw [← polar_eq_add_add, hv w]
  obtain ⟨-, -, hnf, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.finite_even_regular_quadratic_normal_forms q hnd
  rcases hnf 2 (by norm_num) (by omega) with ⟨b, hb⟩ | ⟨β, γ, hβ, hγ, b, hb⟩
  · obtain ⟨b', hb'⟩ := exists_basis_plus q b hb
    have hcard : Nat.card {v : V // q v = 0} = 10 := by
      rw [card_zero_eq_of_basis q b' _ hb', card_binaryPlusForm_zero]
    exact Or.inl ⟨⟨⟨b', hb'⟩, hcard⟩, fun h => by omega⟩
  · have hβ1 : β = 1 := zmod_two_eq_one_of_ne_zero hβ
    have hγ1 : γ = 1 := zmod_two_eq_one_of_ne_zero fun h => hγ 0 (by rw [h]; ring)
    subst hβ1 hγ1
    obtain ⟨b', hb'⟩ := exists_basis_minus q b hb
    have hcard : Nat.card {v : V // q v = 0} = 6 := by
      rw [card_zero_eq_of_basis q b' _ hb', card_binaryMinusForm_zero]
    exact Or.inr ⟨⟨⟨b', hb'⟩, hcard⟩, fun h => by omega⟩

end CFSG.RankThree.Classical
