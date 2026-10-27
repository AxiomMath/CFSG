module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80L3Levi

public section

namespace CFSG.Quasithin.E2P.Asc80

open Matrix CFSG.Quasithin.A38c15
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime]

@[expose] def diagT (p : ℕ) [Fact p.Prime] : Subgroup SL(3, ZMod p) where
  carrier := {g | (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 0 1 = 0 ∧
    (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 0 2 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 1 0 = 0 ∧
    (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 1 2 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 2 0 = 0 ∧
    (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 2 1 = 0}
  one_mem' := by simp
  mul_mem' := by
    rintro a b ⟨a1, a2, a3, a4, a5, a6⟩ ⟨b1, b2, b3, b4, b5, b6⟩
    simp [Matrix.mul_apply, Fin.sum_univ_three, a1, a2, a3, a4, a5, a6, b1, b2, b3, b4, b5, b6]
  inv_mem' := by
    rintro a ⟨a1, a2, a3, a4, a5, a6⟩
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three, a1, a2, a3, a4, a5, a6]

theorem mem_diagT_iff {g : SL(3, ZMod p)} : g ∈ diagT p ↔
    (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 0 1 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 0 2 = 0 ∧
    (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 1 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 1 2 = 0 ∧
    (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 2 0 = 0 ∧
    (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 2 1 = 0 := Iff.rfl

@[expose] def monoT (p : ℕ) [Fact p.Prime] : Subgroup SL(3, ZMod p) where
  carrier := {g | (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 0 2 = 0 ∧
    (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 1 2 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 2 0 = 0 ∧
    (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 2 1 = 0 ∧
    (((g : Matrix (Fin 3) (Fin 3) (ZMod p)) 0 1 = 0 ∧
        (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 1 0 = 0) ∨
      ((g : Matrix (Fin 3) (Fin 3) (ZMod p)) 0 0 = 0 ∧
        (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 1 1 = 0))}
  one_mem' := by simp
  mul_mem' := by
    rintro a b ⟨a1, a2, a3, a4, ⟨a5, a6⟩ | ⟨a5, a6⟩⟩ ⟨b1, b2, b3, b4, ⟨b5, b6⟩ | ⟨b5, b6⟩⟩
    · refine ⟨?_, ?_, ?_, ?_, Or.inl ⟨?_, ?_⟩⟩ <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three, a1, a2, a3, a4, a5, a6, b1, b2, b3, b4, b5, b6]
    · refine ⟨?_, ?_, ?_, ?_, Or.inr ⟨?_, ?_⟩⟩ <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three, a1, a2, a3, a4, a5, a6, b1, b2, b3, b4, b5, b6]
    · refine ⟨?_, ?_, ?_, ?_, Or.inr ⟨?_, ?_⟩⟩ <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three, a1, a2, a3, a4, a5, a6, b1, b2, b3, b4, b5, b6]
    · refine ⟨?_, ?_, ?_, ?_, Or.inl ⟨?_, ?_⟩⟩ <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three, a1, a2, a3, a4, a5, a6, b1, b2, b3, b4, b5, b6]
  inv_mem' := by
    rintro a ⟨a1, a2, a3, a4, ⟨a5, a6⟩ | ⟨a5, a6⟩⟩
    · refine ⟨?_, ?_, ?_, ?_, Or.inl ⟨?_, ?_⟩⟩ <;>
        simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three, a1, a2, a3, a4, a5, a6]
    · refine ⟨?_, ?_, ?_, ?_, Or.inr ⟨?_, ?_⟩⟩ <;>
        simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three, a1, a2, a3, a4, a5, a6]

theorem mem_monoT_iff {g : SL(3, ZMod p)} : g ∈ monoT p ↔
    (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 0 2 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 1 2 = 0 ∧
    (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 2 1 = 0 ∧
    (((g : Matrix (Fin 3) (Fin 3) (ZMod p)) 0 1 = 0 ∧
        (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 1 0 = 0) ∨
      ((g : Matrix (Fin 3) (Fin 3) (ZMod p)) 0 0 = 0 ∧
        (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 1 1 = 0)) := Iff.rfl

theorem diagT_le_monoT : diagT p ≤ monoT p := fun _ ⟨h1, h2, h3, h4, h5, h6⟩ =>
  ⟨h2, h4, h5, h6, Or.inl ⟨h1, h3⟩⟩

theorem monoT_le_leviBlock : monoT p ≤ leviBlock p := fun _ ⟨h1, h2, h3, h4, _⟩ =>
  mem_leviBlock_iff.mpr ⟨h1, h2, h3, h4⟩

@[expose] def diagMat (x y z : (ZMod p)ˣ) (h : x * y * z = 1) : SL(3, ZMod p) :=
  ⟨Matrix.diagonal ![(x : ZMod p), (y : ZMod p), (z : ZMod p)], by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    show (x : ZMod p) * y * z = 1
    simpa using congrArg Units.val h⟩

theorem coe_diagMat (x y z : (ZMod p)ˣ) (h : x * y * z = 1) :
    ((diagMat x y z h : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) =
      Matrix.diagonal ![(x : ZMod p), (y : ZMod p), (z : ZMod p)] := rfl

theorem diagMat_mem (x y z : (ZMod p)ˣ) (h : x * y * z = 1) : diagMat x y z h ∈ diagT p := by
  rw [mem_diagT_iff, coe_diagMat]
  simp

theorem diag_det {g : SL(3, ZMod p)} (hg : g ∈ diagT p) :
    (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 0 0 * (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 1 1 *
      (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 2 2 = 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hg
  have := g.2
  rw [Matrix.det_fin_three] at this
  simpa [h1, h2, h3, h4, h5, h6] using this

noncomputable def diagEquiv (p : ℕ) [Fact p.Prime] : ↥(diagT p) ≃ (ZMod p)ˣ × (ZMod p)ˣ where
  toFun g := (Units.mk0 ((g.1 : Matrix (Fin 3) (Fin 3) (ZMod p)) 0 0) (by
      intro h
      have := diag_det g.2
      rw [h] at this
      simp at this), Units.mk0 ((g.1 : Matrix (Fin 3) (Fin 3) (ZMod p)) 1 1) (by
      intro h
      have := diag_det g.2
      rw [h] at this
      simp at this))
  invFun xy := ⟨diagMat xy.1 xy.2 (xy.1 * xy.2)⁻¹ (mul_inv_cancel _), diagMat_mem _ _ _ _⟩
  left_inv g := by
    obtain ⟨g, hg⟩ := g
    have hd := diag_det hg
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hg
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_diagMat, h1, h2, h3, h4, h5, h6]
    rw [← _root_.mul_inv_rev]
    exact (eq_inv_of_mul_eq_one_right hd).symm
  right_inv xy := by
    obtain ⟨x, y⟩ := xy
    refine Prod.ext (Units.ext ?_) (Units.ext ?_)
    · simp only [Units.val_mk0, coe_diagMat, Matrix.diagonal_apply_eq]
      rfl
    · simp only [Units.val_mk0, coe_diagMat, Matrix.diagonal_apply_eq]
      rfl

theorem card_diagT : Nat.card (diagT p) = (p - 1) ^ 2 := by
  rw [Nat.card_congr (diagEquiv p), Nat.card_prod, Nat.card_units, Nat.card_zmod, sq]

theorem center_le_diagT : Subgroup.center SL(3, ZMod p) ≤ diagT p := by
  intro g hg
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  rw [mem_diagT_iff, ← hr]
  simp [Matrix.scalar_apply]

@[expose] def swapT (p : ℕ) [Fact p.Prime] : SL(3, ZMod p) :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, -1], by norm_num [Matrix.det_fin_three]⟩

theorem swapT_mem : swapT p ∈ monoT p := by
  rw [mem_monoT_iff]
  simp [swapT]

theorem relIndex_diagT_monoT : (diagT p).relIndex (monoT p) = 2 := by
  have : ((diagT p).subgroupOf (monoT p)).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨swapT p, swapT_mem⟩, fun b => ?_⟩
    obtain ⟨b, hb⟩ := b
    obtain ⟨h02, h12, h20, h21, ⟨h01, h10⟩ | ⟨h00, h11⟩⟩ := hb
    ·
      have hbD : b ∈ diagT p := ⟨h01, h02, h10, h12, h20, h21⟩
      have hd := diag_det hbD
      have h00 : (b : Matrix (Fin 3) (Fin 3) (ZMod p)) 0 0 ≠ 0 := fun h => by
        rw [h] at hd
        simp at hd
      refine Or.inr ⟨?_, ?_⟩
      · exact hbD
      · intro h
        have h' : (b * swapT p : SL(3, ZMod p)) ∈ diagT p := h
        have := h'.1
        rw [Matrix.SpecialLinearGroup.coe_mul] at this
        simp [swapT, Matrix.mul_apply, Fin.sum_univ_three, h01, h02] at this
        exact h00 this
    ·
      have hbD : b ∉ diagT p := fun h => by
        have hd := diag_det h
        rw [h00] at hd
        simp at hd
      refine Or.inl ⟨?_, hbD⟩
      show b * swapT p ∈ diagT p
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        (rw [Matrix.SpecialLinearGroup.coe_mul]
         simp [swapT, Matrix.mul_apply, Fin.sum_univ_three, h00, h11, h02, h12, h20, h21])
  exact this

theorem index_diagT : (diagT p).index * (p - 1) ^ 2 = p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)) := by
  have h := (diagT p).index_mul_card
  rw [card_diagT] at h
  have hSL := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := ZMod p) (n := 3)
    (by norm_num)
  rw [show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num), Nat.card_zmod] at hSL
  norm_num at hSL
  rw [Nat.card_eq_fintype_card, hSL] at h
  exact h

theorem odd_index_monoT (hp : p % 4 = 1) : Odd (monoT p).index := by
  have h1 := Subgroup.relIndex_mul_index (diagT_le_monoT (p := p))
  rw [relIndex_diagT_monoT] at h1
  have hi := index_diagT (p := p)
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  obtain ⟨k, hk⟩ : ∃ k, p = 4 * k + 1 := ⟨p / 4, by omega⟩
  have hk1 : 1 ≤ k := by
    have := (Fact.out : p.Prime).two_le
    omega
  have hpos : 0 < (p - 1) ^ 2 := by
    have : 0 < p - 1 := by omega
    positivity
  have key : (diagT p).index = p ^ 3 * ((p + 1) * (p ^ 2 + p + 1)) := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [hi]
    zify [hp1, Nat.one_le_pow 2 p (by omega), Nat.one_le_pow 3 p (by omega)]
    ring
  have h2 : 2 * (monoT p).index = p ^ 3 * ((p + 1) * (p ^ 2 + p + 1)) := by
    rw [← key, ← h1]
  have h3 : (monoT p).index = p ^ 3 * ((2 * k + 1) * (p ^ 2 + p + 1)) := by
    have : p + 1 = 2 * (2 * k + 1) := by omega
    rw [this] at h2
    linarith
  rw [h3]
  refine (Odd.pow (by rw [hk]; exact ⟨2 * k, by ring⟩)).mul (Odd.mul ⟨k, rfl⟩ ?_)
  rw [hk]
  exact ⟨8 * k ^ 2 + 6 * k + 1, by ring⟩

end CFSG.Quasithin.E2P.Asc80
