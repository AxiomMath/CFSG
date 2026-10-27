module

public import CFSG.RankThree.PartTwo.Sec21.Item233TablesMatrix
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticSixCoverModel

public section

namespace CFSG.RankThree.PartTwo.Sec21.Tables

open Matrix CFSG.LocalAnalysis.ComponentInitial.SymplecticSixCover
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

theorem IsIdOutside.of_mul_eq_one {c : Set ι} {X Y : Matrix ι ι K} (hX : IsIdOutside c X)
    (hXY : X * Y = 1) (hYX : Y * X = 1) : IsIdOutside c Y := by
  intro i j hij
  rcases hij with hi | hj
  · have hrow : ∀ k, X i k = (1 : Matrix ι ι K) i k := fun k => hX i k (Or.inl hi)
    have h := congrFun₂ hXY i j
    rw [Matrix.mul_apply] at h
    simp_rw [hrow, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true] at h
    rw [h, Matrix.one_apply]
  · have hcol : ∀ k, X k j = (1 : Matrix ι ι K) k j := fun k => hX k j (Or.inr hj)
    have h := congrFun₂ hYX i j
    rw [Matrix.mul_apply] at h
    simp_rw [hcol, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true] at h
    rw [h, Matrix.one_apply]

variable {m n : ℕ} {F : Type} [Field F] {f : Fin m → Fin n}

@[expose] def coordSet (f : Fin m → Fin n) : Set (Fin n ⊕ Fin n) := Set.range (Sum.map f f)

theorem blockIncl_apply (x : Fin n ⊕ Fin n) (a : Fin m ⊕ Fin m) :
    blockIncl (K := F) f x a = if x = Sum.map f f a then 1 else 0 := by
  rcases x with x | x <;> rcases a with a | a <;> simp [blockIncl, inclMat]

theorem blockIncl_mul_transpose_apply_of_mem (hf : Function.Injective f) {x : Fin n ⊕ Fin n}
    (hx : x ∈ coordSet f) (y : Fin n ⊕ Fin n) :
    (blockIncl (K := F) f * (blockIncl (K := F) f)ᵀ) x y = (1 : Matrix _ _ F) x y := by
  rw [Matrix.mul_apply]
  simp_rw [transpose_apply, blockIncl_apply, ite_mul, one_mul, zero_mul]
  obtain ⟨a, rfl⟩ := hx
  rw [Finset.sum_eq_single a]
  · by_cases hy : Sum.map f f a = y
    · subst hy
      simp
    · simp [Ne.symm hy, Matrix.one_apply_ne hy]
  · intro b _ hba
    have : Sum.map f f a ≠ Sum.map f f b := fun e =>
      hba ((Sum.map_injective.mpr ⟨hf, hf⟩) e).symm
    simp [this]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem blockIncl_mul_transpose_apply_of_not_mem {x : Fin n ⊕ Fin n} (hx : x ∉ coordSet f)
    (y : Fin n ⊕ Fin n) : (blockIncl (K := F) f * (blockIncl (K := F) f)ᵀ) x y = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  have : x ≠ Sum.map f f b := fun e => hx ⟨b, e.symm⟩
  simp [blockIncl_apply, this]

theorem blockIncl_mul_transpose_apply_of_not_mem' {y : Fin n ⊕ Fin n} (hy : y ∉ coordSet f)
    (x : Fin n ⊕ Fin n) : (blockIncl (K := F) f * (blockIncl (K := F) f)ᵀ) x y = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  have : y ≠ Sum.map f f b := fun e => hy ⟨b, e.symm⟩
  simp [blockIncl_apply, this]

theorem projQ_mul_of_supp (hf : Function.Injective f) {N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hN : ∀ x y, (x ∉ coordSet f ∨ y ∉ coordSet f) → N x y = 0) :
    blockIncl (K := F) f * (blockIncl (K := F) f)ᵀ * N = N ∧
      N * (blockIncl (K := F) f * (blockIncl (K := F) f)ᵀ) = N := by
  constructor
  · ext x y
    by_cases hx : x ∈ coordSet f
    · rw [Matrix.mul_apply]
      simp_rw [blockIncl_mul_transpose_apply_of_mem hf hx, Matrix.one_apply, ite_mul, one_mul,
        zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    · rw [Matrix.mul_apply, hN x y (Or.inl hx)]
      exact Finset.sum_eq_zero fun b _ => by
        rw [blockIncl_mul_transpose_apply_of_not_mem hx, zero_mul]
  · ext x y
    by_cases hy : y ∈ coordSet f
    · rw [Matrix.mul_apply]
      have hQ : ∀ b, (blockIncl (K := F) f * (blockIncl (K := F) f)ᵀ) b y =
          (1 : Matrix _ _ F) b y := by
        intro b
        by_cases hb : b ∈ coordSet f
        · exact blockIncl_mul_transpose_apply_of_mem hf hb y
        · rw [blockIncl_mul_transpose_apply_of_not_mem hb, Matrix.one_apply_ne]
          rintro rfl
          exact hb hy
      simp_rw [hQ, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
    · rw [Matrix.mul_apply, hN x y (Or.inr hy)]
      exact Finset.sum_eq_zero fun b _ => by
        rw [blockIncl_mul_transpose_apply_of_not_mem' hy, mul_zero]

theorem isIdOutside_embedMat (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) :
    IsIdOutside (coordSet f) (embedMat f g) := by
  intro x y hxy
  have hP : ∀ z : Fin n ⊕ Fin n, z ∉ coordSet f → ∀ a, blockIncl (K := F) f z a = 0 := by
    intro z hz a
    have : z ≠ Sum.map f f a := fun e => hz ⟨a, e.symm⟩
    simp [blockIncl_apply, this]
  rw [embedMat, Matrix.add_apply, add_eq_left]
  rcases hxy with hx | hy
  · rw [Matrix.mul_assoc, Matrix.mul_apply]
    exact Finset.sum_eq_zero fun a _ => by rw [hP x hx a, zero_mul]
  · rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun a _ => by rw [transpose_apply, hP y hy a, mul_zero]

theorem mem_range_embedSp_iff (hf : Function.Injective f) (x : StatedSp n F) :
    x ∈ (embedSp f hf).range ↔
      IsIdOutside (coordSet f) ((x : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n)
        (Fin n ⊕ Fin n) F) := by
  constructor
  · rintro ⟨g, rfl⟩
    rw [coe_embedSp]
    exact isIdOutside_embedMat _
  · intro hx
    set P := blockIncl (K := F) f
    set X := ((x : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    set X' := (((x⁻¹ : StatedSp n F) : GL (Fin n ⊕ Fin n) F) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    set J : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F := fromBlocks 0 1 (-1) 0
    set J' : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F := fromBlocks 0 1 (-1) 0
    have hPP : Pᵀ * P = 1 := blockIncl_transpose_mul hf
    have hJP : J * P = P * J' := symplecticJ_mul_blockIncl
    have hPJ : Pᵀ * J = J' * Pᵀ := blockIncl_transpose_mul_symplecticJ
    have hXX' : X * X' = 1 := by
      have h := congrArg (fun z : StatedSp n F =>
        ((z : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)) (mul_inv_cancel x)
      simpa only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one] using h
    have hX'X : X' * X = 1 := by
      have h := congrArg (fun z : StatedSp n F =>
        ((z : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)) (inv_mul_cancel x)
      simpa only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one] using h
    have hx' : IsIdOutside (coordSet f) X' := hx.of_mul_eq_one hXX' hX'X
    have hsupp : ∀ {Y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}, IsIdOutside (coordSet f) Y →
        ∀ a b, (a ∉ coordSet f ∨ b ∉ coordSet f) → (Y - 1) a b = 0 := by
      intro Y hY a b hab
      rw [Matrix.sub_apply, hY a b hab, sub_self]
    have hQ : ∀ {Y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}, IsIdOutside (coordSet f) Y →
        P * Pᵀ * Y = Y * (P * Pᵀ) ∧ P * Pᵀ * Y * (P * Pᵀ) = Y * (P * Pᵀ) := by
      intro Y hY
      obtain ⟨h1, h2⟩ := projQ_mul_of_supp hf (hsupp hY)
      have hQQ : P * Pᵀ * (P * Pᵀ) = P * Pᵀ := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc Pᵀ, hPP, Matrix.one_mul]
      have eY : Y = 1 + (Y - 1) := by abel
      constructor
      · rw [eY, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, h1, h2]
      · rw [eY, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, Matrix.mul_one, h1, hQQ,
          Matrix.one_mul, h2]
    obtain ⟨hQX, hQXQ⟩ := hQ hx
    obtain ⟨hQX', -⟩ := hQ hx'
    have hQP : P * Pᵀ * P = P := by rw [Matrix.mul_assoc, hPP, Matrix.mul_one]
    set g := Pᵀ * X * P
    set g' := Pᵀ * X' * P
    have hgg' : g * g' = 1 := by
      calc g * g' = Pᵀ * (X * (P * Pᵀ)) * X' * P := by simp only [g, g', Matrix.mul_assoc]
        _ = Pᵀ * (P * Pᵀ) * (X * X') * P := by rw [← hQX]; simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hXX', Matrix.mul_one, ← Matrix.mul_assoc, hPP, Matrix.one_mul, hPP]
    have hg'g : g' * g = 1 := mul_eq_one_comm.mp hgg'
    have hgJ : gᵀ * J' * g = J' := by
      have hXJ : Xᵀ * J * X = J := mem_statedSp_iff.mp x.2
      calc gᵀ * J' * g = Pᵀ * Xᵀ * (P * J') * Pᵀ * X * P := by
            simp only [g, transpose_mul, transpose_transpose, Matrix.mul_assoc]
        _ = Pᵀ * Xᵀ * J * (P * Pᵀ * X) * P := by rw [← hJP]; simp only [Matrix.mul_assoc]
        _ = Pᵀ * (Xᵀ * J * X) * (P * Pᵀ * P) := by rw [hQX]; simp only [Matrix.mul_assoc]
        _ = J' := by rw [hXJ, hQP, hPJ, Matrix.mul_assoc, hPP, Matrix.mul_one]
    let gGL : GL (Fin m ⊕ Fin m) F := ⟨g, g', hgg', hg'g⟩
    have hgSp : gGL ∈ StatedSp m F := mem_statedSp_iff.mpr hgJ
    refine ⟨⟨gGL, hgSp⟩, statedSp_ext ?_⟩
    rw [coe_embedSp]
    change embedMat f g = X
    rw [embedMat]
    have e1 : P * (g - 1) * Pᵀ = P * Pᵀ * X * (P * Pᵀ) - P * Pᵀ := by
      simp only [g, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
    rw [e1, hQXQ]
    obtain ⟨-, h2⟩ := projQ_mul_of_supp hf (hsupp hx)
    have e2 : X * (P * Pᵀ) = P * Pᵀ + (X - 1) := by
      have := h2
      rw [Matrix.sub_mul, Matrix.one_mul] at this
      rw [← this]
      abel
    rw [e2]
    abel

end CFSG.RankThree.PartTwo.Sec21.Tables
