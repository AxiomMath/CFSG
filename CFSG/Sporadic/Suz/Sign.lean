module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Sporadic.Suz

open Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {n : ℕ}

@[expose] def qf (F : Matrix (Fin n) (Fin n) (ZMod 3)) (x : Fin n → ZMod 3) : ZMod 3 :=
  2 * (x ⬝ᵥ F *ᵥ x)

theorem dot_conj (M F : Matrix (Fin n) (Fin n) (ZMod 3)) (x : Fin n → ZMod 3) :
    (M *ᵥ x) ⬝ᵥ F *ᵥ (M *ᵥ x) = x ⬝ᵥ (Mᵀ * F * M) *ᵥ x := by
  calc (M *ᵥ x) ⬝ᵥ F *ᵥ (M *ᵥ x) = (M *ᵥ x) ⬝ᵥ (F * M) *ᵥ x := by rw [mulVec_mulVec]
    _ = ((M *ᵥ x) ᵥ* (F * M)) ⬝ᵥ x := dotProduct_mulVec _ _ _
    _ = ((x ᵥ* Mᵀ) ᵥ* (F * M)) ⬝ᵥ x := by rw [vecMul_transpose]
    _ = (x ᵥ* (Mᵀ * F * M)) ⬝ᵥ x := by rw [vecMul_vecMul, mul_assoc]
    _ = x ⬝ᵥ (Mᵀ * F * M) *ᵥ x := (dotProduct_mulVec _ _ _).symm

theorem qf_mulVec {F g : Matrix (Fin n) (Fin n) (ZMod 3)} (hg : gᵀ * F * g = F)
    (x : Fin n → ZMod 3) : qf F (g *ᵥ x) = qf F x := by
  unfold qf
  rw [dot_conj, hg]

abbrev Lev (F : Matrix (Fin n) (Fin n) (ZMod 3)) : Type := {x : Fin n → ZMod 3 // qf F x = 1}

theorem qf_neg (F : Matrix (Fin n) (Fin n) (ZMod 3)) (x : Fin n → ZMod 3) :
    qf F (-x) = qf F x := by
  unfold qf
  rw [mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]

theorem qf_zero (F : Matrix (Fin n) (Fin n) (ZMod 3)) : qf F 0 = 0 := by
  unfold qf
  simp

section Action

variable (F : Matrix (Fin n) (Fin n) (ZMod 3)) (J : Subgroup (GL (Fin n) (ZMod 3)))
  (hJ : ∀ g ∈ J, ((g : Matrix (Fin n) (Fin n) (ZMod 3)))ᵀ * F * g = F)

@[reducible, expose] noncomputable def levAction : MulAction J (Lev F) where
  smul g x := ⟨((g : GL (Fin n) (ZMod 3)) : Matrix (Fin n) (Fin n) (ZMod 3)) *ᵥ x.1, by
    rw [qf_mulVec (hJ g g.2)]; exact x.2⟩
  one_smul x := Subtype.ext (one_mulVec x.1)
  mul_smul g h x := Subtype.ext (mulVec_mulVec x.1 _ _).symm

@[expose] noncomputable def levSign : J →* ℤˣ :=
  letI := levAction F J hJ
  Equiv.Perm.sign.comp (MulAction.toPermHom J (Lev F))

theorem units_eq_one_of_pow_odd {u : ℤˣ} {k : ℕ} (hk : Odd k) (h : u ^ k = 1) : u = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · rfl
  · rw [hk.neg_one_pow] at h
    exact absurd h (by decide)

theorem levSign_eq_one {a b : J} (hgen : Subgroup.closure ({a, b} : Set J) = ⊤)
    (hb : b ^ 3 = 1) (hab : (a * b) ^ 13 = 1) (g : J) : levSign F J hJ g = 1 := by
  have h1 : levSign F J hJ b = 1 :=
    units_eq_one_of_pow_odd (k := 3) (by decide) (by rw [← map_pow, hb, map_one])
  have h2 : levSign F J hJ (a * b) = 1 :=
    units_eq_one_of_pow_odd (k := 13) (by decide) (by rw [← map_pow, hab, map_one])
  have h3 : levSign F J hJ a = 1 := by
    rw [map_mul, h1, mul_one] at h2
    exact h2
  have hle : Subgroup.closure ({a, b} : Set J) ≤ (levSign F J hJ).ker := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact h3
    · exact h1
  rw [hgen] at hle
  exact hle (Subgroup.mem_top g)

theorem levSign_of_neg_one (g : J)
    (hg : ((g : GL (Fin n) (ZMod 3)) : Matrix (Fin n) (Fin n) (ZMod 3)) = -1) :
    levSign F J hJ g = (-1) ^ (Fintype.card (Lev F) / 2) := by
  let _ := levAction F J hJ
  have hσ : (MulAction.toPerm g : Equiv.Perm (Lev F)) = ⟨fun x => ⟨-x.1, by rw [qf_neg]; exact x.2⟩,
      fun x => ⟨-x.1, by rw [qf_neg]; exact x.2⟩, fun x => by simp, fun x => by simp⟩ := by
    ext x j
    show (((g : GL (Fin n) (ZMod 3)) : Matrix (Fin n) (Fin n) (ZMod 3)) *ᵥ x.1) j = -x.1 j
    rw [hg, neg_mulVec, one_mulVec]
    rfl
  have hsq : (MulAction.toPerm g : Equiv.Perm (Lev F)) ^ 2 = 1 := by
    rw [hσ]
    ext x j
    simp [sq, Equiv.Perm.mul_apply]
  have hfix : Fintype.card (Function.fixedPoints ((MulAction.toPerm g : Equiv.Perm (Lev F)))) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    refine ⟨fun ⟨x, hx⟩ => ?_⟩
    have hx' : -x.1 = x.1 := by
      have := congrArg Subtype.val hx
      rw [hσ] at this
      exact this
    have h0 : x.1 = 0 := by
      funext j
      have := congrFun hx' j
      have h2 : (2 : ZMod 3) * x.1 j = 0 := by
        rw [two_mul]
        nth_rewrite 1 [← this]
        simp
      have key : ∀ y : ZMod 3, 2 * y = 0 → y = 0 := by decide
      exact key _ h2
    have := x.2
    rw [h0, qf_zero] at this
    exact absurd this (by decide)
  show Equiv.Perm.sign ((MulAction.toPerm g : Equiv.Perm (Lev F))) = _
  rw [Equiv.Perm.sign_of_pow_two_eq_one hsq, hfix, Nat.sub_zero]

include hJ in
theorem ne_neg_one_of_sign {a b : J} (hgen : Subgroup.closure ({a, b} : Set J) = ⊤)
    (hb : b ^ 3 = 1) (hab : (a * b) ^ 13 = 1) (hcard : Fintype.card (Lev F) / 2 % 2 = 1)
    (g : J) : ((g : GL (Fin n) (ZMod 3)) : Matrix (Fin n) (Fin n) (ZMod 3)) ≠ -1 := by
  intro hg
  have h1 := levSign_eq_one F J hJ hgen hb hab g
  rw [levSign_of_neg_one F J hJ g hg] at h1
  have hodd : Odd (Fintype.card (Lev F) / 2) := Nat.odd_iff.2 hcard
  rw [hodd.neg_one_pow] at h1
  exact absurd h1 (by decide)

end Action

@[expose] def step3 (e : ZMod 3) (t : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  match t with
  | (a0, a1, a2) =>
    if e = 0 then (3 * a0, 3 * a1, 3 * a2)
    else if e = 1 then (a0 + 2 * a2, a1 + 2 * a0, a2 + 2 * a1)
    else (a0 + 2 * a1, a1 + 2 * a2, a2 + 2 * a0)

@[expose] def cnt3 : List (ZMod 3) → ℕ × ℕ × ℕ
  | [] => (1, 0, 0)
  | e :: es => step3 e (cnt3 es)

@[expose] def triAt (t : ℕ × ℕ × ℕ) (c : ZMod 3) : ℕ :=
  if c = 0 then t.1 else if c = 1 then t.2.1 else t.2.2

theorem triAt_step3 (e : ZMod 3) (t : ℕ × ℕ × ℕ) (c : ZMod 3) :
    triAt (step3 e t) c = triAt t c + 2 * triAt t (c - e) := by
  obtain ⟨a0, a1, a2⟩ := t
  have h : (e = 0 ∨ e = 1 ∨ e = 2) ∧ (c = 0 ∨ c = 1 ∨ c = 2) := by revert e c; decide
  obtain ⟨he, hc⟩ := h
  rcases he with rfl | rfl | rfl <;> rcases hc with rfl | rfl | rfl <;>
    simp (config := { decide := true }) only [step3, triAt, ite_true, ite_false] <;> ring

theorem sum_sq_zmod3 (f : ZMod 3 → ℕ) (e c : ZMod 3) :
    ∑ x : ZMod 3, f (c - e * x ^ 2) = f c + 2 * f (c - e) := by
  have huniv : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
  have h2 : (2 : ZMod 3) ^ 2 = 1 := by decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    h2]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_zero, one_pow,
    mul_one]
  ring

theorem card_diag : ∀ {k : ℕ} (e : Fin k → ZMod 3) (c : ZMod 3),
    Fintype.card {w : Fin k → ZMod 3 // ∑ i, e i * w i ^ 2 = c} = triAt (cnt3 (List.ofFn e)) c
  | 0, e, c => by
    have hs : ∀ w : Fin 0 → ZMod 3, ∑ i, e i * w i ^ 2 = 0 := fun w => by simp
    rw [List.ofFn_zero, cnt3]
    by_cases hc : c = 0
    · subst hc
      have h1 : triAt (1, 0, 0) 0 = 1 := rfl
      rw [h1, Fintype.card_eq_one_iff]
      exact ⟨⟨finZeroElim, hs _⟩, fun ⟨w, _⟩ => Subtype.ext (funext fun i => Fin.elim0 i)⟩
    · have h0 : triAt (1, 0, 0) c = 0 := by simp [triAt, hc]
      rw [h0, Fintype.card_eq_zero_iff]
      exact ⟨fun ⟨w, hw⟩ => hc (by rw [← hw, hs])⟩
  | k + 1, e, c => by
    rw [List.ofFn_succ, cnt3, triAt_step3]
    have ih := fun c' => card_diag (fun i : Fin k => e i.succ) c'
    let E : {w : Fin (k + 1) → ZMod 3 // ∑ i, e i * w i ^ 2 = c} ≃
        Σ x : ZMod 3, {w : Fin k → ZMod 3 // ∑ i, e i.succ * w i ^ 2 = c - e 0 * x ^ 2} :=
      { toFun := fun w => ⟨w.1 0, ⟨fun i : Fin k => w.1 i.succ, by
          have := w.2
          rw [Fin.sum_univ_succ] at this
          show ∑ i : Fin k, e i.succ * w.1 i.succ ^ 2 = c - e 0 * w.1 0 ^ 2
          linear_combination this⟩⟩
        invFun := fun p => ⟨(Fin.cons p.1 p.2.1 : Fin (k + 1) → ZMod 3), by
          rw [Fin.sum_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [p.2.2]
          ring⟩
        left_inv := fun w => by
          apply Subtype.ext
          funext i
          refine Fin.cases ?_ (fun j => ?_) i <;> simp
        right_inv := fun p => by
          obtain ⟨x, w, hw⟩ := p
          rfl }
    rw [Fintype.card_congr E, Fintype.card_sigma]
    simp only [ih]
    exact sum_sq_zmod3 (fun c' => triAt (cnt3 (List.ofFn fun i : Fin k => e i.succ)) c') (e 0) c

theorem qf_diagonal (d : Fin n → ZMod 3) (w : Fin n → ZMod 3) :
    qf (Matrix.diagonal d) w = ∑ i, (2 * d i) * w i ^ 2 := by
  unfold qf
  rw [dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mulVec_diagonal]
  ring

theorem card_lev_eq_diag (F P Pinv : Matrix (Fin n) (Fin n) (ZMod 3)) (d : Fin n → ZMod 3)
    (hP : Pinv * P = 1) (hPF : Pᵀ * F * P = Matrix.diagonal d) :
    Fintype.card (Lev F) =
      Fintype.card {w : Fin n → ZMod 3 // ∑ i, (2 * d i) * w i ^ 2 = 1} := by
  have hP' : P * Pinv = 1 := mul_eq_one_comm.1 hP
  have hq : ∀ w, qf F (P *ᵥ w) = qf (Matrix.diagonal d) w := by
    intro w
    rw [← hPF]
    unfold qf
    rw [dot_conj]
  refine Fintype.card_congr
    { toFun := fun x => ⟨Pinv *ᵥ x.1, by
        rw [← qf_diagonal, ← hq, mulVec_mulVec, hP', one_mulVec]; exact x.2⟩
      invFun := fun w => ⟨P *ᵥ w.1, by rw [hq, qf_diagonal]; exact w.2⟩
      left_inv := fun x => Subtype.ext (by simp [mulVec_mulVec, hP'])
      right_inv := fun w => Subtype.ext (by simp [mulVec_mulVec, hP]) }

end CFSG.Sporadic.Suz
