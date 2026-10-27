module

public import CFSG.RankThree.PartTwo.Sec21.Hering2119SModel
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Finsupp.Pointwise
public import Mathlib.RingTheory.SimpleRing.Principal

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2119S

open Module

theorem eq_of_smul_one {V : Type*} [AddCommGroup V] [Module F3 V] {a b : V}
    (h : (1 : F3) • a = (1 : F3) • b) : a = b := by simpa using h

section Coord

variable {V : Type*} [AddCommGroup V] [Module F3 V]

structure QRel (I J : V →ₗ[F3] V) : Prop where
  II : ∀ v, I (I v) = -v
  JJ : ∀ v, J (J v) = -v
  IJ : ∀ v, I (J v) = -J (I v)

theorem QRel.sub_P {I J : V →ₗ[F3] V} (h : QRel I J) (v : V) :
    v - (-v - I v - J v) = I (J (-(J (I v)) - I (J (I v)) - J (J (I v)))) := by
  refine eq_of_smul_one ?_
  simp only [map_neg, map_add, map_sub, h.II, h.JJ, h.IJ]
  match_scalars <;> decide

theorem QRel.J_P {I J : V →ₗ[F3] V} (h : QRel I J) (w : V) :
    J (-w - I w - J w) = (-w - I w - J w) - I (-w - I w - J w) := by
  refine eq_of_smul_one ?_
  simp only [map_neg, map_add, map_sub, h.II, h.JJ, h.IJ]
  match_scalars <;> decide

structure CoordHyp (I J ε : V →ₗ[F3] V) : Prop extends QRel I J where
  Iε : ∀ v, I (ε v) = ε (I v)
  Jε : ∀ v, J (ε v) = ε (J v)
  εε : ∀ v, ε (ε v) = 0

theorem CoordHyp.exists_good {I J ε : V →ₗ[F3] V} (h : CoordHyp I J ε) (hε0 : ∃ v, ε v ≠ 0) :
    ∃ u : V, J u = u - I u ∧ ε u ≠ 0 := by
  obtain ⟨v, hv⟩ := hε0
  by_cases hP : ε (-v - I v - J v) = 0
  · set w := J (I v) with hw
    refine ⟨-w - I w - J w, h.J_P w, fun hz => hv ?_⟩
    have h1 : v = (-v - I v - J v) + I (J (-w - I w - J w)) := by
      have := h.sub_P v
      rw [← hw] at this
      calc v = (-v - I v - J v) + (v - (-v - I v - J v)) := by abel
        _ = _ := by rw [this]
    have h2 : ε (I (J (-w - I w - J w))) = 0 := by
      rw [← h.Iε, ← h.Jε, hz, map_zero, map_zero]
    calc ε v = ε ((-v - I v - J v) + I (J (-w - I w - J w))) := by rw [← h1]
      _ = 0 := by rw [map_add, hP, h2, add_zero]
  · refine ⟨-v - I v - J v, h.J_P v, hP⟩

@[expose] def bvec (I ε : V →ₗ[F3] V) (u : V) : Fin 2 × Fin 2 → V :=
  fun k => ![![u, I u], ![ε u, ε (I u)]] k.1 k.2

theorem CoordHyp.relations {I J ε : V →ₗ[F3] V} (h : CoordHyp I J ε) {u : V}
    (hJu : J u = u - I u) :
    J (I u) = -I u - u ∧ J (ε u) = ε u - ε (I u) ∧ J (ε (I u)) = -ε (I u) - ε u ∧
      I (I u) = -u ∧ I (ε u) = ε (I u) ∧ I (ε (I u)) = -ε u := by
  have e1 : J (I u) = -I u - u := by
    have hJI : J (I u) = -I (J u) := by rw [h.IJ u, neg_neg]
    rw [hJI, hJu, map_sub, h.II]
    abel
  refine ⟨e1, ?_, ?_, h.II u, h.Iε u, ?_⟩
  · rw [h.Jε, hJu, map_sub]
  · rw [h.Jε, e1, map_sub, map_neg]
  · rw [h.Iε, h.II, map_neg]

theorem pair_zero {I J ε : V →ₗ[F3] V} (h : CoordHyp I J ε) {u : V} (hεu : ε u ≠ 0) (c d : F3)
    (hcd : c • u + d • ε u = 0) : c = 0 ∧ d = 0 := by
  have h1 : ε (c • u + d • ε u) = 0 := by rw [hcd, map_zero]
  rw [map_add, map_smul, map_smul, h.εε, smul_zero, add_zero] at h1
  have hc : c = 0 := by
    by_contra hc
    exact hεu ((smul_eq_zero.mp h1).resolve_left hc)
  refine ⟨hc, ?_⟩
  rw [hc, zero_smul, zero_add] at hcd
  by_contra hd
  exact hεu ((smul_eq_zero.mp hcd).resolve_left hd)

theorem CoordHyp.E1 {I J ε : V →ₗ[F3] V} (h : CoordHyp I J ε) {u : V}
    (hJu : J u = u - I u) (a b c d : F3) :
    (-(a • u + b • I u + (c • ε u + d • ε (I u))) -
        I (a • u + b • I u + (c • ε u + d • ε (I u))) -
        J (a • u + b • I u + (c • ε u + d • ε (I u)))) =
        (a - b) • u + (c - d) • ε u := by
  obtain ⟨hJIu, hJεu, hJεIu, hIIu, hIεu, hIεIu⟩ := h.relations hJu
  refine eq_of_smul_one ?_
  simp only [map_neg, map_add, map_smul, map_sub, hJu, hJIu, hJεu, hJεIu, hIIu, hIεu, hIεIu]
  match_scalars <;> (revert a b c d; decide)

theorem CoordHyp.E2 {I J ε : V →ₗ[F3] V} (h : CoordHyp I J ε) {u : V}
    (hJu : J u = u - I u) (a b c d : F3) :
    (-(I (a • u + b • I u + (c • ε u + d • ε (I u)))) -
        I (I (a • u + b • I u + (c • ε u + d • ε (I u)))) -
        J (I (a • u + b • I u + (c • ε u + d • ε (I u))))) =
        (-(a + b)) • u + (-(c + d)) • ε u := by
  obtain ⟨hJIu, hJεu, hJεIu, hIIu, hIεu, hIεIu⟩ := h.relations hJu
  refine eq_of_smul_one ?_
  simp only [map_neg, map_add, map_smul, map_sub, hJu, hJIu, hJεu, hJεIu, hIIu, hIεu, hIεIu,
    h.II, h.JJ, h.IJ]
  match_scalars <;> (revert a b c d; decide)

theorem CoordHyp.linIndep {I J ε : V →ₗ[F3] V} (h : CoordHyp I J ε) {u : V}
    (hJu : J u = u - I u) (hεu : ε u ≠ 0) : LinearIndependent F3 (bvec I ε u) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [bvec, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hg
  have key : ∀ a b c d : F3, (a • u + b • I u + (c • ε u + d • ε (I u)) = 0) →
      a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
    intro a b c d hS
    have E1 := h.E1 hJu a b c d
    have E2 := h.E2 hJu a b c d
    simp only [hS, map_zero, neg_zero, sub_zero] at E1 E2
    obtain ⟨h1, h2⟩ := pair_zero h hεu _ _ E1.symm
    obtain ⟨h3, h4⟩ := pair_zero h hεu _ _ E2.symm
    clear E1 E2 hS
    revert h1 h2 h3 h4
    revert a b c d
    decide
  have := key (g (0, 0)) (g (0, 1)) (g (1, 0)) (g (1, 1)) (by simpa using hg)
  rintro ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> simp [this]

theorem CoordHyp.exists_coord [Finite V] (hV : Nat.card V = 81) {I J ε : V →ₗ[F3] V}
    (h : CoordHyp I J ε) (hε0 : ∃ v, ε v ≠ 0) :
    ∃ b : Basis (Fin 2 × Fin 2) F3 V, LinearMap.toMatrix b b I = kr 1 I2m0 ∧
      LinearMap.toMatrix b b J = kr 1 J2m0 ∧ LinearMap.toMatrix b b ε = kr nU 1 := by
  obtain ⟨u, hJu, hεu⟩ := h.exists_good hε0
  have hli := h.linIndep hJu hεu
  haveI : Module.Finite F3 V := Module.Finite.of_finite
  have hfr : Module.finrank F3 V = 4 := by
    have h1 := Module.natCard_eq_pow_finrank (K := F3) (V := V)
    rw [hV, Nat.card_zmod] at h1
    have h2 : (3 : ℕ) ^ 4 = 3 ^ Module.finrank F3 V := by rw [← h1]; norm_num
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h2).symm
  let b : Basis (Fin 2 × Fin 2) F3 V :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [hfr])
  have hb : ∀ k, b k = bvec I ε u k := fun k => by
    simp [b]
  have b00 : b (0, 0) = u := by rw [hb]; rfl
  have b01 : b (0, 1) = I u := by rw [hb]; rfl
  have b10 : b (1, 0) = ε u := by rw [hb]; rfl
  have b11 : b (1, 1) = ε (I u) := by rw [hb]; rfl
  obtain ⟨hJIu, hJεu, hJεIu, hIIu, hIεu, hIεIu⟩ := h.relations hJu
  have hrepr : ∀ (k a : Fin 2 × Fin 2), b.repr (b k) a = if k = a then 1 else 0 := by
    intro k a
    rw [Basis.repr_self, Finsupp.single_apply]
  have hrneg : ∀ (x : V) (a : Fin 2 × Fin 2), b.repr (-x) a = -b.repr x a := fun x a => by
    rw [map_neg]; exact Finsupp.neg_apply _ a
  have hrsub : ∀ (x y : V) (a : Fin 2 × Fin 2), b.repr (x - y) a = b.repr x a - b.repr y a :=
    fun x y a => by rw [map_sub]; exact Finsupp.sub_apply _ _ a
  have I00 : I (b (0, 0)) = b (0, 1) := by rw [b00, b01]
  have I01 : I (b (0, 1)) = -b (0, 0) := by rw [b00, b01, hIIu]
  have I10 : I (b (1, 0)) = b (1, 1) := by rw [b10, b11, hIεu]
  have I11 : I (b (1, 1)) = -b (1, 0) := by rw [b10, b11, hIεIu]
  have J00 : J (b (0, 0)) = b (0, 0) - b (0, 1) := by rw [b00, b01, hJu]
  have J01 : J (b (0, 1)) = -b (0, 1) - b (0, 0) := by rw [b00, b01, hJIu]
  have J10 : J (b (1, 0)) = b (1, 0) - b (1, 1) := by rw [b10, b11, hJεu]
  have J11 : J (b (1, 1)) = -b (1, 1) - b (1, 0) := by rw [b10, b11, hJεIu]
  have E00 : ε (b (0, 0)) = b (1, 0) := by rw [b00, b10]
  have E01 : ε (b (0, 1)) = b (1, 1) := by rw [b01, b11]
  have E10 : ε (b (1, 0)) = 0 := by rw [b10, h.εε]
  have E11 : ε (b (1, 1)) = 0 := by rw [b11, h.εε]
  have hmat : ∀ (f : V →ₗ[F3] V) (M : Mat4),
      (∀ k : Fin 2 × Fin 2, f (b k) = ∑ l, M l k • b l) → LinearMap.toMatrix b b f = M := by
    intro f M hf
    have : f = Matrix.toLin b b M := b.ext fun k => by rw [Matrix.toLin_self, hf k]
    rw [this, LinearMap.toMatrix_toLin]
  refine ⟨b, hmat I _ ?_, hmat J _ ?_, hmat ε _ ?_⟩
  · rintro ⟨c, j⟩
    fin_cases c <;> fin_cases j <;>
      simp [Fintype.sum_prod_type, Fin.sum_univ_two, kr_apply, I2m0, Matrix.one_apply,
        I00, I01, I10, I11, neg_smul, neg_one_smul F3]
    all_goals exact (neg_one_smul F3 _).symm
  · rintro ⟨c, j⟩
    fin_cases c <;> fin_cases j <;>
      simp [Fintype.sum_prod_type, Fin.sum_univ_two, kr_apply, J2m0, Matrix.one_apply,
        J00, J01, J10, J11, neg_smul, neg_one_smul F3]
    all_goals (match_scalars <;> decide)
  · rintro ⟨c, j⟩
    fin_cases c <;> fin_cases j <;>
      simp [Fintype.sum_prod_type, Fin.sum_univ_two, kr_apply, Matrix.one_apply,
        E00, E01, E10, E11, nU, Matrix.of_apply, Matrix.cons_val']

end Coord

end CFSG.RankThree.PartTwo.Sec21.Hering2119S
