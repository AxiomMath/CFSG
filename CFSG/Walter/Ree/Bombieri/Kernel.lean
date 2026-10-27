module

public import CFSG.Walter.Ree.Bombieri.MatrixDef
public import CFSG.Walter.Ree.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.Walter.Ree.Bombieri

namespace Elim

variable {K : Type*} [Field K]

@[expose] def eqE0 (z1 y1 A B C : K) : K := z1 * A - (z1 - y1 + 1) * B - y1 * C + A * C

@[expose] def eqE1 (z0 y0 u0 A B C : K) : K :=
  z0 * (u0 - 1) ^ 2 * (B * C) - (z0 - y0 + 1) * u0 ^ 2 * (A * C) - y0 * (u0 + 1) ^ 2 * (A * B) +
    (u0 ^ 2 - 1) ^ 2 * B

@[expose] def eqE2 (z3 y3 u1 u2 A B C : K) : K :=
  z3 * (u2 - 1) ^ 2 * u1 ^ 2 * (u1 + 1) ^ 2 * A -
    (z3 - y3 + 1) * u2 ^ 2 * (u1 - 1) ^ 2 * (u1 + 1) ^ 2 * B -
    y3 * (u2 + 1) ^ 2 * (u1 - 1) ^ 2 * u1 ^ 2 * C + (u2 ^ 2 - 1) ^ 2 * u1 ^ 2 * (A * C)

@[expose] def eqE3 (z2 y2 u1 A B C : K) : K :=
  z2 * (u1 - 1) ^ 2 * (B * C) - (z2 - y2 + 1) * u1 ^ 2 * (A * C) - y2 * (u1 + 1) ^ 2 * (A * B) +
    (u1 ^ 2 - 1) ^ 2 * B

@[expose] def ptVars (z0 z1 z2 z3 y0 : K) : ℕ → K
  | 0 => z0 | 1 => z1 | 2 => z2 | 3 => z3 | 4 => y0 | _ => 0

@[expose] def ptAtoms (y0 y1 y2 y3 u0 u1 u2 : K) : ℕ → K
  | 0 => y1 * y0 ^ 2
  | 1 => y2 * y1 ^ 2
  | 2 => y3 * y2 ^ 2
  | 3 => y0 * u0
  | 4 => y1 * y0 ^ 2 * u1
  | 5 => y2 * y1 ^ 2 * y0 ^ 4
  | 6 => y2 * y1 ^ 2 * y0 ^ 4 * u2
  | _ => 0

@[expose] def monVec (A B C : K) : Fin 12 → K :=
  ![B, A ^ 2, B ^ 2, C ^ 2, A * B, A * C, B * C, A ^ 2 * B, A ^ 2 * C, A * C ^ 2, B * C ^ 2,
    A * B * C]

theorem rows (z0 z1 z2 z3 y0 y1 y2 y3 u0 u1 u2 A B C : K) :
    let ρ := ptVars z0 z1 z2 z3 y0
    let α := ptAtoms y0 y1 y2 y3 u0 u1 u2
    let ζ0 := y1 * y0 ^ 2
    let W := y2 * y1 ^ 2 * y0 ^ 4
    (Matrix.of fun i j => (ent i j).eval ρ α).mulVec (monVec A B C) =
      ![y0 ^ 4 * eqE1 z0 y0 u0 A B C,
        y0 ^ 2 * A * eqE0 z1 y1 A B C,
        y0 ^ 2 * B * eqE0 z1 y1 A B C,
        y0 ^ 2 * C * eqE0 z1 y1 A B C,
        ζ0 ^ 4 * eqE3 z2 y2 u1 A B C,
        W ^ 4 * ζ0 ^ 4 * A * eqE2 z3 y3 u1 u2 A B C,
        W ^ 4 * ζ0 ^ 4 * B * eqE2 z3 y3 u1 u2 A B C,
        y0 ^ 4 * A * eqE1 z0 y0 u0 A B C,
        ζ0 ^ 4 * A * eqE3 z2 y2 u1 A B C,
        W ^ 4 * ζ0 ^ 4 * C * eqE2 z3 y3 u1 u2 A B C,
        y0 ^ 4 * C * eqE1 z0 y0 u0 A B C,
        ζ0 ^ 4 * C * eqE3 z2 y2 u1 A B C] := by
  intro ρ α ζ0 W
  ext i
  fin_cases i <;>
  simp [ρ, α, ζ0, W, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, ent, monVec, ptVars,
    ptAtoms, a0, b0, c0, e0, b1, d1, e1, f1, a2, b2, c2, e2, b3, d3, e3, f3, vz0, vz1, vz2, vz3,
    vy, aζ0, aζ2, aU0, aU1, aW, aU2, eqE0, eqE1, eqE2, eqE3] <;>
  ring

theorem atomsOf_eq {z0 z1 z2 z3 y0 y1 y2 y3 u0 u1 u2 : K}
    (hy1 : y1 * y0 ^ 2 = 1 + z1 * z0 ^ 2) (hy2 : y2 * y1 ^ 2 = 1 + z2 * z1 ^ 2)
    (hy3 : y3 * y2 ^ 2 = 1 + z3 * z2 ^ 2) (hu0 : u0 = z1 * z0 - y1 * y0)
    (hu1 : u1 = z2 * z1 - y2 * y1) (hu2 : u2 = z3 * z2 - y3 * y2) :
    atomsOf (ptVars z0 z1 z2 z3 y0) = ptAtoms y0 y1 y2 y3 u0 u1 u2 := by
  funext k
  rcases k with _ | _ | _ | _ | _ | _ | _ | k <;>
    simp only [atomsOf, atomDef, ptVars, ptAtoms, PE.eval_var, PE.eval_add, PE.eval_sub,
      PE.eval_mul, PE.eval_pow, PE.eval_one, PE.eval_zero]
  · linear_combination -hy1
  · linear_combination -hy2
  · linear_combination -hy3
  · rw [hu0]; linear_combination hy1
  · rw [hu1]; linear_combination -(z2 * z1) * hy1 + y0 ^ 2 * hy2
  · linear_combination -(y0 ^ 4) * hy2
  · rw [hu2]
    linear_combination -(z3 * z2 * y0 ^ 4) * hy2 + (y1 * y0 ^ 2) ^ 2 * hy3 +
      (1 + z3 * z2 ^ 2) * (y1 * y0 ^ 2 + 1 + z1 * z0 ^ 2) * hy1

theorem eqs_zero {z0 z1 z2 z3 y0 y1 y2 y3 u0 u1 u2 X0 Y0 Z0 A B C X2 Y2 Z2 X3 Y3 Z3 : K}
    (hT0 : z0 * X0 - (z0 - y0 + 1) * Y0 - y0 * Z0 + X0 * Z0 = 0)
    (hT1 : z1 * A - (z1 - y1 + 1) * B - y1 * C + A * C = 0)
    (hT2 : z2 * X2 - (z2 - y2 + 1) * Y2 - y2 * Z2 + X2 * Z2 = 0)
    (hT3 : z3 * X3 - (z3 - y3 + 1) * Y3 - y3 * Z3 + X3 * Z3 = 0)
    (hX0 : X0 * A = (u0 - 1) ^ 2) (hY0 : Y0 * B = u0 ^ 2) (hZ0 : Z0 * C = (u0 + 1) ^ 2)
    (hX2 : X2 * A = (u1 - 1) ^ 2) (hY2 : Y2 * B = u1 ^ 2) (hZ2 : Z2 * C = (u1 + 1) ^ 2)
    (hX3 : X3 * X2 = (u2 - 1) ^ 2) (hY3 : Y3 * Y2 = u2 ^ 2) (hZ3 : Z3 * Z2 = (u2 + 1) ^ 2) :
    eqE0 z1 y1 A B C = 0 ∧ eqE1 z0 y0 u0 A B C = 0 ∧ eqE2 z3 y3 u1 u2 A B C = 0 ∧
      eqE3 z2 y2 u1 A B C = 0 := by
  have hP : X3 * (u1 - 1) ^ 2 = (u2 - 1) ^ 2 * A := by
    rw [← hX2, ← hX3]; ring
  have hQ : Y3 * u1 ^ 2 = u2 ^ 2 * B := by
    rw [← hY2, ← hY3]; ring
  have hR : Z3 * (u1 + 1) ^ 2 = (u2 + 1) ^ 2 * C := by
    rw [← hZ2, ← hZ3]; ring
  refine ⟨hT1, ?_, ?_, ?_⟩
  · have e : A * B * C * (z0 * X0 - (z0 - y0 + 1) * Y0 - y0 * Z0 + X0 * Z0) =
        z0 * (X0 * A) * (B * C) - (z0 - y0 + 1) * (Y0 * B) * (A * C) -
          y0 * (Z0 * C) * (A * B) + (X0 * A) * (Z0 * C) * B := by ring
    rw [hT0, mul_zero, hX0, hY0, hZ0] at e
    unfold eqE1
    linear_combination -e
  · have e : u1 ^ 2 * (u1 - 1) ^ 2 * (u1 + 1) ^ 2 *
        (z3 * X3 - (z3 - y3 + 1) * Y3 - y3 * Z3 + X3 * Z3) =
        z3 * (X3 * (u1 - 1) ^ 2) * u1 ^ 2 * (u1 + 1) ^ 2 -
          (z3 - y3 + 1) * (Y3 * u1 ^ 2) * (u1 - 1) ^ 2 * (u1 + 1) ^ 2 -
          y3 * (Z3 * (u1 + 1) ^ 2) * (u1 - 1) ^ 2 * u1 ^ 2 +
          (X3 * (u1 - 1) ^ 2) * (Z3 * (u1 + 1) ^ 2) * u1 ^ 2 := by ring
    rw [hT3, mul_zero, hP, hQ, hR] at e
    unfold eqE2
    linear_combination -e
  · have e : A * B * C * (z2 * X2 - (z2 - y2 + 1) * Y2 - y2 * Z2 + X2 * Z2) =
        z2 * (X2 * A) * (B * C) - (z2 - y2 + 1) * (Y2 * B) * (A * C) -
          y2 * (Z2 * C) * (A * B) + (X2 * A) * (Z2 * C) * B := by ring
    rw [hT2, mul_zero, hX2, hY2, hZ2] at e
    unfold eqE3
    linear_combination -e

theorem _root_.CFSG.Walter.Ree.ESigma.map {σ : K ≃+* K} {p : K × K × K}
    (hp : p ∈ ESigma K σ) : (σ p.1, σ p.2.1, σ p.2.2) ∈ ESigma K σ := by
  obtain ⟨h1, h2, h3⟩ := hp
  refine ⟨?_, ?_, ?_⟩
  · simpa using congrArg σ h1
  · simpa using congrArg σ h2
  · intro h
    apply h3
    apply σ.injective
    simpa using h

theorem det_matOf_eq_zero {σ : K ≃+* K} {a : ℕ} (hB : ∀ x : K, (σ x * x) ^ a = x ^ 2)
    (hC : ∀ p ∈ ESigma K σ, thompsonT a p.1 p.2.1 p.2.2 = 0) {p : K × K × K}
    (hp : p ∈ ESigma K σ) :
    (matOf (ptVars p.1 (σ p.1) (σ (σ p.1)) (σ (σ (σ p.1))) p.2.1)).det = 0 := by
  obtain ⟨z, y, u⟩ := p
  have hp1 := ESigma.map hp
  have hp2 := ESigma.map hp1
  have hp3 := ESigma.map hp2
  simp only at hp1 hp2 hp3 ⊢
  have hy (q : K × K × K) (hq : q ∈ ESigma K σ) : σ q.2.1 * q.2.1 ^ 2 = 1 + σ q.1 * q.1 ^ 2 := by
    linear_combination -hq.1
  have hu (q : K × K × K) (hq : q ∈ ESigma K σ) : q.2.2 = σ q.1 * q.1 - σ q.2.1 * q.2.1 :=
    hq.2.1.symm
  have hy1 := hy _ hp
  have hy2 := hy _ hp1
  have hy3 := hy _ hp2
  have hu0 := hu _ hp
  have hu1 := hu _ hp1
  have hu2 := hu _ hp2
  simp only at hy1 hy2 hy3 hu0 hu1 hu2
  have hT (q : K × K × K) (hq : q ∈ ESigma K σ) :
      q.1 * (q.2.2 - 1) ^ a - (q.1 - q.2.1 + 1) * q.2.2 ^ a - q.2.1 * (q.2.2 + 1) ^ a +
        (q.2.2 - 1) ^ a * (q.2.2 + 1) ^ a = 0 := by
    have := hC q hq
    simp only [thompsonT] at this
    rw [show q.2.2 ^ 2 - 1 = (q.2.2 - 1) * (q.2.2 + 1) by ring, mul_pow] at this
    exact this
  have hT0 := hT _ hp
  have hT1 := hT _ hp1
  have hT2 := hT _ hp2
  have hT3 := hT _ hp3
  simp only at hT0 hT1 hT2 hT3
  have hBw (w : K) : (σ w) ^ a * w ^ a = w ^ 2 := by rw [← mul_pow]; exact hB w
  have hm (w : K) (c : K) (hc : σ c = c) : (σ w + c) ^ a * (w + c) ^ a = (w + c) ^ 2 := by
    have := hBw (w + c); rwa [map_add, hc] at this
  have hσ1 : σ (1 : K) = 1 := map_one σ
  have hσm1 : σ (-1 : K) = -1 := by simp
  have hX0 : (u - 1) ^ a * (σ u - 1) ^ a = (u - 1) ^ 2 := by
    rw [mul_comm]; simpa [sub_eq_add_neg] using hm u (-1) hσm1
  have hY0 : u ^ a * (σ u) ^ a = u ^ 2 := by rw [mul_comm]; exact hBw u
  have hZ0 : (u + 1) ^ a * (σ u + 1) ^ a = (u + 1) ^ 2 := by
    rw [mul_comm]; exact hm u 1 hσ1
  have hX2 : (σ (σ u) - 1) ^ a * (σ u - 1) ^ a = (σ u - 1) ^ 2 := by
    simpa [sub_eq_add_neg] using hm (σ u) (-1) hσm1
  have hY2 : (σ (σ u)) ^ a * (σ u) ^ a = (σ u) ^ 2 := hBw (σ u)
  have hZ2 : (σ (σ u) + 1) ^ a * (σ u + 1) ^ a = (σ u + 1) ^ 2 := hm (σ u) 1 hσ1
  have hX3 : (σ (σ (σ u)) - 1) ^ a * (σ (σ u) - 1) ^ a = (σ (σ u) - 1) ^ 2 := by
    simpa [sub_eq_add_neg] using hm (σ (σ u)) (-1) hσm1
  have hY3 : (σ (σ (σ u))) ^ a * (σ (σ u)) ^ a = (σ (σ u)) ^ 2 := hBw (σ (σ u))
  have hZ3 : (σ (σ (σ u)) + 1) ^ a * (σ (σ u) + 1) ^ a = (σ (σ u) + 1) ^ 2 :=
    hm (σ (σ u)) 1 hσ1
  obtain ⟨hE0, hE1, hE2, hE3⟩ := eqs_zero hT0 hT1 hT2 hT3 hX0 hY0 hZ0 hX2 hY2 hZ2 hX3 hY3 hZ3
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨monVec ((σ u - 1) ^ a) ((σ u) ^ a) ((σ u + 1) ^ a), ?_, ?_⟩
  · intro h0
    have h1 := congrFun h0 0
    simp only [monVec, Matrix.cons_val_zero, Pi.zero_apply] at h1
    have hu0' : σ u ≠ 0 := by
      intro h; apply hp1.2.2; simp only at h ⊢; rw [h]; ring
    exact pow_ne_zero a hu0' h1
  · have hmat : matOf (ptVars z (σ z) (σ (σ z)) (σ (σ (σ z))) y) =
        Matrix.of fun i j => (ent i j).eval (ptVars z (σ z) (σ (σ z)) (σ (σ (σ z))) y)
          (ptAtoms y (σ y) (σ (σ y)) (σ (σ (σ y))) u (σ u) (σ (σ u))) := by
      rw [matOf, atomsOf_eq hy1 hy2 hy3 hu0 hu1 hu2]
    rw [hmat, rows]
    simp [hE0, hE1, hE2, hE3]

end Elim

end CFSG.Walter.Ree.Bombieri
