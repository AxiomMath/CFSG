module

public import CFSG.LocalAnalysis.StandardType.FS81.AutMat
public import CFSG.LocalAnalysis.StandardType.FS81.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

public noncomputable section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem coordinates_prod_single {k : ℕ} (v : Coords k) :
    (List.ofFn fun i : Fin k =>
      (Multiplicative.ofAdd (Pi.single i (1 : ZMod 3) : Coords k)) ^ (v i).val).prod =
      Multiplicative.ofAdd v := by
  have hpow : ∀ i : Fin k,
      (Multiplicative.ofAdd (Pi.single i (1 : ZMod 3) : Coords k)) ^ (v i).val =
        Multiplicative.ofAdd (Pi.single i (v i)) := by
    intro i
    change (v i).val • (Pi.single i (1 : ZMod 3) : Coords k) = Pi.single i (v i)
    ext j
    by_cases h : j = i
    · subst j
      simp [nsmul_eq_mul]
    · simp [Pi.single_eq_of_ne h]
  simp only [hpow]
  have hsum : (List.ofFn fun i : Fin k => Pi.single i (v i)).sum = v := by
    rw [List.sum_ofFn]
    funext j
    simp only [Finset.sum_apply]
    exact Fintype.sum_pi_single j v
  simpa only [List.map_ofFn, Function.comp_def, hsum] using
    (ofAdd_list_prod (List.ofFn fun i : Fin k => Pi.single i (v i))).symm

namespace Basis3

variable {G : Type} [Group G] {k : ℕ}

@[expose] def rebaseHom (B : Basis3 G k) (e : Coords k ≃ₗ[ZMod 3] Coords k) :
    Multiplicative (Coords k) →* G :=
  B.span.subtype.comp (B.equiv.toMonoidHom.comp
    e.toAddEquiv.toMultiplicative.toMonoidHom)

theorem rebaseHom_apply (B : Basis3 G k) (e : Coords k ≃ₗ[ZMod 3] Coords k)
    (v : Coords k) : B.rebaseHom e (Multiplicative.ofAdd v) = B.vec (e v) := rfl

theorem rebaseHom_injective (B : Basis3 G k) (e : Coords k ≃ₗ[ZMod 3] Coords k) :
    Function.Injective (B.rebaseHom e) := by
  intro x y h
  change x.toAdd = y.toAdd
  exact e.injective (B.vec_injective h)

theorem rebase_prod (B : Basis3 G k) (e : Coords k ≃ₗ[ZMod 3] Coords k)
    (v : Coords k) :
    (List.ofFn fun i : Fin k =>
      (B.rebaseHom e (Multiplicative.ofAdd (Pi.single i 1))) ^ (v i).val).prod =
        B.vec (e v) := by
  have h := congrArg (B.rebaseHom e) (coordinates_prod_single v)
  simpa only [map_list_prod, List.map_ofFn, Function.comp_def, map_pow,
    rebaseHom_apply] using h

@[expose] def rebase (B : Basis3 G k) (e : Coords k ≃ₗ[ZMod 3] Coords k) : Basis3 G k where
  b i := B.rebaseHom e (Multiplicative.ofAdd (Pi.single i 1))
  comm i j := (show Commute (Multiplicative.ofAdd (Pi.single i 1 : Coords k))
    (Multiplicative.ofAdd (Pi.single j 1 : Coords k)) from mul_comm _ _).map _
  ord i := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow]
      have h : (Multiplicative.ofAdd (Pi.single i (1 : ZMod 3) : Coords k)) ^ 3 = 1 := by
        change (3 : ℕ) • (Pi.single i (1 : ZMod 3) : Coords k) = 0
        ext j
        simp [Pi.single_apply, nsmul_eq_mul, show (3 : ZMod 3) = 0 by decide]
      rw [h, map_one]
    · intro h
      have h' := B.rebaseHom_injective e (h.trans (map_one (B.rebaseHom e)).symm)
      have h'' := congrArg (fun x : Multiplicative (Coords k) => x.toAdd i) h'
      simp at h''
  indep v hv := by
    rw [B.rebase_prod e] at hv
    exact e.injective ((B.indep (e v) hv).trans e.map_zero.symm)

theorem vec_rebase (B : Basis3 G k) (e : Coords k ≃ₗ[ZMod 3] Coords k) (v : Coords k) :
    (B.rebase e).vec v = B.vec (e v) := B.rebase_prod e v

theorem span_rebase (B : Basis3 G k) (e : Coords k ≃ₗ[ZMod 3] Coords k) :
    (B.rebase e).span = B.span := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨i, rfl⟩
    exact B.vec_mem_span _
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨i, rfl⟩
    have h := (B.rebase e).vec_mem_span (e.symm (Pi.single i 1))
    change B.b i ∈ (B.rebase e).span
    simpa only [vec_rebase, e.apply_symm_apply, vec_single] using h

end Basis3

@[expose] def twD7BetaCoordinates : Coords 8 ≃ₗ[ZMod 3] Coords 8 where
  toFun v i := if i = 0 then v 0 - v 1 else if i = 1 then v 0 + v 1 else v i
  invFun v i := if i = 0 then -v 0 - v 1 else if i = 1 then v 0 - v 1 else v i
  left_inv v := by
    ext i
    by_cases h0 : i = 0
    · subst i
      simp only [if_pos, if_neg (show (0 : Fin 8) ≠ 1 by decide)]
      calc -(v 0 - v 1) - (v 0 + v 1) = (-2 : ZMod 3) * v 0 := by ring
        _ = v 0 := by rw [show (-2 : ZMod 3) = 1 by decide, one_mul]
    · by_cases h1 : i = 1
      · subst i
        simp only [if_pos, if_neg (show (1 : Fin 8) ≠ 0 by decide)]
        calc (v 0 - v 1) - (v 0 + v 1) = (-2 : ZMod 3) * v 1 := by ring
          _ = v 1 := by rw [show (-2 : ZMod 3) = 1 by decide, one_mul]
      · simp only [if_neg h0, if_neg h1]
  right_inv v := by
    ext i
    by_cases h0 : i = 0
    · subst i
      simp only [if_pos, if_neg (show (0 : Fin 8) ≠ 1 by decide)]
      calc (-v 0 - v 1) - (v 0 - v 1) = (-2 : ZMod 3) * v 0 := by ring
        _ = v 0 := by rw [show (-2 : ZMod 3) = 1 by decide, one_mul]
    · by_cases h1 : i = 1
      · subst i
        simp only [if_pos, if_neg (show (1 : Fin 8) ≠ 0 by decide)]
        calc (-v 0 - v 1) + (v 0 - v 1) = (-2 : ZMod 3) * v 1 := by ring
          _ = v 1 := by rw [show (-2 : ZMod 3) = 1 by decide, one_mul]
      · simp only [if_neg h0, if_neg h1]
  map_add' v w := by
    ext i
    by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;>
      simp [h0, h1, sub_eq_add_neg] <;> ring
  map_smul' a v := by
    ext i
    by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;>
      simp [h0, h1, mul_sub, mul_add]

namespace Basis3

variable {G : Type} [Group G] (B : Basis3 G 8)

@[expose] def twD7Beta : Basis3 G 8 := B.rebase twD7BetaCoordinates

theorem twD7Beta_b_zero : B.twD7Beta.b 0 = B.b 0 * B.b 1 := by
  change B.vec (twD7BetaCoordinates (Pi.single 0 1)) = _
  have h : twD7BetaCoordinates (Pi.single 0 1) =
      (Pi.single 0 1 : Coords 8) + Pi.single 1 1 := by
    decide +kernel
  rw [h, B.vec_add, B.vec_single, B.vec_single]

theorem twD7Beta_b_one : B.twD7Beta.b 1 = (B.b 0)⁻¹ * B.b 1 := by
  change B.vec (twD7BetaCoordinates (Pi.single 1 1)) = _
  have h : twD7BetaCoordinates (Pi.single 1 1) =
      -(Pi.single 0 1 : Coords 8) + Pi.single 1 1 := by
    decide +kernel
  rw [h, B.vec_add]
  have hneg : B.vec (-(Pi.single 0 1 : Coords 8)) = (B.b 0)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← B.vec_single 0, ← B.vec_add, neg_add_cancel, B.vec_zero]
  rw [hneg, B.vec_single]

theorem twD7Beta_b_succ_succ (i : Fin 6) : B.twD7Beta.b i.succ.succ = B.b i.succ.succ := by
  change B.vec (twD7BetaCoordinates (Pi.single i.succ.succ 1)) = _
  have h : twD7BetaCoordinates (Pi.single i.succ.succ 1) = Pi.single i.succ.succ 1 := by
    revert i
    decide +kernel
  rw [h, B.vec_single]

theorem twD7Beta_span : B.twD7Beta.span = B.span := B.span_rebase twD7BetaCoordinates

end Basis3

end CFSG.StandardType.FrameRoute.FS81
