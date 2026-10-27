module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaCoord

public section

namespace CFSG.StandardType.E6QTwo

open Module CFSG.Assembly
open scoped Matrix

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]

@[expose] def stdRefl (r c : Fin 5 → ZMod 3) : Fin 5 → ZMod 3 :=
  c - (r ⬝ᵥ c) • r

theorem stdRefl_involutive {r : Fin 5 → ZMod 3} (hr : r ⬝ᵥ r = 2) (x : Fin 5 → ZMod 3) :
    stdRefl r (stdRefl r x) = x := by
  have hd : r ⬝ᵥ stdRefl r x = -(r ⬝ᵥ x) := by
    rw [stdRefl, dotProduct_sub, dotProduct_smul, hr, smul_eq_mul]
    exact (by decide : ∀ d : ZMod 3, d - d * 2 = -d) (r ⬝ᵥ x)
  have hneg : (-(r ⬝ᵥ x)) • r = -((r ⬝ᵥ x) • r) := by
    funext j
    simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    exact neg_mul (r ⬝ᵥ x) (r j)
  calc stdRefl r (stdRefl r x) = stdRefl r x - (r ⬝ᵥ stdRefl r x) • r := rfl
    _ = stdRefl r x - (-(r ⬝ᵥ x)) • r := by rw [hd]
    _ = (x - (r ⬝ᵥ x) • r) - (-(r ⬝ᵥ x)) • r := by rw [stdRefl]
    _ = (x - (r ⬝ᵥ x) • r) - -((r ⬝ᵥ x) • r) := by rw [hneg]
    _ = x := by abel

variable {B : LinearMap.BilinForm (ZMod 3) V} {f : Fin 5 → V}

theorem frame_linearIndependent
    (hf : ∀ i j, B (f i) (f j) = if i = j then 1 else 0) : LinearIndependent (ZMod 3) f := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have h := congrArg (B (f j)) hc
  simp only [map_zero, map_sum, map_smul, smul_eq_mul] at h
  have h2 : ∑ i, c i * B (f j) (f i) = c j := by
    rw [Finset.sum_eq_single j]
    · rw [hf j j, if_pos rfl, mul_one]
    · intro b _ hbj
      rw [hf j b, if_neg (Ne.symm hbj), mul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  rwa [h2] at h

theorem frame_span_eq_top (hV : Nat.card V = 3 ^ 5)
    (hf : ∀ i j, B (f i) (f j) = if i = j then 1 else 0) :
    Submodule.span (ZMod 3) (Set.range f) = ⊤ :=
  LinearIndependent.span_eq_top_of_card_eq_finrank (frame_linearIndependent hf)
    (by rw [Fintype.card_fin, finrank_eq_five hV])

theorem eq_sum_frame (hV : Nat.card V = 3 ^ 5) {f : Fin 5 → V}
    (hf : ∀ i j, B (f i) (f j) = if i = j then 1 else 0) (u : V) :
    u = ∑ i, B u (f i) • f i := by
  classical
  have hli := frame_linearIndependent hf
  let b : Basis (Fin 5) (ZMod 3) V :=
    basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, finrank_eq_five hV])
  have hb : ⇑b = f := coe_basisOfLinearIndependentOfCardEqFinrank hli _
  have hu : u = ∑ i, b.repr u i • f i := by
    conv_lhs => rw [← b.sum_repr u]
    exact Finset.sum_congr rfl fun i _ => by rw [hb]
  have hrepr : ∀ i, B u (f i) = b.repr u i := by
    intro i
    have hφ : B.flip (f i) = b.coord i := by
      refine LinearMap.ext_on_range (frame_span_eq_top hV hf) ?_
      intro j
      rw [LinearMap.BilinForm.flip_apply, hf j i, b.coord_apply, ← hb]
      rw [Module.Basis.repr_self_apply]
    calc B u (f i) = B.flip (f i) u := by rw [LinearMap.BilinForm.flip_apply]
      _ = b.coord i u := by rw [hφ]
      _ = b.repr u i := b.coord_apply i u
  conv_lhs => rw [hu]
  exact Finset.sum_congr rfl fun i _ => by rw [← hrepr i]

theorem apply_eq_sum_frame (hV : Nat.card V = 3 ^ 5) {f : Fin 5 → V}
    (hf : ∀ i j, B (f i) (f j) = if i = j then 1 else 0) (u v : V) :
    B u v = ∑ i, B u (f i) * B v (f i) := by
  conv_lhs => rw [eq_sum_frame hV hf v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

@[expose] noncomputable def frameCoord (hV : Nat.card V = 3 ^ 5) {f : Fin 5 → V}
    (hf : ∀ i j, B (f i) (f j) = if i = j then 1 else 0) : V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3) where
  toFun u i := B u (f i)
  map_add' u v := by
    funext i
    simp only [map_add, LinearMap.add_apply, Pi.add_apply]
  map_smul' a u := by
    funext i
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Pi.smul_apply, RingHom.id_apply]
  invFun c := ∑ i, c i • f i
  left_inv u := (eq_sum_frame hV hf u).symm
  right_inv c := by
    funext i
    simp [map_sum, hf]

theorem frameCoord_apply (hV : Nat.card V = 3 ^ 5) {f : Fin 5 → V}
    (hf : ∀ i j, B (f i) (f j) = if i = j then 1 else 0) (u : V) (i : Fin 5) :
    frameCoord hV hf u i = B u (f i) := rfl

theorem frameCoord_form (hV : Nat.card V = 3 ^ 5) {f : Fin 5 → V}
    (hf : ∀ i j, B (f i) (f j) = if i = j then 1 else 0) (u v : V) :
    B u v = frameCoord hV hf u ⬝ᵥ frameCoord hV hf v := by
  rw [apply_eq_sum_frame hV hf u v]
  rfl

theorem frameCoord_frame (hV : Nat.card V = 3 ^ 5) {f : Fin 5 → V}
    (hf : ∀ i j, B (f i) (f j) = if i = j then 1 else 0) (i : Fin 5) :
    frameCoord hV hf (f i) = Pi.single i 1 := by
  funext j
  rw [frameCoord_apply, hf, Pi.single_apply]
  by_cases hij : i = j
  · rw [if_pos hij, if_pos hij.symm]
  · rw [if_neg hij, if_neg (Ne.symm hij)]

theorem frameCoord_rootRefl (hV : Nat.card V = 3 ^ 5) {f : Fin 5 → V}
    (hf : ∀ i j, B (f i) (f j) = if i = j then 1 else 0) {v : V} (hv : B v v = 2) (u : V) :
    frameCoord hV hf (rootRefl (B := B) v hv u) =
      frameCoord hV hf u - (frameCoord hV hf v ⬝ᵥ frameCoord hV hf u) • frameCoord hV hf v := by
  rw [rootRefl_apply, map_sub, map_smul, ← frameCoord_form hV hf v u]
  rfl

end CFSG.StandardType.E6QTwo

end
