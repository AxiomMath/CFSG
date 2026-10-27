module

public import CFSG.Timmesfeld.Exceptional.CosetWalk
public import CFSG.Timmesfeld.Exceptional.L211Check
public import CFSG.Certificates.WordPresentation
public import CFSG.Timmesfeld.Basic
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.Timmesfeld.Moufang

open CFSG.Certificates CFSG.Certificates.CosetEnumeration

variable {G : Type*} [Group G]

namespace Exc

@[expose] def rels555 : List (List (Fin 3 × Bool)) :=
  [[(0, true), (0, true)], [(1, true), (1, true)], [(2, true), (2, true)],
    [(0, true), (1, true), (0, true), (1, true)],
    (List.replicate 5 [(0, true), (2, true)]).flatten,
    (List.replicate 5 [(1, true), (2, true)]).flatten,
    (List.replicate 5 [(0, true), (1, true), (2, true)]).flatten]

@[expose] def invWord {m : ℕ} (w : List (Fin m × Bool)) : List (Fin m × Bool) :=
  w.reverse.map fun l => (l.1, !l.2)

theorem signedProd_invWord {m : ℕ} (x : Fin m → G) (w : List (Fin m × Bool)) :
    signedProd x (invWord w) = (signedProd x w)⁻¹ := by
  induction w with
  | nil => simp [invWord]
  | cons l w ih =>
    rw [invWord, List.reverse_cons, List.map_append, signedProd_append, ← invWord, ih,
      signedProd_cons, mul_inv_rev]
    obtain ⟨i, b⟩ := l
    cases b <;> simp [signedProd]

theorem signedProd_eq_one_of_mk_eq_one {m : ℕ} {ws : List (List (Fin m × Bool))}
    {w : List (Fin m × Bool)} (hw : PresentedGroup.mk (wordRels ws) (FreeGroup.mk w) = 1)
    (x : Fin m → G) (hx : ∀ r ∈ ws, signedProd x r = 1) : signedProd x w = 1 := by
  rw [← wordsHom_signedProd ws x hx w, signedProd_of, hw, map_one]

@[expose] def wY : List (Fin 3 × Bool) := [(0, true), (2, true), (1, true), (2, true)]

@[expose] def wG : List (Fin 3 × Bool) :=
  wY ++ wY ++ [(0, true), (2, true), (0, true), (2, true), (0, true), (2, true)] ++
    [(1, true), (2, true), (0, false), (2, false), (1, false), (2, true), (0, true), (2, true)]

@[expose] def wA : List (Fin 3 × Bool) :=
  [(0, true), (2, true), (0, true), (2, true)] ++
    [(1, true), (2, true), (0, false), (2, false), (1, false), (2, true), (0, true), (2, true)]

@[expose] def wB : List (Fin 3 × Bool) := [(0, true), (2, true), (1, true)]

theorem mk_eq_one_555 (w : List (Fin 3 × Bool))
    (hwalk : Exc.coverWalk (2 * 3) L211Data.fx L211Data.fy L211Data.ffi 0 (w.map letterCode) = 0) :
    PresentedGroup.mk (wordRels rels555) (FreeGroup.mk w) = 1 :=
  mk_eq_one_of_coverWalk (N := 660) (F := 1980) (fx := L211Data.fx) (fc := L211Data.fc)
    (fy := L211Data.fy) (kind := L211Data.kind) (wi := L211Data.wi) (fs := L211Data.fs)
    (ft := L211Data.ft) (fo := L211Data.fo) (refs := L211Data.refs) (pl := L211Data.pl)
    (ffi := L211Data.ffi) (live := L211Data.live) (rels := wordRels rels555) rels555 L211Data.words
    (fun w hw => ⟨w, hw, rfl⟩) (by decide +kernel) L211Data.live_zero (by norm_num)
    L211Data.facts_all L211Data.cover_all w hwalk

theorem mk_pow_six : PresentedGroup.mk (wordRels rels555)
    (FreeGroup.mk (wY ++ wY ++ wY ++ wY ++ wY ++ wY)) = 1 :=
  mk_eq_one_555 _ (by decide +kernel)

theorem mk_conj_cube : PresentedGroup.mk (wordRels rels555)
    (FreeGroup.mk (invWord wG ++ (wY ++ wY ++ wY) ++ wG ++ [(0, false)])) = 1 :=
  mk_eq_one_555 _ (by decide +kernel)

theorem mk_conj_sq : PresentedGroup.mk (wordRels rels555)
    (FreeGroup.mk (wA ++ (wY ++ wY) ++ invWord wA ++ wB ++ (wY ++ wY) ++ invWord wB ++
      [(0, false)])) = 1 :=
  mk_eq_one_555 _ (by decide +kernel)

end Exc

open Exc

theorem false_of_orderOf_five_five_five {D : Set G} (hD : IsRootInvolutionSet D)
    (hconj : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D) {u v c : G} (hu : u ∈ D) (hv : v ∈ D)
    (hc : c ∈ D) (huv : Commute u v) (h1 : orderOf (u * c) = 5) (h2 : orderOf (v * c) = 5)
    (h3 : orderOf (u * v * c) = 5) : False := by
  have hu2 := hD.mul_self_eq_one hu
  have hv2 := hD.mul_self_eq_one hv
  have hc2 := hD.mul_self_eq_one hc
  set x : Fin 3 → G := ![u, v, c] with hx
  have hrel : ∀ r ∈ rels555, signedProd x r = 1 := by
    intro r hr
    simp only [rels555, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [signedProd, hx] using hu2
    · simpa [signedProd, hx] using hv2
    · simpa [signedProd, hx] using hc2
    · simp only [signedProd, hx, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, ite_true]
      rw [show u * (v * (u * v)) = u * (v * u) * v by group, ← huv.eq,
        show u * (u * v) * v = u * u * (v * v) by group, hu2, hv2, one_mul]
    · rw [signedProd_replicate, ← h1]
      simp [signedProd, hx]
    · rw [signedProd_replicate, ← h2]
      simp [signedProd, hx]
    · rw [signedProd_replicate, ← h3]
      simp [signedProd, hx, mul_assoc]
  have hY : signedProd x wY = u * (c * v * c) := by
    simp [signedProd, wY, hx, mul_assoc]
  set y := u * (c * v * c) with hy
  have k6 := signedProd_eq_one_of_mk_eq_one mk_pow_six x hrel
  have k3 := signedProd_eq_one_of_mk_eq_one mk_conj_cube x hrel
  have k2 := signedProd_eq_one_of_mk_eq_one mk_conj_sq x hrel
  simp only [signedProd_append, signedProd_invWord, hY] at k6 k3 k2
  have hux : signedProd x [(0, false)] = u⁻¹ := by simp [signedProd, hx]
  rw [hux] at k3 k2
  have hy6 : y ^ 6 = 1 := by
    rw [show (6 : ℕ) = 1 + 1 + 1 + 1 + 1 + 1 from rfl]
    simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using k6
  have hu1 : u ≠ 1 := hD.ne_one hu
  have hcvc : c * v * c ∈ D := by
    have := hconj c v hv
    rwa [hD.inv_eq hc] at this
  have hdvd : orderOf y ∣ 6 := orderOf_dvd_of_pow_eq_one hy6
  rcases hD.orderOf_mul hu hcvc with ho | ho | ho
  ·
    have hy2 : y * y = 1 := by rw [← pow_two, ← ho]; exact pow_orderOf_eq_one y
    have hyy : ∀ z : G, y * (y * z) = z := fun z => by rw [← mul_assoc, hy2, one_mul]
    apply hu1
    have e := k2
    simp only [mul_assoc, hyy, mul_inv_cancel_left] at e
    exact inv_eq_one.mp e
  · rw [ho] at hdvd
    exact absurd hdvd (by norm_num)
  ·
    have h3d : orderOf y ∣ 3 :=
      (Nat.Coprime.dvd_of_dvd_mul_left ((Nat.coprime_two_right).2 ho)
        (by simpa [show (6 : ℕ) = 2 * 3 from rfl] using hdvd))
    have hy3 : y * (y * y) = 1 := by
      rw [← mul_assoc, ← pow_two, ← pow_succ]; exact orderOf_dvd_iff_pow_eq_one.1 h3d
    have hyyy : ∀ z : G, y * (y * (y * z)) = z := fun z => by
      rw [← mul_assoc, ← mul_assoc, mul_assoc y, hy3, one_mul]
    apply hu1
    have e := k3
    simp only [mul_assoc, hyyy, inv_mul_cancel_left] at e
    exact inv_eq_one.mp e

end CFSG.Timmesfeld.Moufang
