module

public import CFSG.Timmesfeld.Exceptional.CosetWalk
public import CFSG.Timmesfeld.Bridge.RootClosureCoxA3
public import CFSG.Timmesfeld.Bridge.RootClosureCoxD4
public import CFSG.Timmesfeld.Bridge.RootClosureCoxB3
public import CFSG.Timmesfeld.Bridge.RootClosureCoxS4
public import CFSG.Timmesfeld.Bridge.RootClosureCoxQ2
public import CFSG.Certificates.WordPresentation
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.Timmesfeld.Bridge.RootClosure

open CFSG.Certificates CFSG.Certificates.CosetEnumeration

variable {G : Type*} [Group G]

namespace Cox

@[expose] def relsA3 : List (List (Fin 3 × Bool)) :=
  [[(0, true), (0, true)], [(1, true), (1, true)], [(2, true), (2, true)],
    (List.replicate 2 [(0, true), (1, true)]).flatten,
    (List.replicate 3 [(0, true), (2, true)]).flatten,
    (List.replicate 3 [(1, true), (2, true)]).flatten]

@[expose] def wA3₁ : List (Fin 3 × Bool) :=
  [(2, true), (0, true), (1, true), (2, true), (0, true), (2, true), (1, true), (0, true),
    (2, true), (1, true)]

@[expose] def wA3₂ : List (Fin 3 × Bool) :=
  (List.replicate 4 [(2, true), (0, true), (1, true)]).flatten

@[expose] def relsD4 : List (List (Fin 4 × Bool)) :=
  [[(0, true), (0, true)], [(1, true), (1, true)], [(2, true), (2, true)],
    [(3, true), (3, true)],
    (List.replicate 2 [(0, true), (1, true)]).flatten,
    (List.replicate 2 [(0, true), (2, true)]).flatten,
    (List.replicate 2 [(1, true), (2, true)]).flatten,
    (List.replicate 3 [(0, true), (3, true)]).flatten,
    (List.replicate 3 [(1, true), (3, true)]).flatten,
    (List.replicate 3 [(2, true), (3, true)]).flatten]

@[expose] def zD4 : List (Fin 4 × Bool) :=
  [(0, true), (1, true), (2, true), (3, true), (0, true), (1, true), (3, true), (2, true),
    (3, true), (1, true), (0, true), (3, true)]

@[expose] def wD4 : List (Fin 4 × Bool) := zD4 ++ [(3, true)] ++ zD4.reverse ++ [(3, true)]

@[expose] def relsB3 : List (List (Fin 3 × Bool)) :=
  [[(0, true), (0, true)], [(1, true), (1, true)], [(2, true), (2, true)],
    (List.replicate 2 [(0, true), (2, true)]).flatten,
    (List.replicate 3 [(0, true), (1, true)]).flatten,
    (List.replicate 4 [(1, true), (2, true)]).flatten]

@[expose] def wB3 : List (Fin 3 × Bool) :=
  (List.replicate 6 [(1, true), (0, true), (2, true)]).flatten

@[expose] def relsE (k : ℕ) : List (List (Fin 3 × Bool)) :=
  [[(0, true), (0, true)], [(1, true), (1, true)], [(2, true), (2, true)],
    (List.replicate 4 [(0, true), (1, true)]).flatten,
    (List.replicate 3 [(1, true), (2, true)]).flatten,
    (List.replicate 2 [(0, true), (2, true)]).flatten,
    (List.replicate k [(1, true), (0, true), (2, true)]).flatten]

@[expose] def wS4 : List (Fin 3 × Bool) :=
  [(2, true), (1, true), (0, true), (1, true), (2, true), (1, true), (0, true), (1, true),
    (0, true)]

@[expose] def wQ2 : List (Fin 3 × Bool) := [(1, true), (2, true)]

theorem mk_eq_one_A3 (w : List (Fin 3 × Bool))
    (hwalk : Moufang.Exc.coverWalk (2 * 3) CoxA3.fx CoxA3.fy CoxA3.ffi 0 (w.map letterCode) =
      0) :
    PresentedGroup.mk (wordRels relsA3) (FreeGroup.mk w) = 1 :=
  Moufang.Exc.mk_eq_one_of_coverWalk (N := 24) (F := 72) (fx := CoxA3.fx) (fc := CoxA3.fc)
    (fy := CoxA3.fy) (kind := CoxA3.kind) (wi := CoxA3.wi) (fs := CoxA3.fs) (ft := CoxA3.ft)
    (fo := CoxA3.fo) (refs := CoxA3.refs) (pl := CoxA3.pl) (ffi := CoxA3.ffi)
    (live := CoxA3.live) (rels := wordRels relsA3) relsA3 CoxA3.words
    (fun w hw => ⟨w, hw, rfl⟩) (by decide +kernel) CoxA3.live_zero (by norm_num)
    CoxA3.facts_all CoxA3.cover_all w hwalk

theorem mk_eq_one_D4 (w : List (Fin 4 × Bool))
    (hwalk : Moufang.Exc.coverWalk (2 * 4) CoxD4.fx CoxD4.fy CoxD4.ffi 0 (w.map letterCode) =
      0) :
    PresentedGroup.mk (wordRels relsD4) (FreeGroup.mk w) = 1 :=
  Moufang.Exc.mk_eq_one_of_coverWalk (N := 192) (F := 768) (fx := CoxD4.fx) (fc := CoxD4.fc)
    (fy := CoxD4.fy) (kind := CoxD4.kind) (wi := CoxD4.wi) (fs := CoxD4.fs) (ft := CoxD4.ft)
    (fo := CoxD4.fo) (refs := CoxD4.refs) (pl := CoxD4.pl) (ffi := CoxD4.ffi)
    (live := CoxD4.live) (rels := wordRels relsD4) relsD4 CoxD4.words
    (fun w hw => ⟨w, hw, rfl⟩) (by decide +kernel) CoxD4.live_zero (by norm_num)
    CoxD4.facts_all CoxD4.cover_all w hwalk

theorem mk_eq_one_B3 (w : List (Fin 3 × Bool))
    (hwalk : Moufang.Exc.coverWalk (2 * 3) CoxB3.fx CoxB3.fy CoxB3.ffi 0 (w.map letterCode) =
      0) :
    PresentedGroup.mk (wordRels relsB3) (FreeGroup.mk w) = 1 :=
  Moufang.Exc.mk_eq_one_of_coverWalk (N := 48) (F := 144) (fx := CoxB3.fx) (fc := CoxB3.fc)
    (fy := CoxB3.fy) (kind := CoxB3.kind) (wi := CoxB3.wi) (fs := CoxB3.fs) (ft := CoxB3.ft)
    (fo := CoxB3.fo) (refs := CoxB3.refs) (pl := CoxB3.pl) (ffi := CoxB3.ffi)
    (live := CoxB3.live) (rels := wordRels relsB3) relsB3 CoxB3.words
    (fun w hw => ⟨w, hw, rfl⟩) (by decide +kernel) CoxB3.live_zero (by norm_num)
    CoxB3.facts_all CoxB3.cover_all w hwalk

theorem mk_eq_one_S4 (w : List (Fin 3 × Bool))
    (hwalk : Moufang.Exc.coverWalk (2 * 3) CoxS4.fx CoxS4.fy CoxS4.ffi 0 (w.map letterCode) =
      0) :
    PresentedGroup.mk (wordRels (relsE 3)) (FreeGroup.mk w) = 1 :=
  Moufang.Exc.mk_eq_one_of_coverWalk (N := 24) (F := 72) (fx := CoxS4.fx) (fc := CoxS4.fc)
    (fy := CoxS4.fy) (kind := CoxS4.kind) (wi := CoxS4.wi) (fs := CoxS4.fs) (ft := CoxS4.ft)
    (fo := CoxS4.fo) (refs := CoxS4.refs) (pl := CoxS4.pl) (ffi := CoxS4.ffi)
    (live := CoxS4.live) (rels := wordRels (relsE 3)) (relsE 3) CoxS4.words
    (fun w hw => ⟨w, hw, rfl⟩) (by decide +kernel) CoxS4.live_zero (by norm_num)
    CoxS4.facts_all CoxS4.cover_all w hwalk

theorem mk_eq_one_Q2 (w : List (Fin 3 × Bool))
    (hwalk : Moufang.Exc.coverWalk (2 * 3) CoxQ2.fx CoxQ2.fy CoxQ2.ffi 0 (w.map letterCode) =
      0) :
    PresentedGroup.mk (wordRels (relsE 2)) (FreeGroup.mk w) = 1 :=
  Moufang.Exc.mk_eq_one_of_coverWalk (N := 11) (F := 43) (fx := CoxQ2.fx) (fc := CoxQ2.fc)
    (fy := CoxQ2.fy) (kind := CoxQ2.kind) (wi := CoxQ2.wi) (fs := CoxQ2.fs) (ft := CoxQ2.ft)
    (fo := CoxQ2.fo) (refs := CoxQ2.refs) (pl := CoxQ2.pl) (ffi := CoxQ2.ffi)
    (live := CoxQ2.live) (rels := wordRels (relsE 2)) (relsE 2) CoxQ2.words
    (fun w hw => ⟨w, hw, rfl⟩) (by decide +kernel) CoxQ2.live_zero (by norm_num)
    CoxQ2.facts_all CoxQ2.cover_all w hwalk

theorem mk_wA3₁ : PresentedGroup.mk (wordRels relsA3) (FreeGroup.mk wA3₁) = 1 :=
  mk_eq_one_A3 _ (by decide +kernel)

theorem mk_wA3₂ : PresentedGroup.mk (wordRels relsA3) (FreeGroup.mk wA3₂) = 1 :=
  mk_eq_one_A3 _ (by decide +kernel)

theorem mk_wD4 : PresentedGroup.mk (wordRels relsD4) (FreeGroup.mk wD4) = 1 :=
  mk_eq_one_D4 _ (by decide +kernel)

theorem mk_wB3 : PresentedGroup.mk (wordRels relsB3) (FreeGroup.mk wB3) = 1 :=
  mk_eq_one_B3 _ (by decide +kernel)

theorem mk_wS4 : PresentedGroup.mk (wordRels (relsE 3)) (FreeGroup.mk wS4) = 1 :=
  mk_eq_one_S4 _ (by decide +kernel)

theorem mk_wQ2 : PresentedGroup.mk (wordRels (relsE 2)) (FreeGroup.mk wQ2) = 1 :=
  mk_eq_one_Q2 _ (by decide +kernel)

end Cox

open Cox

private theorem sq_mul_eq_one {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hab : Commute a b) :
    (a * b) ^ 2 = 1 := by
  rw [hab.mul_pow, sq, sq, ha, hb, one_mul]

theorem conj_eq_of_a3 {u v y : G} (hu : u * u = 1) (hv : v * v = 1) (hy : y * y = 1)
    (huv : Commute u v) (huy : (u * y) ^ 3 = 1) (hvy : (v * y) ^ 3 = 1) :
    (y * u * v * y) * u * (y * u * v * y)⁻¹ = v ∧ (y * u * v) ^ 4 = 1 := by
  set x : Fin 3 → G := ![u, v, y] with hx
  have hrel : ∀ r ∈ relsA3, signedProd x r = 1 := by
    intro r hr
    simp only [relsA3, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [signedProd, hx] using hu
    · simpa [signedProd, hx] using hv
    · simpa [signedProd, hx] using hy
    · rw [signedProd_replicate]; simpa [signedProd, hx] using sq_mul_eq_one hu hv huv
    · rw [signedProd_replicate]; simpa [signedProd, hx] using huy
    · rw [signedProd_replicate]; simpa [signedProd, hx] using hvy
  have k1 : signedProd x wA3₁ = 1 := by
    rw [← wordsHom_signedProd relsA3 x hrel, signedProd_of, mk_wA3₁, map_one]
  have k2 : signedProd x wA3₂ = 1 := by
    rw [← wordsHom_signedProd relsA3 x hrel, signedProd_of, mk_wA3₂, map_one]
  have hinv : (y * u * v * y)⁻¹ = y * v * u * y := by
    simp only [mul_inv_rev, inv_eq_of_mul_eq_one_right hu, inv_eq_of_mul_eq_one_right hv,
      inv_eq_of_mul_eq_one_right hy, mul_assoc]
  refine ⟨?_, ?_⟩
  · have e : y * u * v * y * u * (y * v * u * y) * v = 1 := by
      simpa [signedProd, wA3₁, hx, mul_assoc] using k1
    rw [hinv]
    have e' := eq_inv_of_mul_eq_one_left e
    rwa [inv_eq_of_mul_eq_one_right hv] at e'
  · simp only [wA3₂, signedProd_replicate] at k2
    simpa [signedProd, hx, mul_assoc] using k2

theorem commute_of_d4 {u v w y : G} (hu : u * u = 1) (hv : v * v = 1) (hw : w * w = 1)
    (hy : y * y = 1) (huv : Commute u v) (huw : Commute u w) (hvw : Commute v w)
    (huy : (u * y) ^ 3 = 1) (hvy : (v * y) ^ 3 = 1) (hwy : (w * y) ^ 3 = 1) :
    Commute (u * v * w * ((y * u * v * y) * w * (y * u * v * y)⁻¹)) y := by
  set x : Fin 4 → G := ![u, v, w, y] with hx
  have hrel : ∀ r ∈ relsD4, signedProd x r = 1 := by
    intro r hr
    simp only [relsD4, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [signedProd, hx] using hu
    · simpa [signedProd, hx] using hv
    · simpa [signedProd, hx] using hw
    · simpa [signedProd, hx] using hy
    · rw [signedProd_replicate]; simpa [signedProd, hx] using sq_mul_eq_one hu hv huv
    · rw [signedProd_replicate]; simpa [signedProd, hx] using sq_mul_eq_one hu hw huw
    · rw [signedProd_replicate]; simpa [signedProd, hx] using sq_mul_eq_one hv hw hvw
    · rw [signedProd_replicate]; simpa [signedProd, hx] using huy
    · rw [signedProd_replicate]; simpa [signedProd, hx] using hvy
    · rw [signedProd_replicate]; simpa [signedProd, hx] using hwy
  have k : signedProd x wD4 = 1 := by
    rw [← wordsHom_signedProd relsD4 x hrel, signedProd_of, mk_wD4, map_one]
  have hinv : (y * u * v * y)⁻¹ = y * v * u * y := by
    simp only [mul_inv_rev, inv_eq_of_mul_eq_one_right hu, inv_eq_of_mul_eq_one_right hv,
      inv_eq_of_mul_eq_one_right hy, mul_assoc]
  set z := u * v * w * ((y * u * v * y) * w * (y * u * v * y)⁻¹) with hz
  have hzinv : z⁻¹ = y * u * v * y * w * y * v * u * y * w * v * u := by
    rw [hz, hinv]
    simp only [mul_inv_rev, inv_eq_of_mul_eq_one_right hu, inv_eq_of_mul_eq_one_right hv,
      inv_eq_of_mul_eq_one_right hw, inv_eq_of_mul_eq_one_right hy, mul_assoc]
  have e : z * y * z⁻¹ * y = 1 := by
    rw [hzinv, hz, hinv]
    simpa [signedProd, wD4, zD4, hx, mul_assoc] using k
  have e' : z * y * z⁻¹ = y := by
    rw [eq_inv_of_mul_eq_one_left e, inv_eq_of_mul_eq_one_right hy]
  show z * y = y * z
  calc z * y = z * y * z⁻¹ * z := by group
    _ = y * z := by rw [e']

theorem pow_six_of_b3 {a y c : G} (ha : a * a = 1) (hy : y * y = 1) (hc : c * c = 1)
    (hac : Commute a c) (hay : (a * y) ^ 3 = 1) (hyc : (y * c) ^ 4 = 1) :
    (y * a * c) ^ 6 = 1 := by
  set x : Fin 3 → G := ![a, y, c] with hx
  have hrel : ∀ r ∈ relsB3, signedProd x r = 1 := by
    intro r hr
    simp only [relsB3, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [signedProd, hx] using ha
    · simpa [signedProd, hx] using hy
    · simpa [signedProd, hx] using hc
    · rw [signedProd_replicate]; simpa [signedProd, hx] using sq_mul_eq_one ha hc hac
    · rw [signedProd_replicate]; simpa [signedProd, hx] using hay
    · rw [signedProd_replicate]; simpa [signedProd, hx] using hyc
  have k : signedProd x wB3 = 1 := by
    rw [← wordsHom_signedProd relsB3 x hrel, signedProd_of, mk_wB3, map_one]
  simp only [wB3, signedProd_replicate] at k
  simpa [signedProd, hx, mul_assoc] using k

private theorem relsE_hold {e a y : G} (he : e * e = 1) (ha : a * a = 1) (hy : y * y = 1)
    (hea : (e * a) ^ 4 = 1) (hay : (a * y) ^ 3 = 1) (hey : Commute e y) {k : ℕ}
    (haey : (a * e * y) ^ k = 1) : ∀ r ∈ relsE k, signedProd ![e, a, y] r = 1 := by
  intro r hr
  simp only [relsE, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [signedProd] using he
  · simpa [signedProd] using ha
  · simpa [signedProd] using hy
  · rw [signedProd_replicate]; simpa [signedProd] using hea
  · rw [signedProd_replicate]; simpa [signedProd] using hay
  · rw [signedProd_replicate]; simpa [signedProd] using sq_mul_eq_one he hy hey
  · rw [signedProd_replicate]; simpa [signedProd, mul_assoc] using haey

theorem conj_eq_of_s4 {e a y : G} (he : e * e = 1) (ha : a * a = 1) (hy : y * y = 1)
    (hea : (e * a) ^ 4 = 1) (hay : (a * y) ^ 3 = 1) (hey : Commute e y)
    (haey : (a * e * y) ^ 3 = 1) : y * (a * e * a) * y = e * (a * e * a) := by
  have k : signedProd ![e, a, y] wS4 = 1 := by
    rw [← wordsHom_signedProd (relsE 3) ![e, a, y]
      (relsE_hold he ha hy hea hay hey haey), signedProd_of, mk_wS4, map_one]
  have e₁ : y * (a * e * a) * y * (a * e * a * e) = 1 := by
    simpa [signedProd, wS4, mul_assoc] using k
  have hinv : (a * e * a * e)⁻¹ = e * (a * e * a) := by
    simp only [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right he,
      mul_assoc]
  rw [← hinv]
  exact eq_inv_of_mul_eq_one_left e₁

theorem eq_of_q2 {e a y : G} (he : e * e = 1) (ha : a * a = 1) (hy : y * y = 1)
    (hea : (e * a) ^ 4 = 1) (hay : (a * y) ^ 3 = 1) (hey : Commute e y)
    (haey : (a * e * y) ^ 2 = 1) : a = y := by
  have k : signedProd ![e, a, y] wQ2 = 1 := by
    rw [← wordsHom_signedProd (relsE 2) ![e, a, y]
      (relsE_hold he ha hy hea hay hey haey), signedProd_of, mk_wQ2, map_one]
  have e₁ : a * y = 1 := by simpa [signedProd, wQ2] using k
  rw [eq_inv_of_mul_eq_one_left e₁, inv_eq_of_mul_eq_one_right hy]

end CFSG.Timmesfeld.Bridge.RootClosure
