module

public import CFSG.Timmesfeld.Exceptional.CosetWalk
public import CFSG.Timmesfeld.Bridge.RootStructW96CheckA
public import CFSG.Timmesfeld.Bridge.RootStructW96CheckB
public import CFSG.Certificates.WordPresentation
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Certificates CFSG.Certificates.CosetEnumeration

variable {G : Type*} [Group G]

namespace WStarD4

@[expose] def relsA : List (List (Fin 4 × Bool)) :=
  [[(0, true), (0, true)], [(1, true), (1, true)], [(2, true), (2, true)],
    [(3, true), (3, true)],
    (List.replicate 3 [(0, true), (1, true)]).flatten,
    (List.replicate 4 [(1, true), (2, true)]).flatten,
    (List.replicate 4 [(1, true), (3, true)]).flatten,
    (List.replicate 2 [(0, true), (2, true)]).flatten,
    (List.replicate 2 [(0, true), (3, true)]).flatten,
    (List.replicate 2 [(2, true), (3, true)]).flatten,
    (List.replicate 3 [(1, true), (0, true), (3, true)]).flatten,
    (List.replicate 3 [(1, true), (2, true), (0, true)]).flatten,
    (List.replicate 3 [(1, true), (2, true), (0, true), (3, true)]).flatten]

@[expose] def relsB : List (List (Fin 4 × Bool)) :=
  [[(0, true), (0, true)], [(1, true), (1, true)], [(2, true), (2, true)],
    [(3, true), (3, true)],
    (List.replicate 3 [(0, true), (1, true)]).flatten,
    (List.replicate 3 [(1, true), (2, true)]).flatten,
    (List.replicate 4 [(1, true), (3, true)]).flatten,
    (List.replicate 2 [(0, true), (2, true)]).flatten,
    (List.replicate 2 [(0, true), (3, true)]).flatten,
    (List.replicate 2 [(2, true), (3, true)]).flatten,
    (List.replicate 3 [(1, true), (0, true), (3, true)]).flatten,
    (List.replicate 3 [(1, true), (2, true), (3, true)]).flatten]

@[expose] def wA₁ : List (Fin 4 × Bool) :=
  [(1, true), (2, true), (1, true), (3, true), (1, true), (2, true), (1, true), (3, true)]

@[expose] def wA₂ : List (Fin 4 × Bool) :=
  [(1, true), (2, true), (1, true), (0, true), (1, true), (2, true), (1, true), (2, true),
    (0, true)]

@[expose] def wB₁ : List (Fin 4 × Bool) :=
  [(1, true), (0, true), (2, true), (1, true), (3, true), (1, true), (2, true), (0, true),
    (1, true), (3, true)]

@[expose] def wB₂ : List (Fin 4 × Bool) :=
  [(1, true), (0, true), (2, true), (1, true), (0, true), (1, true), (2, true), (0, true),
    (1, true), (2, true)]

theorem mk_eq_one_A (w : List (Fin 4 × Bool))
    (hwalk : Moufang.Exc.coverWalk (2 * 4) DataA.fx DataA.fy DataA.ffi 0 (w.map letterCode) =
      0) :
    PresentedGroup.mk (wordRels relsA) (FreeGroup.mk w) = 1 :=
  Moufang.Exc.mk_eq_one_of_coverWalk (N := 98) (F := 390) (fx := DataA.fx) (fc := DataA.fc)
    (fy := DataA.fy) (kind := DataA.kind) (wi := DataA.wi) (fs := DataA.fs) (ft := DataA.ft)
    (fo := DataA.fo) (refs := DataA.refs) (pl := DataA.pl) (ffi := DataA.ffi)
    (live := DataA.live) (rels := wordRels relsA) relsA DataA.words (fun w hw => ⟨w, hw, rfl⟩)
    (by decide +kernel) DataA.live_zero (by norm_num) DataA.facts_all DataA.cover_all w hwalk

theorem mk_eq_one_B (w : List (Fin 4 × Bool))
    (hwalk : Moufang.Exc.coverWalk (2 * 4) DataB.fx DataB.fy DataB.ffi 0 (w.map letterCode) =
      0) :
    PresentedGroup.mk (wordRels relsB) (FreeGroup.mk w) = 1 :=
  Moufang.Exc.mk_eq_one_of_coverWalk (N := 96) (F := 384) (fx := DataB.fx) (fc := DataB.fc)
    (fy := DataB.fy) (kind := DataB.kind) (wi := DataB.wi) (fs := DataB.fs) (ft := DataB.ft)
    (fo := DataB.fo) (refs := DataB.refs) (pl := DataB.pl) (ffi := DataB.ffi)
    (live := DataB.live) (rels := wordRels relsB) relsB DataB.words (fun w hw => ⟨w, hw, rfl⟩)
    (by decide +kernel) DataB.live_zero (by norm_num) DataB.facts_all DataB.cover_all w hwalk

theorem mk_wA₁ : PresentedGroup.mk (wordRels relsA) (FreeGroup.mk wA₁) = 1 :=
  mk_eq_one_A _ (by decide +kernel)

theorem mk_wA₂ : PresentedGroup.mk (wordRels relsA) (FreeGroup.mk wA₂) = 1 :=
  mk_eq_one_A _ (by decide +kernel)

theorem mk_wB₁ : PresentedGroup.mk (wordRels relsB) (FreeGroup.mk wB₁) = 1 :=
  mk_eq_one_B _ (by decide +kernel)

theorem mk_wB₂ : PresentedGroup.mk (wordRels relsB) (FreeGroup.mk wB₂) = 1 :=
  mk_eq_one_B _ (by decide +kernel)

end WStarD4

open WStarD4

theorem conj_eq_mul_of_wStarD4 {p z y d : G} (hp : p * p = 1) (hz : z * z = 1) (hy : y * y = 1)
    (hd : d * d = 1) (hpz : (p * z) ^ 3 = 1) (hzy : (z * y) ^ 4 = 1) (hzd : (z * d) ^ 4 = 1)
    (hpy : Commute p y) (hpd : Commute p d) (hyd : Commute y d)
    (h1 : (z * (p * d)) ^ 3 = 1) (h2 : (z * (y * p)) ^ 3 = 1) (h3 : (z * (y * p * d)) ^ 3 = 1) :
    Commute (z * y * z) d ∧ (z * y * z) * p * (z * y * z)⁻¹ = p * y := by
  set x : Fin 4 → G := ![p, z, y, d] with hx
  have hrel : ∀ r ∈ relsA, signedProd x r = 1 := by
    intro r hr
    simp only [relsA, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [signedProd, hx] using hp
    · simpa [signedProd, hx] using hz
    · simpa [signedProd, hx] using hy
    · simpa [signedProd, hx] using hd
    · rw [signedProd_replicate]; simpa [signedProd, hx] using hpz
    · rw [signedProd_replicate]; simpa [signedProd, hx] using hzy
    · rw [signedProd_replicate]; simpa [signedProd, hx] using hzd
    · rw [signedProd_replicate]
      simpa [signedProd, hx] using (by rw [hpy.mul_pow, sq, sq, hp, hy, one_mul] :
        (p * y) ^ 2 = 1)
    · rw [signedProd_replicate]
      simpa [signedProd, hx] using (by rw [hpd.mul_pow, sq, sq, hp, hd, one_mul] :
        (p * d) ^ 2 = 1)
    · rw [signedProd_replicate]
      simpa [signedProd, hx] using (by rw [hyd.mul_pow, sq, sq, hy, hd, one_mul] :
        (y * d) ^ 2 = 1)
    · rw [signedProd_replicate]; simpa [signedProd, hx] using h1
    · rw [signedProd_replicate]; simpa [signedProd, hx] using h2
    · rw [signedProd_replicate]; simpa [signedProd, hx, mul_assoc] using h3
  have k1 : signedProd x wA₁ = 1 := by
    rw [← wordsHom_signedProd relsA x hrel, signedProd_of, mk_wA₁, map_one]
  have k2 : signedProd x wA₂ = 1 := by
    rw [← wordsHom_signedProd relsA x hrel, signedProd_of, mk_wA₂, map_one]
  have hg : (z * y * z)⁻¹ = z * y * z := by
    simp only [mul_inv_rev, inv_eq_of_mul_eq_one_right hz, inv_eq_of_mul_eq_one_right hy,
      mul_assoc]
  refine ⟨?_, ?_⟩
  · have e : z * y * z * d * (z * y * z * d) = 1 := by
      simpa [signedProd, wA₁, hx, mul_assoc] using k1
    have e' := eq_inv_of_mul_eq_one_left e
    rw [mul_inv_rev, hg, inv_eq_of_mul_eq_one_right hd] at e'
    exact e'
  · have e : z * y * z * p * (z * y * z) * (y * p) = 1 := by
      simpa [signedProd, wA₂, hx, mul_assoc] using k2
    rw [hg]
    rw [mul_eq_one_iff_eq_inv, mul_inv_rev, inv_eq_of_mul_eq_one_right hy,
      inv_eq_of_mul_eq_one_right hp] at e
    exact e

theorem conj_eq_of_wStarD4' {b z y d : G} (hb : b * b = 1) (hz : z * z = 1) (hy : y * y = 1)
    (hd : d * d = 1) (hbz : (b * z) ^ 3 = 1) (hzy : (z * y) ^ 3 = 1) (hzd : (z * d) ^ 4 = 1)
    (hby : Commute b y) (hbd : Commute b d) (hyd : Commute y d)
    (h1 : (z * (b * d)) ^ 3 = 1) (h2 : (z * (y * d)) ^ 3 = 1) :
    Commute (z * b * y * z) d ∧ (z * b * y * z) * b * (z * b * y * z)⁻¹ = y := by
  set x : Fin 4 → G := ![b, z, y, d] with hx
  have hrel : ∀ r ∈ relsB, signedProd x r = 1 := by
    intro r hr
    simp only [relsB, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [signedProd, hx] using hb
    · simpa [signedProd, hx] using hz
    · simpa [signedProd, hx] using hy
    · simpa [signedProd, hx] using hd
    · rw [signedProd_replicate]; simpa [signedProd, hx] using hbz
    · rw [signedProd_replicate]; simpa [signedProd, hx] using hzy
    · rw [signedProd_replicate]; simpa [signedProd, hx] using hzd
    · rw [signedProd_replicate]
      simpa [signedProd, hx] using (by rw [hby.mul_pow, sq, sq, hb, hy, one_mul] :
        (b * y) ^ 2 = 1)
    · rw [signedProd_replicate]
      simpa [signedProd, hx] using (by rw [hbd.mul_pow, sq, sq, hb, hd, one_mul] :
        (b * d) ^ 2 = 1)
    · rw [signedProd_replicate]
      simpa [signedProd, hx] using (by rw [hyd.mul_pow, sq, sq, hy, hd, one_mul] :
        (y * d) ^ 2 = 1)
    · rw [signedProd_replicate]; simpa [signedProd, hx] using h1
    · rw [signedProd_replicate]; simpa [signedProd, hx] using h2
  have k1 : signedProd x wB₁ = 1 := by
    rw [← wordsHom_signedProd relsB x hrel, signedProd_of, mk_wB₁, map_one]
  have k2 : signedProd x wB₂ = 1 := by
    rw [← wordsHom_signedProd relsB x hrel, signedProd_of, mk_wB₂, map_one]
  have hg : (z * b * y * z)⁻¹ = z * y * b * z := by
    simp only [mul_inv_rev, inv_eq_of_mul_eq_one_right hz, inv_eq_of_mul_eq_one_right hy,
      inv_eq_of_mul_eq_one_right hb, mul_assoc]
  refine ⟨?_, ?_⟩
  · have e : z * b * y * z * d * (z * b * y * z)⁻¹ * d = 1 := by
      rw [hg]
      simpa [signedProd, wB₁, hx, mul_assoc] using k1
    have e' := eq_inv_of_mul_eq_one_left e
    rw [inv_eq_of_mul_eq_one_right hd] at e'
    calc z * b * y * z * d
        = z * b * y * z * d * (z * b * y * z)⁻¹ * (z * b * y * z) := by group
      _ = d * (z * b * y * z) := by rw [e']
  · have e : z * b * y * z * b * (z * b * y * z)⁻¹ * y = 1 := by
      rw [hg]
      simpa [signedProd, wB₂, hx, mul_assoc] using k2
    have e' := eq_inv_of_mul_eq_one_left e
    rwa [inv_eq_of_mul_eq_one_right hy] at e'

end CFSG.Timmesfeld.Bridge
