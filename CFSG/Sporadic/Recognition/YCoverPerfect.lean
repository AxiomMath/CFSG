module

public import CFSG.Sporadic.Recognition.YCoverLift
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.Sporadic.Recognition.YCover

open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons)
open CFSG.YGroups (yRels yEdges ngen spiderWord pairExp yGen YGroup closure_yGen)

variable {p q r : ℕ}

theorem braid_of_cube {G : Type*} [Group G] {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (h : (x * y) ^ 3 = 1) : x * y * x = y * x * y := by
  have h1 : x * y * x * (y * x * y) = 1 := by
    rw [← h]; simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have h2 : (y * x * y)⁻¹ = y * x * y := by
    rw [mul_inv_rev, mul_inv_rev, inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right hy,
      mul_assoc]
  exact (eq_inv_of_mul_eq_one_left h1).trans h2

theorem conj_of_braid {G : Type*} [Group G] {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : x * y * x = y * x * y) : x * y * x * (x * y)⁻¹ = y := by
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right hy, hxy]
  calc y * x * y * (y * x) = y * x * (y * y) * x := by simp only [mul_assoc]
    _ = y := by rw [hy, mul_one, mul_assoc, hx, mul_one]

theorem isPerfect_quotY (D : FlagData p q r) {F : YGroup p q r}
    (hFdef : F = evalWord (yGen p q r) D.Fw ^ 9) : Group.IsPerfect (QuotY p q r F) := by
  set Q := QuotY p q r F with hQ
  let g : ℕ → Q := marked F (MonoidHom.id Q)
  have hrel := marked_rels F (MonoidHom.id Q)
  have hinv := marked_mul_self F (MonoidHom.id Q)
  have hedge : ∀ c, 0 < c → c < ngen p q r → (g (parentY p q c) * g c) ^ 3 = 1 := by
    intro c hc0 hc
    obtain ⟨hlt, he⟩ := D.parent_edge c hc hc0
    have h := fam_pair hrel hlt hc
    have h3 : pairExp p q r (parentY p q c) c = 3 := by simp [pairExp, he]
    rwa [h3] at h
  let ab : Q →* Abelianization Q := Abelianization.of
  have hconj : ∀ c, 0 < c → c < ngen p q r → ab (g c) = ab (g (parentY p q c)) := by
    intro c hc0 hc
    have hb := braid_of_cube (hinv _) (hinv _) (hedge c hc0 hc)
    have h2 := conj_of_braid (hinv _) (hinv _) hb
    calc ab (g c) = ab (g (parentY p q c) * g c * g (parentY p q c) *
        (g (parentY p q c) * g c)⁻¹) := by rw [h2]
      _ = ab (g (parentY p q c)) := by
        simp only [map_mul, map_inv]
        exact mul_inv_cancel_comm _ _
  have hall : ∀ c < ngen p q r, ab (g c) = ab (g 0) := by
    intro c
    induction c using Nat.strong_induction_on with
    | _ c ih =>
      intro hc
      rcases Nat.eq_zero_or_pos c with rfl | hpos
      · rfl
      · obtain ⟨hlt, -⟩ := D.parent_edge c hc hpos
        rw [hconj c hpos hc]
        exact ih _ hlt (by omega)
  have h0 : 0 < ngen p q r := by unfold ngen; omega
  set a : Abelianization Q := ab (g 0) with ha
  have ha2 : a * a = 1 := by rw [ha, ← map_mul, hinv 0, map_one]
  have hFw : ab (evalWord g D.Fw) = a ^ D.Fw.length := by
    have : ∀ w : List ℕ, (∀ c ∈ w, c < ngen p q r) → ab (evalWord g w) = a ^ w.length := by
      intro w
      induction w with
      | nil => intro _; simp [evalWord]
      | cons c w ih =>
        intro hw
        rw [evalWord_cons, map_mul, ih (fun c' hc' => hw c' (by simp [hc'])),
          hall c (hw c (by simp)), List.length_cons, pow_succ']
    exact this D.Fw D.Fw_lt
  have h9 : a ^ (D.Fw.length * 9) = 1 := by
    have := marked_F hFdef (MonoidHom.id Q)
    have h1 := congrArg ab this
    rw [map_pow, hFw, ← pow_mul, map_one] at h1
    exact h1
  have ha1 : a = 1 := by
    obtain ⟨m, hm⟩ : ∃ m, D.Fw.length * 9 = 2 * m + 1 := ⟨D.Fw.length * 9 / 2, by
      have := D.Fw_odd; omega⟩
    rw [hm, pow_succ, pow_mul, sq, ha2, one_pow, one_mul] at h9
    exact h9
  have hgens : ∀ c < ngen p q r, g c ∈ commutator Q := by
    intro c hc
    have : ab (g c) = 1 := by rw [hall c hc]; exact ha1
    rw [← Abelianization.ker_of]
    exact this
  rw [Group.isPerfect_def, eq_top_iff]
  have hgen : Subgroup.closure (g '' Set.Iio (ngen p q r)) = ⊤ := by
    have h := congrArg (Subgroup.map (quotMk F)) (closure_yGen p q r)
    rw [MonoidHom.map_closure, Set.image_image, Subgroup.map_top_of_surjective _
      (quotMk_surjective F)] at h
    exact h
  rw [← hgen, Subgroup.closure_le]
  rintro _ ⟨c, hc, rfl⟩
  exact hgens c hc

end CFSG.Sporadic.Recognition.YCover
