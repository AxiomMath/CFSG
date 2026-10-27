module

public import CFSG.RankThree.PartOne.KF.SpQuad

public section

namespace CFSG.RankThree.PartOne.S13K

open CFSG.RankThree.PartOne.KFQ

variable {K : Type} [Field K] [Finite K] [CharP K 2]

noncomputable abbrev sg (i : Fin 3) (a : Qext K) : QV K (Fin 3) := (Pi.single i a : Fin 3 → Qext K)

abbrev AutV (K : Type) [Field K] [Finite K] [CharP K 2] : Type := QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)

theorem formQ_apply (x y : QV K (Fin 3)) :
    formQ K x y = qForm (x 0) (y 0) + qForm (x 1) (y 1) + qForm (x 2) (y 2) := by
  unfold formQ
  rw [Fin.sum_univ_three]

theorem formQ_sg_left (i : Fin 3) (a : Qext K) (w : QV K (Fin 3)) :
    formQ K (sg i a) w = qForm a (w i) := by
  unfold formQ
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

theorem formQ_sg_right (i : Fin 3) (a : Qext K) (w : QV K (Fin 3)) :
    formQ K w (sg i a) = qForm (w i) a := by
  unfold formQ
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

theorem eq_zero_of_forall_qForm {a : Qext K} (h : ∀ b, qForm a b = 0) : a = 0 :=
  qForm_nondegenerate.1 a h

theorem sg_add_sg_add_sg (v : QV K (Fin 3)) : sg 0 (v 0) + sg 1 (v 1) + sg 2 (v 2) = v := by
  funext i
  fin_cases i <;> simp

theorem autV_ext_sg {g h : AutV K} (h0 : ∀ a, g (sg 0 a) = h (sg 0 a))
    (h1 : ∀ a, g (sg 1 a) = h (sg 1 a)) (h2 : ∀ a, g (sg 2 a) = h (sg 2 a)) : g = h := by
  refine LinearEquiv.ext fun v => ?_
  have hv := sg_add_sg_add_sg v
  calc g v = g (sg 0 (v 0) + sg 1 (v 1) + sg 2 (v 2)) := by rw [hv]
    _ = h (sg 0 (v 0) + sg 1 (v 1) + sg 2 (v 2)) := by simp only [map_add, h0, h1, h2]
    _ = h v := by rw [hv]

theorem mem_M10_iff' (g : AutV K) :
    g ∈ M10 K ↔ ∀ x y, qForm (g x 0) (g y 0) + qForm (g x 1) (g y 1) + qForm (g x 2) (g y 2) =
      qForm (x 0) (y 0) + qForm (x 1) (y 1) + qForm (x 2) (y 2) := by
  rw [mem_M10_iff]
  simp only [Fin.sum_univ_three]

theorem formQ_map {g : AutV K} (hg : g ∈ M10 K) (x y : QV K (Fin 3)) :
    formQ K (g x) (g y) = formQ K x y := by
  rw [formQ_apply, formQ_apply]
  exact (mem_M10_iff' g).1 hg x y

@[expose] def sBlk (K : Type) [Field K] [Finite K] [CharP K 2] : Subgroup ↥(M10 K) where
  carrier := {g | ∀ a : Qext K, g.1 (sg 1 a) = sg 1 a ∧ g.1 (sg 2 a) = sg 2 a}
  mul_mem' {g h} hg hh a := by
    refine ⟨?_, ?_⟩
    · change g.1 (h.1 (sg 1 a)) = _
      rw [(hh a).1, (hg a).1]
    · change g.1 (h.1 (sg 2 a)) = _
      rw [(hh a).2, (hg a).2]
  one_mem' a := ⟨rfl, rfl⟩
  inv_mem' {g} hg a := by
    refine ⟨?_, ?_⟩
    · change g.1.symm (sg 1 a) = _
      rw [LinearEquiv.symm_apply_eq, (hg a).1]
    · change g.1.symm (sg 2 a) = _
      rw [LinearEquiv.symm_apply_eq, (hg a).2]

theorem mem_sBlk_iff {g : ↥(M10 K)} :
    g ∈ sBlk K ↔ ∀ a : Qext K, g.1 (sg 1 a) = sg 1 a ∧ g.1 (sg 2 a) = sg 2 a := Iff.rfl

theorem sBlk_sg_zero {g : ↥(M10 K)} (hg : g ∈ sBlk K) (a : Qext K) :
    g.1 (sg 0 a) 1 = 0 ∧ g.1 (sg 0 a) 2 = 0 := by
  have key : ∀ j : Fin 3, j ≠ 0 → g.1 (sg 0 a) j = 0 := by
    intro j hj
    apply eq_zero_of_forall_qForm
    intro b
    have hfixb : g.1 (sg j b) = sg j b := by
      fin_cases j
      · exact absurd rfl hj
      · exact (hg b).1
      · exact (hg b).2
    have h1 := formQ_map g.2 (sg 0 a) (sg j b)
    rw [hfixb, formQ_sg_right, formQ_sg_right] at h1
    rw [h1]
    simp [Pi.single_eq_of_ne hj]
  exact ⟨key 1 (by decide), key 2 (by decide)⟩


theorem torusEquiv_sg (x : Fin 3 → (Qext K)ˣ) (i : Fin 3) (a : Qext K) :
    torusEquiv x (sg i a) = sg i ((x i : Qext K) * a) := by
  funext j
  rw [torusEquiv_apply]
  by_cases h : j = i
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]

theorem sg_add (i : Fin 3) (a b : Qext K) : sg i (a + b) = sg i a + sg i b := by
  funext j
  by_cases h : j = i
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]

theorem sg_sub (i : Fin 3) (a b : Qext K) : sg i (a - b) = sg i a - sg i b := by
  funext j
  by_cases h : j = i
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]

theorem sg_zero (i : Fin 3) : sg i (0 : Qext K) = 0 := by
  funext j
  simp

theorem sg_apply_self (i : Fin 3) (a : Qext K) : sg i a i = a := by simp

theorem sg_apply_ne {i j : Fin 3} (h : j ≠ i) (a : Qext K) : sg i a j = 0 := by
  simp [Pi.single_eq_of_ne h]

theorem coord_eq_zero_of_comm {m : AutV K} {x : Fin 3 → (Qext K)ˣ}
    (hm : m * torusEquiv x = torusEquiv x * m) {i j : Fin 3} (hxj : x j ≠ 1) (hxi : x i = 1)
    (a : Qext K) : m (sg j a) i = 0 := by
  have hne : ((x j : (Qext K)ˣ) : Qext K) - 1 ≠ 0 := by
    intro h
    apply hxj
    apply Units.ext
    simpa [sub_eq_zero] using h
  set u : Qext K := a / (((x j : (Qext K)ˣ) : Qext K) - 1) with hu
  have hsg : sg j a = torusEquiv x (sg j u) - sg j u := by
    rw [torusEquiv_sg, ← sg_sub]
    congr 1
    rw [hu]
    field_simp
  have h1 : m (torusEquiv x (sg j u)) = torusEquiv x (m (sg j u)) := by
    have := congrArg (fun f : AutV K => f (sg j u)) hm
    simpa using this
  rw [hsg, map_sub, h1]
  simp only [Pi.sub_apply, torusEquiv_apply, hxi, Units.val_one, one_mul, sub_self]

theorem sBlk_comm_tor {g : ↥(M10 K)} (hg : g ∈ sBlk K) {x : Fin 3 → (Qext K)ˣ} (hx : x 0 = 1) :
    g.1 * torusEquiv x = torusEquiv x * g.1 := by
  have h0 : ∀ a, g.1 (sg 0 a) = sg 0 (g.1 (sg 0 a) 0) := by
    intro a
    obtain ⟨h1, h2⟩ := sBlk_sg_zero hg a
    funext j
    fin_cases j
    · simp
    · simpa using h1
    · simpa using h2
  refine autV_ext_sg (fun a => ?_) (fun a => ?_) (fun a => ?_)
  · change g.1 (torusEquiv x (sg 0 a)) = torusEquiv x (g.1 (sg 0 a))
    rw [torusEquiv_sg, hx, Units.val_one, one_mul, h0 a, torusEquiv_sg, hx, Units.val_one, one_mul]
  · change g.1 (torusEquiv x (sg 1 a)) = torusEquiv x (g.1 (sg 1 a))
    rw [torusEquiv_sg, (hg _).1, (hg a).1, torusEquiv_sg]
  · change g.1 (torusEquiv x (sg 2 a)) = torusEquiv x (g.1 (sg 2 a))
    rw [torusEquiv_sg]
    rw [(hg _).2, (hg a).2, torusEquiv_sg]

theorem zero_coord_of_comm {m : AutV K} {ζ : (Qext K)ˣ} (hζ : ζ ≠ 1)
    (hm1 : m * torusEquiv ![1, ζ, 1] = torusEquiv ![1, ζ, 1] * m)
    (hm2 : m * torusEquiv ![1, 1, ζ] = torusEquiv ![1, 1, ζ] * m) (v : QV K (Fin 3))
    (hv : v 0 = 0) : m v 0 = 0 := by
  have hv' : v = sg 1 (v 1) + sg 2 (v 2) := by
    have := sg_add_sg_add_sg v
    rw [hv, sg_zero, zero_add] at this
    exact this.symm
  rw [hv', map_add]
  simp only [Pi.add_apply]
  rw [coord_eq_zero_of_comm hm1 (i := 0) (j := 1) (by simpa using hζ) (by simp),
    coord_eq_zero_of_comm hm2 (i := 0) (j := 2) (by simpa using hζ) (by simp), add_zero]

theorem sBlk_normalized {m : ↥(M10 K)} {ζ : (Qext K)ˣ} (hζ : ζ ≠ 1)
    (hm1 : m.1 * torusEquiv ![1, ζ, 1] = torusEquiv ![1, ζ, 1] * m.1)
    (hm2 : m.1 * torusEquiv ![1, 1, ζ] = torusEquiv ![1, 1, ζ] * m.1) {g : ↥(M10 K)}
    (hg : g ∈ sBlk K) : m * g * m⁻¹ ∈ sBlk K := by
  have hinv : ∀ x : Fin 3 → (Qext K)ˣ, m.1 * torusEquiv x = torusEquiv x * m.1 →
      m.1.symm * torusEquiv x = torusEquiv x * m.1.symm := by
    intro x hx
    refine LinearEquiv.ext fun v => ?_
    have h := congrArg (fun f : AutV K => f (m.1.symm v)) hx
    simp only [LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply] at h
    change m.1.symm (torusEquiv x v) = torusEquiv x (m.1.symm v)
    rw [LinearEquiv.symm_apply_eq, ← h]
  have hm1' := hinv _ hm1
  have hm2' := hinv _ hm2
  intro a
  have key : ∀ j : Fin 3, j ≠ 0 → m.1.symm (sg j a) = sg 1 (m.1.symm (sg j a) 1) +
      sg 2 (m.1.symm (sg j a) 2) := by
    intro j hj
    have h0 : m.1.symm (sg j a) 0 = 0 := by
      refine zero_coord_of_comm hζ hm1' hm2' (sg j a) ?_
      exact sg_apply_ne (Ne.symm hj) a
    have := sg_add_sg_add_sg (m.1.symm (sg j a))
    rw [h0, sg_zero, zero_add] at this
    exact this.symm
  have hfix : ∀ j : Fin 3, j ≠ 0 → (m * g * m⁻¹).1 (sg j a) = sg j a := by
    intro j hj
    have hw := key j hj
    have hgw : g.1 (m.1.symm (sg j a)) = m.1.symm (sg j a) := by
      rw [hw, map_add, (hg _).1, (hg _).2]
    change m.1 (g.1 (m.1.symm (sg j a))) = sg j a
    rw [hgw]
    simp
  exact ⟨hfix 1 (by decide), hfix 2 (by decide)⟩

end CFSG.RankThree.PartOne.S13K
