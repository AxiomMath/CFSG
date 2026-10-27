module

public import CFSG.Quasithin.EmptyFaithful.S153EQuad
public import CFSG.Quasithin.EmptyFaithful.S153EO4

public section

namespace CFSG.Quasithin

namespace S153E56f

open CFSG.Quasithin.S153E

section Polar

variable {W : Type} [CommGroup W] {q : W → ZMod 2}

theorem quadPolar_comm' (x y : W) : quadPolar q x y = quadPolar q y x := by
  unfold quadPolar
  rw [mul_comm x y]
  ring

theorem quadPolar_self' (hq : IsQuadraticFormOn q) (hexp : ∀ w : W, w * w = 1) (x : W) :
    quadPolar q x x = 0 := by
  unfold quadPolar
  rw [hexp x, hq.1]
  generalize q x = a
  revert a
  decide

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem mem_perp_zpowers (hq : IsQuadraticFormOn q) (hexp : ∀ w : W, w * w = 1) {z v : W} :
    v ∈ perpSub hq (Subgroup.zpowers z) ↔ quadPolar q z v = 0 := by
  rw [mem_perpSub]
  constructor
  · intro h
    exact h z (Subgroup.mem_zpowers z)
  · intro h x hx
    rcases S152O4.eq_one_or_eq_of_mem_zpowers_two (hexp z) hx with h' | h'
    · rw [h']
      exact quadPolar_one_left hq v
    · rw [h']
      exact h

end Polar

section Pair

variable {W : Type} [CommGroup W] {q : W → ZMod 2}

theorem mem_pair_iff (hexp : ∀ w : W, w * w = 1) {z z' d : W} :
    d ∈ Subgroup.zpowers z ⊔ Subgroup.zpowers z' ↔ d = 1 ∨ d = z ∨ d = z' ∨ d = z * z' := by
  constructor
  · intro hd
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hd
    rcases S152O4.eq_one_or_eq_of_mem_zpowers_two (hexp z) ha with h1 | h1 <;>
      rcases S152O4.eq_one_or_eq_of_mem_zpowers_two (hexp z') hb with h2 | h2 <;>
      simp [h1, h2]
  · rintro (h | h | h | h)
    · rw [h]
      exact Subgroup.one_mem _
    · rw [h]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers z)
    · rw [h]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z')
    · rw [h]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers z'))

theorem card_pair (hexp : ∀ w : W, w * w = 1) {z z' : W} (hz : z ≠ 1) (hz' : z' ≠ 1) (hne : z ≠ z') :
    Nat.card ↥(Subgroup.zpowers z ⊔ Subgroup.zpowers z') = 4 := by
  have hexp' : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact hexp w
  have hz2 : Nat.card (Subgroup.zpowers z) = 2 := T1531O4.card_zpowers_of_sq hz (hexp' z)
  have hz2' : Nat.card (Subgroup.zpowers z') = 2 := T1531O4.card_zpowers_of_sq hz' (hexp' z')
  have hinfS : Subgroup.zpowers z ⊓ Subgroup.zpowers z' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    rcases S152O4.eq_one_or_eq_of_mem_zpowers_two (hexp z) hx.1 with h | h
    · exact h
    · rcases S152O4.eq_one_or_eq_of_mem_zpowers_two (hexp z') hx.2 with h' | h'
      · exact h'
      · exact absurd (h.symm.trans h') hne
  have := card_sup_mul_card_inf (Subgroup.zpowers z) (Subgroup.zpowers z')
  rw [hinfS, Subgroup.card_bot, mul_one, hz2, hz2'] at this
  omega

theorem perp_pair [Finite W] (hq : IsQuadraticFormOn q) (hn : IsNondegQuadratic q)
    (hexp : ∀ w : W, w * w = 1) (hcard : Nat.card W = 16) {z z' v : W} (hz : z ≠ 1) (hz' : z' ≠ 1)
    (hne : z ≠ z') (h0 : quadPolar q z z' = 0) (h1 : quadPolar q z v = 0)
    (h2 : quadPolar q z' v = 0) : v = 1 ∨ v = z ∨ v = z' ∨ v = z * z' := by
  have hexp' : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact hexp w
  have hz2 : Nat.card (Subgroup.zpowers z) = 2 := T1531O4.card_zpowers_of_sq hz (hexp' z)
  have hz2' : Nat.card (Subgroup.zpowers z') = 2 := T1531O4.card_zpowers_of_sq hz' (hexp' z')
  have hkzc : Nat.card ↥(perpSub hq (Subgroup.zpowers z)) = 8 := by
    have := card_perpSub_of_card_two hq hn hz2
    omega
  have hkzc' : Nat.card ↥(perpSub hq (Subgroup.zpowers z')) = 8 := by
    have := card_perpSub_of_card_two hq hn hz2'
    omega
  have hScard := card_pair hexp hz hz' hne
  have hzK : z ∈ perpSub hq (Subgroup.zpowers z) ⊓ perpSub hq (Subgroup.zpowers z') :=
    ⟨(mem_perp_zpowers hq hexp).2 (quadPolar_self' hq hexp z),
      (mem_perp_zpowers hq hexp).2 (by rw [quadPolar_comm']; exact h0)⟩
  have hz'K : z' ∈ perpSub hq (Subgroup.zpowers z) ⊓ perpSub hq (Subgroup.zpowers z') :=
    ⟨(mem_perp_zpowers hq hexp).2 h0, (mem_perp_zpowers hq hexp).2 (quadPolar_self' hq hexp z')⟩
  have hSle : Subgroup.zpowers z ⊔ Subgroup.zpowers z' ≤
      perpSub hq (Subgroup.zpowers z) ⊓ perpSub hq (Subgroup.zpowers z') :=
    sup_le (Subgroup.zpowers_le.mpr hzK) (Subgroup.zpowers_le.mpr hz'K)
  have hnle : ¬ perpSub hq (Subgroup.zpowers z) ≤ perpSub hq (Subgroup.zpowers z') := by
    intro hle
    have heq : perpSub hq (Subgroup.zpowers z) = perpSub hq (Subgroup.zpowers z') :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hkzc, hkzc'])
    have hrad : ∀ w : W, quadPolar q (z * z') w = 0 := by
      intro w
      have hiff : quadPolar q z w = 0 ↔ quadPolar q z' w = 0 := by
        constructor
        · intro h
          have h' : w ∈ perpSub hq (Subgroup.zpowers z) := (mem_perp_zpowers hq hexp).2 h
          rw [heq] at h'
          exact (mem_perp_zpowers hq hexp).1 h'
        · intro h
          have h' : w ∈ perpSub hq (Subgroup.zpowers z') := (mem_perp_zpowers hq hexp).2 h
          rw [← heq] at h'
          exact (mem_perp_zpowers hq hexp).1 h'
      rw [hq.2.1 z z' w]
      rcases zmod2_cases (quadPolar q z w) with h | h
      · rw [h, hiff.1 h]
        rfl
      · have h' : quadPolar q z' w = 1 := by
          rcases zmod2_cases (quadPolar q z' w) with h'' | h''
          · exact absurd (hiff.2 h'') (by rw [h]; decide)
          · exact h''
        rw [h, h']
        decide
    have h1' : z * z' = 1 := hn (z * z') hrad
    exact hne ((mul_eq_one_iff_eq_inv.mp h1').trans (inv_eq_of_mul_eq_one_right (hexp z')))
  have hK₂le8 : Nat.card ↥(perpSub hq (Subgroup.zpowers z) ⊓ perpSub hq (Subgroup.zpowers z')) ≤ 8 := by
    rw [← hkzc]
    exact Subgroup.card_le_of_le inf_le_left
  have hK₂ne8 : Nat.card ↥(perpSub hq (Subgroup.zpowers z) ⊓ perpSub hq (Subgroup.zpowers z')) ≠ 8 := by
    intro h8
    apply hnle
    have : perpSub hq (Subgroup.zpowers z) ⊓ perpSub hq (Subgroup.zpowers z') =
        perpSub hq (Subgroup.zpowers z) :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h8, hkzc])
    rw [← this]
    exact inf_le_right
  have hdvd : Nat.card ↥(perpSub hq (Subgroup.zpowers z) ⊓ perpSub hq (Subgroup.zpowers z')) ∣ 8 := by
    rw [← hkzc]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hK₂le4 : Nat.card ↥(perpSub hq (Subgroup.zpowers z) ⊓ perpSub hq (Subgroup.zpowers z')) ≤ 4 := by
    generalize Nat.card ↥(perpSub hq (Subgroup.zpowers z) ⊓ perpSub hq (Subgroup.zpowers z')) = b
      at hdvd hK₂ne8 hK₂le8 ⊢
    interval_cases b <;> omega
  have hSeq : Subgroup.zpowers z ⊔ Subgroup.zpowers z' =
      perpSub hq (Subgroup.zpowers z) ⊓ perpSub hq (Subgroup.zpowers z') :=
    Subgroup.eq_of_le_of_card_ge hSle (by rw [hScard]; exact hK₂le4)
  have hv : v ∈ Subgroup.zpowers z ⊔ Subgroup.zpowers z' := by
    rw [hSeq]
    exact ⟨(mem_perp_zpowers hq hexp).2 h1, (mem_perp_zpowers hq hexp).2 h2⟩
  exact (mem_pair_iff hexp).1 hv

end Pair

section Core

variable {W : Type} [CommGroup W] {q : W → ZMod 2}

theorem comm_le_of_even [Finite W] (hexp : ∀ w : W, w * w = 1) (hcard : Nat.card W = 16)
    {f : MulAut W} (hff : f * f = 1) (hev : Even (rk (commV (Subgroup.zpowers f)))) {D : Subgroup W}
    (hD : Nat.card D = 4) (hfix : ∀ d ∈ D, f d = d) (w : W) : f w * w⁻¹ ∈ D := by
  have hexp' : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact hexp w
  have hle : commV (Subgroup.zpowers f) ≤ fixV (Subgroup.zpowers f) :=
    commV_zpowers_le_fixV_of_sq hexp hff
  have hsum := rk_commV_add_rk_fixV f
  rw [S152O4.rk_V_eq_four hcard] at hsum
  have hDfix : D ≤ fixV (Subgroup.zpowers f) := fun d hd => mem_fixV_zpowers_iff.mpr (hfix d hd)
  have hrD : rk D = 2 := T1531O4.rk_eq_of_card hexp' (n := 2) (by rw [hD]; norm_num)
  have hrle : rk D ≤ rk (fixV (Subgroup.zpowers f)) := rk_mono hDfix
  have hmem : f w * w⁻¹ ∈ commV (Subgroup.zpowers f) :=
    Subgroup.subset_closure ⟨f, Subgroup.mem_zpowers f, w, rfl⟩
  obtain ⟨m, hm⟩ := hev
  have hcases : rk (commV (Subgroup.zpowers f)) = 0 ∨ rk (commV (Subgroup.zpowers f)) = 2 := by
    omega
  rcases hcases with h0 | h2
  · have hbot : commV (Subgroup.zpowers f) = ⊥ := (rk_eq_zero_iff hexp').1 h0
    rw [hbot, Subgroup.mem_bot] at hmem
    rw [hmem]
    exact D.one_mem
  · have hD' : D = fixV (Subgroup.zpowers f) := eq_of_le_of_rk_le hexp' hDfix (by omega)
    rw [hD']
    exact hle hmem

theorem x_perp_core [Finite W] (hq : IsQuadraticFormOn q) (hn : IsNondegQuadratic q)
    (hexp : ∀ w : W, w * w = 1) (hcard : Nat.card W = 16) {z z' : W} (hz : z ≠ 1) (hz' : z' ≠ 1)
    (hne : z ≠ z') (hqz : q z = 0) (hqz' : q z' = 0) (h0 : quadPolar q z z' = 0) {f : MulAut W}
    (hf : f ∈ orthogonalGroupOf q) (hff : f * f = 1)
    (hev : Even (rk (commV (Subgroup.zpowers f)))) (hfz : f z = z) (hfz' : f z' = z') {v : W}
    (hv : quadPolar q z v = 0) : f v * v⁻¹ = 1 ∨ f v * v⁻¹ = z := by
  have hDfix : ∀ d ∈ Subgroup.zpowers z ⊔ Subgroup.zpowers z', f d = d := by
    intro d hd
    rcases (mem_pair_iff hexp).1 hd with h | h | h | h
    · rw [h, map_one]
    · rw [h, hfz]
    · rw [h, hfz']
    · rw [h, map_mul, hfz, hfz']
  have hc : f v * v⁻¹ ∈ Subgroup.zpowers z ⊔ Subgroup.zpowers z' :=
    comm_le_of_even hexp hcard hff hev (card_pair hexp hz hz' hne) hDfix v
  have hqzz' : q (z * z') = 0 := by
    have h := h0
    unfold quadPolar at h
    rw [hqz, hqz'] at h
    simpa using h
  have hBc : ∀ c : W, c = f v * v⁻¹ → q c = 0 → quadPolar q v c = 0 := by
    intro c hc' hqc
    have hvc : v * c = f v := by
      rw [hc', mul_left_comm, mul_inv_cancel, mul_one]
    unfold quadPolar
    rw [hvc, hf v, hqc]
    generalize q v = a
    revert a
    decide
  have hperp : quadPolar q z' v = 0 → v ∈ Subgroup.zpowers z ⊔ Subgroup.zpowers z' := by
    intro h
    exact (mem_pair_iff hexp).2 (perp_pair hq hn hexp hcard hz hz' hne h0 hv h)
  have hfv : v ∈ Subgroup.zpowers z ⊔ Subgroup.zpowers z' → f v * v⁻¹ = 1 := by
    intro h
    rw [hDfix v h]
    exact mul_inv_cancel v
  have hzz'1 : z * z' ≠ 1 := fun h => hne ((mul_eq_one_iff_eq_inv.mp h).trans
    (inv_eq_of_mul_eq_one_right (hexp z')))
  rcases (mem_pair_iff hexp).1 hc with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    have hB := hBc _ rfl (by rw [h]; exact hqz')
    rw [h] at hB
    have := hfv (hperp (by rw [quadPolar_comm']; exact hB))
    rw [h] at this
    exact hz' this
  · exfalso
    have hB := hBc _ rfl (by rw [h]; exact hqzz')
    rw [h, hq.2.2 v z z', quadPolar_comm' v z, hv] at hB
    have hB' : quadPolar q z' v = 0 := by
      rw [quadPolar_comm']
      simpa using hB
    have := hfv (hperp hB')
    rw [h] at this
    exact hzz'1 this

theorem triple_perp [Finite W] (hq : IsQuadraticFormOn q) (hn : IsNondegQuadratic q)
    (hexp : ∀ w : W, w * w = 1) (hcard : Nat.card W = 16) {z z' z'' k : W} (hz : z ≠ 1) (hz' : z' ≠ 1)
    (hne : z ≠ z') (h0 : quadPolar q z z' = 0) (h0'' : quadPolar q z z'' = 0) (hz''1 : z'' ≠ 1)
    (hz''z : z'' ≠ z) (hz''z' : z'' ≠ z') (hz''zz' : z'' ≠ z * z') (hk1 : quadPolar q z k = 0)
    (hk2 : quadPolar q z' k = 0) (hk3 : quadPolar q z'' k = 0) : k = 1 ∨ k = z := by
  have hB : quadPolar q z' z'' ≠ 0 := by
    intro h
    rcases perp_pair hq hn hexp hcard hz hz' hne h0 h0'' h with h' | h' | h' | h'
    · exact hz''1 h'
    · exact hz''z h'
    · exact hz''z' h'
    · exact hz''zz' h'
  rcases perp_pair hq hn hexp hcard hz hz' hne h0 hk1 hk2 with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    rw [h] at hk3
    apply hB
    rw [quadPolar_comm']
    exact hk3
  · exfalso
    rw [h, hq.2.2 z'' z z'] at hk3
    rw [quadPolar_comm' z'' z, h0''] at hk3
    apply hB
    rw [quadPolar_comm']
    simpa using hk3

theorem pair_of_order_three (hexp : ∀ w : W, w * w = 1) {yb : MulAut W}
    (hyq : yb ∈ orthogonalGroupOf q) (hy3 : yb ^ 3 = 1) (hfix : fixV (Subgroup.zpowers yb) = ⊥)
    {z : W} (hz : z ≠ 1) (hqz : q z = 0) :
    yb⁻¹ z ≠ 1 ∧ yb⁻¹ z ≠ z ∧ q (yb⁻¹ z) = 0 ∧ z * yb⁻¹ z = yb z ∧ q (z * yb⁻¹ z) = 0 ∧
      quadPolar q z (yb⁻¹ z) = 0 := by
  have hyinv : yb⁻¹ ∈ orthogonalGroupOf q := (orthogonalGroupOf q).inv_mem hyq
  have h1 : yb⁻¹ z ≠ 1 := by
    intro h
    apply hz
    have := congrArg yb h
    rw [map_one] at this
    simpa using this
  have h2 : yb⁻¹ z ≠ z := by
    intro h
    have h' : yb z = z := by
      have := congrArg yb h
      simpa using this.symm
    have : z ∈ fixV (Subgroup.zpowers yb) := mem_fixV_zpowers_iff.mpr h'
    rw [hfix, Subgroup.mem_bot] at this
    exact hz this
  have h3 : q (yb⁻¹ z) = 0 := by
    rw [hyinv z]
    exact hqz
  have hy2 : yb * yb = yb⁻¹ := by
    have : yb * (yb * yb) = 1 := by
      rw [← pow_three]
      exact hy3
    exact eq_inv_of_mul_eq_one_right this
  have hu : z * yb z * yb⁻¹ z = 1 := by
    have hmem : z * yb z * yb⁻¹ z ∈ fixV (Subgroup.zpowers yb) := by
      rw [mem_fixV_zpowers_iff, map_mul, map_mul]
      have e1 : yb (yb z) = yb⁻¹ z := by
        rw [← MulAut.mul_apply, hy2]
      have e2 : yb (yb⁻¹ z) = z := by simp
      rw [e1, e2]
      ac_rfl
    rw [hfix, Subgroup.mem_bot] at hmem
    exact hmem
  have h4 : z * yb⁻¹ z = yb z := by
    have h5 : yb z * (z * yb⁻¹ z) = 1 := by
      rw [← hu]
      ac_rfl
    have h6 : z * yb⁻¹ z = (yb z)⁻¹ := eq_inv_of_mul_eq_one_right h5
    rw [h6]
    exact inv_eq_of_mul_eq_one_right (hexp _)
  have h7 : q (z * yb⁻¹ z) = 0 := by
    rw [h4, hyq z]
    exact hqz
  refine ⟨h1, h2, h3, h4, h7, ?_⟩
  unfold quadPolar
  rw [h7, hqz, h3]
  rfl

end Core

end S153E56f

end CFSG.Quasithin
