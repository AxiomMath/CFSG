module

public import CFSG.LocalAnalysis.StandardType.GGTypeAFarVec

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal.SpecialLinear Matrix

section Shape

variable {X : Type*} [Group X] {n : ℕ} {F : Type} [Field F]
  {φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) F →* X} {Bs : Subgroup X}

theorem ggFar_shape_x (hL : GGFarLifts φ₁ φ₂ Bs) {x : X} (hx : x ∈ Bs)
    (hxL : ∀ s, x * φ₁ s = φ₁ s * x) (hxK : ¬ ∀ s, x * φ₂ s = φ₂ s * x) :
    ∃ τ : Fˣ, τ ≠ 1 ∧ GGActsVec φ₁ x 1 ∧ GGActsVec φ₂ x (diagAt (Fin.last n) τ) := by
  have h1 : GGActsVec φ₁ x 1 := GGActsVec.one_of_commute hxL
  obtain ⟨u, hu⟩ := hL.diag₂ x hx
  have hc := GGActsVec.block_compat hL.ker₁ hL.compat h1 hu
  obtain ⟨c, hc'⟩ := ggVecEq_iff_exists.1 hc
  have hc'' : ∀ k : Fin n, u k.castSucc = c⁻¹ := fun k =>
    (inv_eq_of_mul_eq_one_right (hc' k).symm).symm
  have he : GGVecEq u (diagAt (Fin.last n) (u (Fin.last n) * c)) := by
    refine ggVecEq_iff_exists.2 ⟨c⁻¹, fun k => ?_⟩
    induction k using Fin.lastCases with
    | last =>
        rw [diagAt_apply_self, mul_comm (u (Fin.last n)) c, ← mul_assoc, inv_mul_cancel,
          one_mul]
    | cast k' =>
        rw [diagAt_apply_of_ne (Fin.castSucc_lt_last k').ne, mul_one]
        exact hc'' k'
  refine ⟨u (Fin.last n) * c, ?_, h1, GGActsVec.of_vecEq hu he⟩
  intro hτ
  rw [hτ, diagAt_one] at he
  exact hxK (GGActsVec.commute_of_vecEq_one hu he)

theorem ggFar_shape_y (hL : GGFarLifts φ₁ φ₂ Bs) {y : X} (hy : y ∈ Bs)
    (hyK : ∀ s, y * φ₂ s = φ₂ s * y) {i : Fin n} (hi : i.val = 0) :
    ∃ τ : Fˣ, GGActsVec φ₂ y 1 ∧ GGActsVec φ₁ y (diagAt i.castSucc τ) := by
  have h1 : GGActsVec φ₂ y 1 := GGActsVec.one_of_commute hyK
  obtain ⟨h, hh⟩ := hL.diag₁ y hy
  have hc := GGActsVec.block_compat hL.ker₁ hL.compat hh h1
  obtain ⟨c, hc'⟩ := ggVecEq_iff_exists.1 hc
  have hi0 : i.castSucc = (0 : Fin (n + 1)) := Fin.ext (by simpa using hi)
  have he : GGVecEq h (diagAt i.castSucc (h i.castSucc * c⁻¹)) := by
    refine ggVecEq_iff_exists.2 ⟨c, fun k => ?_⟩
    induction k using Fin.cases with
    | zero =>
        rw [← hi0, diagAt_apply_self, mul_comm (h i.castSucc) c⁻¹, ← mul_assoc,
          mul_inv_cancel, one_mul]
    | succ j =>
        rw [diagAt_apply_of_ne (k := i.castSucc) (l := j.succ)
          (by rw [hi0]; exact Fin.succ_ne_zero j)]
        exact hc' j
  exact ⟨h i.castSucc * c⁻¹, h1, GGActsVec.of_vecEq hh he⟩

theorem ggFar_shape_z (h2 : (2 : F) = 0) (hL : GGFarLifts φ₁ φ₂ Bs) (hn : 2 ≤ n)
    {i j : Fin n} (hi : i.val = 0) (hj : j.val + 1 = n) {y : X} {τ : Fˣ}
    (hy2 : GGActsVec φ₁ y (diagAt i.castSucc τ)) {a b z : X} (ha : a = φ₁ (weylRep n F i))
    (hb : b = φ₂ (weylRep n F j)) (hz : z = a * y * a⁻¹) (hzB : z ∈ Bs)
    (hbz : b * z * b⁻¹ = z) :
    GGActsVec φ₁ z (diagAt i.succ τ) ∧ GGActsVec φ₂ z (diagAt i.castSucc τ) := by
  have ha' : a = φ₁ (slPerm h2 (Equiv.swap i.castSucc i.succ)) := by
    rw [ha, slPerm_swap_castSucc_succ]
  have hb' : b = φ₂ (slPerm h2 (Equiv.swap j.castSucc j.succ)) := by
    rw [hb, slPerm_swap_castSucc_succ]
  have hz1 : GGActsVec φ₁ z (diagAt i.succ τ) := by
    have hp := GGActsVec.conj_perm h2 hy2 (Equiv.swap i.castSucc i.succ)
    rw [diagAt_comp_perm, Equiv.swap_apply_left] at hp
    have hz' : z = φ₁ (slPerm h2 (Equiv.swap i.castSucc i.succ)) * y *
        (φ₁ (slPerm h2 (Equiv.swap i.castSucc i.succ)))⁻¹ := by rw [hz, ha']
    rwa [hz']
  obtain ⟨v, hv⟩ := hL.diag₂ z hzB
  have h1 := GGActsVec.block_compat hL.ker₁ hL.compat hz1 hv
  rw [diagAt_succ_comp_succ] at h1
  have h2' : GGVecEq v (v ∘ (Equiv.swap j.castSucc j.succ).symm) := by
    have hp := GGActsVec.conj_perm h2 hv (Equiv.swap j.castSucc j.succ)
    have hb'' : φ₂ (slPerm h2 (Equiv.swap j.castSucc j.succ)) * z *
        (φ₂ (slPerm h2 (Equiv.swap j.castSucc j.succ)))⁻¹ = z := by
      rw [← hb']; exact hbz
    rw [hb''] at hp
    exact GGActsVec.vecEq hL.ker₂ hv hp
  exact ⟨hz1, GGActsVec.of_vecEq hv (vec_end_of_swap_fixed hn hi hj τ v h1 h2')⟩

theorem ggFar_shape_w0 (h2 : (2 : F) = 0) (hL : GGFarLifts φ₁ φ₂ Bs) (hn : 2 ≤ n)
    {i j : Fin n} (hi : i.val = 0) (hj : j.val + 1 = n) {x : X} {τ : Fˣ}
    (hx2 : GGActsVec φ₂ x (diagAt (Fin.last n) τ)) {a b w₀ : X} (ha : a = φ₁ (weylRep n F i))
    (hb : b = φ₂ (weylRep n F j)) (hw₀ : w₀ = b * x * b⁻¹) (hw₀B : w₀ ∈ Bs)
    (haw : a * w₀ * a⁻¹ = w₀) :
    GGActsVec φ₂ w₀ (diagAt j.castSucc τ) ∧ GGActsVec φ₁ w₀ (diagAt (Fin.last n) τ) := by
  have ha' : a = φ₁ (slPerm h2 (Equiv.swap i.castSucc i.succ)) := by
    rw [ha, slPerm_swap_castSucc_succ]
  have hb' : b = φ₂ (slPerm h2 (Equiv.swap j.castSucc j.succ)) := by
    rw [hb, slPerm_swap_castSucc_succ]
  have hjl : j.succ = Fin.last n := Fin.ext (by simpa using hj)
  have hw₁ : GGActsVec φ₂ w₀ (diagAt j.castSucc τ) := by
    have hp := GGActsVec.conj_perm h2 hx2 (Equiv.swap j.castSucc j.succ)
    rw [diagAt_comp_perm, ← hjl, Equiv.swap_apply_right] at hp
    have hw' : w₀ = φ₂ (slPerm h2 (Equiv.swap j.castSucc j.succ)) * x *
        (φ₂ (slPerm h2 (Equiv.swap j.castSucc j.succ)))⁻¹ := by rw [hw₀, hb']
    rwa [hw']
  obtain ⟨m, hm⟩ := hL.diag₁ w₀ hw₀B
  have h1 := GGActsVec.block_compat hL.ker₁ hL.compat hm hw₁
  rw [diagAt_castSucc_comp_castSucc] at h1
  have h2' : GGVecEq m (m ∘ (Equiv.swap i.castSucc i.succ).symm) := by
    have hp := GGActsVec.conj_perm h2 hm (Equiv.swap i.castSucc i.succ)
    have ha'' : φ₁ (slPerm h2 (Equiv.swap i.castSucc i.succ)) * w₀ *
        (φ₁ (slPerm h2 (Equiv.swap i.castSucc i.succ)))⁻¹ = w₀ := by
      rw [← ha']; exact haw
    rw [ha''] at hp
    exact GGActsVec.vecEq hL.ker₁ hm hp
  exact ⟨hw₁, GGActsVec.of_vecEq hm (vec_start_of_swap_fixed hn hi hj τ m h1 h2')⟩

theorem ggFar_shape_w (h2 : (2 : F) = 0) (hL : GGFarLifts φ₁ φ₂ Bs) {i j : Fin n}
    (hj : j.val + 1 = n) {w₀ : X} {τ : Fˣ} (hw₁ : GGActsVec φ₂ w₀ (diagAt j.castSucc τ))
    (hw₂ : GGActsVec φ₁ w₀ (diagAt (Fin.last n) τ)) {c w : X}
    (hc : c = φ₁ (slLowerBlockHom n F (slPerm h2 (Equiv.swap i j)))) (hw : w = c * w₀ * c⁻¹) :
    GGActsVec φ₁ w (diagAt i.succ τ) ∧ GGActsVec φ₂ w (diagAt i.castSucc τ) := by
  have hc1 : c = φ₁ (slPerm h2 (Equiv.swap i.succ j.succ)) := by
    rw [hc, slLowerBlockHom_slPerm_swap]
  have hc2 : c = φ₂ (slPerm h2 (Equiv.swap i.castSucc j.castSucc)) := by
    have hcomp := DFunLike.congr_fun hL.compat (slPerm h2 (Equiv.swap i j))
    simp only [MonoidHom.comp_apply] at hcomp
    rw [hc, hcomp, slUpperBlockHom_slPerm_swap]
  have hw₁' : GGActsVec φ₂ w (diagAt i.castSucc τ) := by
    have hp := GGActsVec.conj_perm h2 hw₁ (Equiv.swap i.castSucc j.castSucc)
    rw [diagAt_comp_perm, Equiv.swap_apply_right] at hp
    have hw' : w = φ₂ (slPerm h2 (Equiv.swap i.castSucc j.castSucc)) * w₀ *
        (φ₂ (slPerm h2 (Equiv.swap i.castSucc j.castSucc)))⁻¹ := by rw [hw, hc2]
    rwa [hw']
  have hw₂' : GGActsVec φ₁ w (diagAt i.succ τ) := by
    have hjl : j.succ = Fin.last n := Fin.ext (by simpa using hj)
    have hp := GGActsVec.conj_perm h2 hw₂ (Equiv.swap i.succ j.succ)
    rw [diagAt_comp_perm, ← hjl, Equiv.swap_apply_right] at hp
    have hw' : w = φ₁ (slPerm h2 (Equiv.swap i.succ j.succ)) * w₀ *
        (φ₁ (slPerm h2 (Equiv.swap i.succ j.succ)))⁻¹ := by rw [hw, hc1]
    rwa [hw']
  exact ⟨hw₂', hw₁'⟩

theorem ggFar_shape_zpow [Finite F] (hL : GGFarLifts φ₁ φ₂ Bs) {p : ℕ} [Fact p.Prime]
    (hBp : ∀ b ∈ Bs, b ^ p = 1) (hn : 1 ≤ n) {τ τ' : Fˣ} (hτ' : τ' ≠ 1)
    (hinj : ∀ g ∈ Bs, (∀ s, g * φ₁ s = φ₁ s * g) → (∀ s, g * φ₂ s = φ₂ s * g) → g = 1)
    {z w : X} (hz : z ∈ Bs) (hw : w ∈ Bs) {k₀ k₁ : Fin (n + 1)}
    (hz₁ : GGActsVec φ₁ z (diagAt k₁ τ)) (hz₂ : GGActsVec φ₂ z (diagAt k₀ τ))
    (hw₁ : GGActsVec φ₁ w (diagAt k₁ τ')) (hw₂ : GGActsVec φ₂ w (diagAt k₀ τ')) :
    ∃ k : ℤ, z = w ^ k := by
  have hτ : τ ^ p = 1 :=
    pow_eq_one_of_actsVec_diagAt hL.ker₁ (by omega) (hBp z hz) hz₁
  have hτ'p : τ' ^ p = 1 :=
    pow_eq_one_of_actsVec_diagAt hL.ker₁ (by omega) (hBp w hw) hw₁
  obtain ⟨k, hk⟩ := exists_zpow_eq_of_pow_eq_one hτ hτ'p hτ'
  have hg₁ : GGActsVec φ₁ (z * (w ^ k)⁻¹) 1 := by
    have h := GGActsVec.mul hz₁ (GGActsVec.inv (GGActsVec.zpow hw₁ k))
    rw [diagAt_zpow, ← hk, mul_inv_cancel] at h
    exact h
  have hg₂ : GGActsVec φ₂ (z * (w ^ k)⁻¹) 1 := by
    have h := GGActsVec.mul hz₂ (GGActsVec.inv (GGActsVec.zpow hw₂ k))
    rw [diagAt_zpow, ← hk, mul_inv_cancel] at h
    exact h
  have hgmem : z * (w ^ k)⁻¹ ∈ Bs := Bs.mul_mem hz (Bs.inv_mem (Subgroup.zpow_mem Bs hw k))
  refine ⟨k, ?_⟩
  have h1 := hinj (z * (w ^ k)⁻¹) hgmem
    (GGActsVec.commute_of_vecEq_one hg₁ (GGVecEq.refl (1 : Fin (n + 1) → Fˣ)))
    (GGActsVec.commute_of_vecEq_one hg₂ (GGVecEq.refl (1 : Fin (n + 1) → Fˣ)))
  exact mul_inv_eq_one.mp h1

end Shape

section Aux

variable {X : Type*} [Group X]

theorem ggFar_conj_comm_aux_left {a b g : X} (ha : a * a = 1) (hb : b * b = 1)
    (hu : (a * b * a * b) * g = g * (a * b * a * b)) (hbg : b * g * b⁻¹ = g) :
    b * (a * g * a⁻¹) * b⁻¹ = a * g * a⁻¹ := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  rw [hb'] at hbg
  rw [ha', hb'] at ⊢
  have hbg' : b * g = g * b := by
    have h := congrArg (· * b) hbg
    simpa [mul_assoc, hb] using h
  have hf2 : (a * b * a) * (a * b * a) = 1 := by
    have h : (a * b * a) * (a * b * a) = a * (b * (a * a) * b) * a := by group
    rw [h, ha]
    simp only [mul_one]
    rw [hb]
    simp [ha]
  have hfg : (a * b * a) * g = g * (a * b * a) := by
    have h := hu
    rw [show (a * b * a * b) * g = (a * b * a) * (b * g) by group,
      show g * (a * b * a * b) = g * (a * b * a) * b by group, hbg'] at h
    have h2 := congrArg (· * b) h
    simpa [mul_assoc, hb] using h2
  have hfg2 : (a * b * a) * g * (a * b * a) = g := by
    rw [hfg, mul_assoc, hf2, mul_one]
  have hstep : a * (b * (a * g * a) * b) * a = (a * b * a) * g * (a * b * a) := by group
  have hgoal : a * (b * (a * g * a) * b) * a = g := by rw [hstep, hfg2]
  calc b * (a * g * a) * b
      = (a * a) * (b * (a * g * a) * b) * (a * a) := by simp [ha]
    _ = a * (a * (b * (a * g * a) * b) * a) * a := by group
    _ = a * g * a := by rw [hgoal]

theorem ggFar_conj_comm_aux_right {a b g : X} (ha : a * a = 1) (hb : b * b = 1)
    (hu : (a * b * a * b) * g = g * (a * b * a * b)) (hag : a * g * a⁻¹ = g) :
    a * (b * g * b⁻¹) * a⁻¹ = b * g * b⁻¹ := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  rw [ha'] at hag
  rw [ha', hb'] at ⊢
  have hag2 : a * g * a = g := hag
  have hag' : a * g = g * a := by
    have h := congrArg (· * a) hag2
    simpa [mul_assoc, ha] using h
  have he2 : (b * a * b) * (b * a * b) = 1 := by
    have h : (b * a * b) * (b * a * b) = b * (a * (b * b) * a) * b := by group
    rw [h, hb]
    simp only [mul_one]
    rw [ha]
    simp [hb]
  have hee : (b * a * b) * g = g * (b * a * b) := by
    have h1 : a * ((a * b * a * b) * g) = a * (g * (a * b * a * b)) := congrArg (a * ·) hu
    have h2 : a * ((a * b * a * b) * g) = (b * a * b) * g := by
      calc a * ((a * b * a * b) * g) = (a * (a * b * a * b)) * g := by group
        _ = ((a * a) * b * a * b) * g := by group
        _ = (b * a * b) * g := by rw [ha]; simp
    have h3 : a * (g * (a * b * a * b)) = g * (b * a * b) := by
      calc a * (g * (a * b * a * b)) = (a * g) * (a * b * a * b) := by group
        _ = (g * a) * (a * b * a * b) := by rw [hag']
        _ = (g * (a * a)) * (b * a * b) := by group
        _ = g * (b * a * b) := by rw [ha]; simp
    rw [h2, h3] at h1
    exact h1
  have hee2 : (b * a * b) * g * (b * a * b) = g := by
    rw [hee, mul_assoc, he2, mul_one]
  calc a * (b * g * b) * a
      = (b * b) * (a * (b * g * b) * a) * (b * b) := by simp [hb]
    _ = b * ((b * a * b) * g * (b * a * b)) * b := by group
    _ = b * g * b := by rw [hee2]

theorem zpowers_eq_of_zpowers_le_of_prime {p : ℕ} [Fact p.Prime] {z w : X} (hw : w ^ p = 1)
    (hw1 : w ≠ 1) (hz1 : z ≠ 1) (h : Subgroup.zpowers z ≤ Subgroup.zpowers w) :
    Subgroup.zpowers z = Subgroup.zpowers w := by
  have hcardw : Nat.card (Subgroup.zpowers w) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hw hw1]
  haveI : Finite (Subgroup.zpowers w) :=
    Nat.finite_of_card_ne_zero (by rw [hcardw]; exact (Fact.out : p.Prime).ne_zero)
  have hdvd : Nat.card (Subgroup.zpowers z) ∣ Nat.card (Subgroup.zpowers w) :=
    Subgroup.card_dvd_of_le h
  rw [hcardw] at hdvd
  rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd _ hdvd with h1 | hp
  · exfalso
    have hbot : Subgroup.zpowers z = ⊥ := Subgroup.card_eq_one.mp h1
    exact hz1 (Subgroup.zpowers_eq_bot.mp hbot)
  · exact Subgroup.eq_of_le_of_card_ge h (by simp [hcardw, hp])

end Aux

end CFSG.StandardType
