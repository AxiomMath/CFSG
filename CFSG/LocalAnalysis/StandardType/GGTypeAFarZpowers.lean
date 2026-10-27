module

public import CFSG.LocalAnalysis.StandardType.GGTypeAFarShape

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal.SpecialLinear Matrix

section Perm

theorem ggFar_swap_conj {n : ℕ} {i j : Fin n} (hi : i.val = 0) (hj : j.val + 1 = n)
    (hn : 2 ≤ n) :
    Equiv.swap i.castSucc j.castSucc * Equiv.swap j.castSucc j.succ *
        (Equiv.swap i.castSucc j.castSucc)⁻¹ = Equiv.swap i.castSucc j.succ := by
  have hjn : j.succ ≠ j.castSucc := fun h => by
    have := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.coe_castSucc] at this
    omega
  have hin : j.succ ≠ i.castSucc := fun h => by
    have := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.coe_castSucc] at this
    omega
  rw [Equiv.swap_inv, Equiv.swap_comm j.castSucc j.succ, Equiv.swap_comm i.castSucc j.castSucc]
  exact Equiv.swap_mul_swap_mul_swap hjn hin

theorem ggFar_swap_conj' {n : ℕ} {i j : Fin n} (hi : i.val = 0) (hj : j.val + 1 = n)
    (hn : 2 ≤ n) :
    Equiv.swap i.castSucc j.succ * Equiv.swap i.castSucc j.castSucc *
        (Equiv.swap i.castSucc j.succ)⁻¹ = Equiv.swap j.castSucc j.succ := by
  have hjc : j.castSucc ≠ i.castSucc := fun h => by
    have := congrArg Fin.val h
    simp only [Fin.coe_castSucc] at this
    omega
  have hjs : j.castSucc ≠ j.succ := fun h => by
    have := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.coe_castSucc] at this
    omega
  rw [Equiv.swap_inv, Equiv.swap_comm i.castSucc j.castSucc, Equiv.swap_comm j.castSucc j.succ]
  exact Equiv.swap_mul_swap_mul_swap hjc hjs

end Perm

section Lifts

variable {X : Type*} [Group X] {n : ℕ} {F : Type} [Field F]

theorem ggFar_c_eq {φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) F →* X} (h2 : (2 : F) = 0)
    (hc : φ₁.comp (slLowerBlockHom n F) = φ₂.comp (slUpperBlockHom n F)) (i j : Fin n) :
    φ₁ (slLowerBlockHom n F (slPerm h2 (Equiv.swap i j))) =
      φ₂ (slPerm h2 (Equiv.swap i.castSucc j.castSucc)) := by
  have e := DFunLike.congr_fun hc (slPerm h2 (Equiv.swap i j))
  simp only [MonoidHom.comp_apply] at e
  rw [e, slUpperBlockHom_slPerm_swap]

theorem ggFar_c_mul_b (h2 : (2 : F) = 0) {i j : Fin n} (hi : i.val = 0) (hj : j.val + 1 = n)
    (hn : 2 ≤ n) (φ : SpecialLinearGroup (Fin (n + 1)) F →* X) :
    φ (slPerm h2 (Equiv.swap i.castSucc j.castSucc)) * φ (weylRep n F j) *
        (φ (slPerm h2 (Equiv.swap i.castSucc j.castSucc)))⁻¹ =
      φ (slPerm h2 (Equiv.swap i.castSucc j.succ)) := by
  rw [← slPerm_swap_castSucc_succ h2 j, ← ggFar_swap_conj hi hj hn]
  simp only [map_mul, map_inv]

theorem ggFar_b₁_mul_c (h2 : (2 : F) = 0) {i j : Fin n} (hi : i.val = 0) (hj : j.val + 1 = n)
    (hn : 2 ≤ n) (φ : SpecialLinearGroup (Fin (n + 1)) F →* X) :
    φ (slPerm h2 (Equiv.swap i.castSucc j.succ)) *
        φ (slPerm h2 (Equiv.swap i.castSucc j.castSucc)) *
        (φ (slPerm h2 (Equiv.swap i.castSucc j.succ)))⁻¹ = φ (weylRep n F j) := by
  rw [← slPerm_swap_castSucc_succ h2 j, ← ggFar_swap_conj' hi hj hn]
  simp only [map_mul, map_inv]

end Lifts

section Zpowers

variable {X : Type*} [Group X] {n : ℕ} {F : Type} [Field F]
  {φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) F →* X} {Bs : Subgroup X}

theorem conj_mem_of_mem_normalizer {g b : X} (hg : g ∈ Subgroup.normalizer (Bs : Set X))
    (hb : b ∈ Bs) : g * b * g⁻¹ ∈ Bs :=
  (Subgroup.mem_normalizer_iff.1 hg b).1 hb

theorem ggTypeAFar_zpowers_eq [Finite F] (h2 : (2 : F) = 0) (hL : GGFarLifts φ₁ φ₂ Bs) {p : ℕ}
    [Fact p.Prime] (hBp : ∀ b ∈ Bs, b ^ p = 1)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set X), g ^ p = 1 → g ∈ Bs) (hn : 3 ≤ n)
    {i j : Fin n} (hi : i.val = 0) (hj : j.val + 1 = n) {x y : X} (hx : x ∈ Bs) (hy : y ∈ Bs)
    (hy1 : y ≠ 1) (hxL : ∀ s, x * φ₁ s = φ₁ s * x) (hyK : ∀ s, y * φ₂ s = φ₂ s * y)
    (hxK : ¬ ∀ s, x * φ₂ s = φ₂ s * x)
    (hinj : ∀ g ∈ Bs, (∀ s, g * φ₁ s = φ₁ s * g) → (∀ s, g * φ₂ s = φ₂ s * g) → g = 1)
    {a b b₁ : X} (ha : a = φ₁ (weylRep n F i)) (hb : b = φ₂ (weylRep n F j))
    (hb₁ : b₁ = φ₂ (slPerm h2 (Equiv.swap i.castSucc j.succ)))
    (hxu : (a * b * a * b) * x = x * (a * b * a * b))
    (hyu : (a * b * a * b) * y = y * (a * b * a * b)) :
    Subgroup.zpowers (a * y * a⁻¹) = Subgroup.zpowers (b₁ * x * b₁⁻¹) := by
  classical
  obtain ⟨τ', hτ'1, -, hx2⟩ := ggFar_shape_x hL hx hxL hxK
  obtain ⟨τ, -, hy3⟩ := ggFar_shape_y hL hy hyK hi
  have ha2 : a * a = 1 := by rw [ha, ← map_mul, weylRep_mul_self n h2, map_one]
  have hb2 : b * b = 1 := by rw [hb, ← map_mul, weylRep_mul_self n h2, map_one]
  have hnorm₁ : ∀ π, φ₁ (slPerm h2 π) ∈ Subgroup.normalizer (Bs : Set X) :=
    slPerm_mem_normalizer_of_actsDiag h2 hBp hBs hL.ker₁ hL.diag₁
  have hnorm₂ : ∀ π, φ₂ (slPerm h2 π) ∈ Subgroup.normalizer (Bs : Set X) :=
    slPerm_mem_normalizer_of_actsDiag h2 hBp hBs hL.ker₂ hL.diag₂
  have ha' : a = φ₁ (slPerm h2 (Equiv.swap i.castSucc i.succ)) := by
    rw [ha, slPerm_swap_castSucc_succ]
  have hb' : b = φ₂ (slPerm h2 (Equiv.swap j.castSucc j.succ)) := by
    rw [hb, slPerm_swap_castSucc_succ]
  have hx1 : x ≠ 1 := fun h => hxK (fun s => by rw [h, one_mul, mul_one])
  have hzB : a * y * a⁻¹ ∈ Bs := by
    rw [ha']
    exact conj_mem_of_mem_normalizer (hnorm₁ _) hy
  have hbg : b * y * b⁻¹ = y := by
    have e : y * b = b * y := by
      have := hyK (weylRep n F j)
      rwa [← hb] at this
    rw [← e]
    group
  have hbz : b * (a * y * a⁻¹) * b⁻¹ = a * y * a⁻¹ := ggFar_conj_comm_aux_left ha2 hb2 hyu hbg
  obtain ⟨hz₁, hz₂⟩ := ggFar_shape_z h2 hL (by omega) hi hj hy3 ha hb rfl hzB hbz
  have hw₀B : b * x * b⁻¹ ∈ Bs := by
    rw [hb']
    exact conj_mem_of_mem_normalizer (hnorm₂ _) hx
  have hax : a * x * a⁻¹ = x := by
    have e : x * a = a * x := by
      have := hxL (weylRep n F i)
      rwa [← ha] at this
    rw [← e]
    group
  have haw : a * (b * x * b⁻¹) * a⁻¹ = b * x * b⁻¹ := by
    have hax' : a * x * a⁻¹ = x := hax
    exact ggFar_conj_comm_aux_right ha2 hb2 hxu hax'
  obtain ⟨hw₁, hw₂⟩ := ggFar_shape_w0 h2 hL (by omega) hi hj hx2 ha hb rfl hw₀B haw
  set c : X := φ₁ (slLowerBlockHom n F (slPerm h2 (Equiv.swap i j))) with hc
  have hcnorm : c ∈ Subgroup.normalizer (Bs : Set X) := by
    rw [hc, slLowerBlockHom_slPerm_swap]
    exact hnorm₁ _
  have hwB : c * (b * x * b⁻¹) * c⁻¹ ∈ Bs := conj_mem_of_mem_normalizer hcnorm hw₀B
  obtain ⟨hw₃, hw₄⟩ := ggFar_shape_w h2 hL hj hw₁ hw₂ hc rfl
  obtain ⟨k, hk⟩ := ggFar_shape_zpow hL hBp (by omega) hτ'1 hinj hzB hwB hz₁ hz₂ hw₃ hw₄
  have hcb : c = φ₂ (slPerm h2 (Equiv.swap i.castSucc j.castSucc)) := by
    rw [hc, ggFar_c_eq h2 hL.compat]
  have hcbc : c * b * c⁻¹ = b₁ := by
    rw [hcb, hb, hb₁]
    exact ggFar_c_mul_b h2 hi hj (by omega) φ₂
  have hcx : c⁻¹ * x * c = x := by
    have e : x * c = c * x := hxL _
    calc c⁻¹ * x * c = c⁻¹ * (x * c) := by group
      _ = x := by rw [e]; group
  have hw : c * (b * x * b⁻¹) * c⁻¹ = b₁ * x * b₁⁻¹ := by
    have e : b₁ * x * b₁⁻¹ = c * b * (c⁻¹ * x * c) * b⁻¹ * c⁻¹ := by
      rw [← hcbc]; group
    rw [e, hcx]; group
  rw [← hw]
  have hz1 : a * y * a⁻¹ ≠ 1 := fun h => hy1 (conj_eq_one_iff.1 h)
  have hw1 : c * (b * x * b⁻¹) * c⁻¹ ≠ 1 := fun h =>
    hx1 (conj_eq_one_iff.1 (conj_eq_one_iff.1 h))
  exact zpowers_eq_of_zpowers_le_of_prime (hBp _ hwB) hw1 hz1
    (Subgroup.zpowers_le.2 (Subgroup.mem_zpowers_iff.2 ⟨k, hk.symm⟩))

end Zpowers

end CFSG.StandardType
