module

public import CFSG.Timmesfeld.ARS.CaseOANSLFrameMinus

public section

open scoped commutatorElement
open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
open CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.Steinberg CFSG.LieType.RootSystem
open CFSG.Timmesfeld.RankTwo
open Matrix

namespace CFSG.Timmesfeld.ARS.CaseOADeg

open CaseOANSL (tv_comm tv_commute pmat pmat_swap conj_pmat conj_of_commute' cartanB_self
  cartanB_far reflectionB_far reflectionB_A2 minusLong_neg')

section Nodes

abbrev nd0 : Fin (5 - 1) := ⟨0, by omega⟩

abbrev nd1 : Fin (5 - 1) := ⟨1, by omega⟩

abbrev nd2 : Fin (5 - 1) := ⟨2, by omega⟩

abbrev nd3 : Fin (5 - 1) := ⟨3, by omega⟩

abbrev sr (k : Fin (5 - 1)) : Fin (5 - 1) → ℤ := Pi.single k 1

theorem nd_cases (k : Fin (5 - 1)) : k = nd0 ∨ k = nd1 ∨ k = nd2 ∨ k = nd3 := by
  rcases k with ⟨_ | _ | _ | _ | k, hk⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact absurd hk (by omega)

theorem nd0_ne_nd2 : nd0 ≠ nd2 := by decide
theorem nd0_ne_nd3 : nd0 ≠ nd3 := by decide
theorem nd1_ne_nd2 : nd1 ≠ nd2 := by decide
theorem nd1_ne_nd3 : nd1 ≠ nd3 := by decide
theorem pos_or_neg₅ {γ : Fin (5 - 1) → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanB (5 - 1)) ∅) :
    0 < Steinberg.ht γ ∨ 0 < Steinberg.ht (-γ) := by
  have hne := RootSystem.ne_zero_of_mem_roots _ _ hγ
  rcases RootSystem.nonneg_or_nonpos _ _ hγ with h | h
  · exact Or.inl (lt_of_lt_of_le one_pos (RootSystem.one_le_sum_of_nonneg h hne))
  · exact Or.inr (lt_of_lt_of_le one_pos
      (RootSystem.one_le_sum_of_nonneg (neg_nonneg.2 h) (neg_ne_zero.2 hne)))

theorem neg_mem₅ {γ : Fin (5 - 1) → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanB (5 - 1)) ∅) :
    -γ ∈ RootSystem.roots (isFiniteType_cartanB (5 - 1)) ∅ :=
  (Steinberg.RootSystem.ofCartan (isFiniteType_cartanB (5 - 1)) ∅).neg_mem _ hγ

theorem supp_neg {γ : Fin (5 - 1) → ℤ} {i j : Fin (5 - 1)}
    (hs : ∀ l, l ≠ i → l ≠ j → γ l = 0) : ∀ l, l ≠ i → l ≠ j → (-γ) l = 0 := fun l hi hj => by
  rw [Pi.neg_apply, hs l hi hj, neg_zero]

theorem pairA2₅ {i j : Fin (5 - 1)} (hi : i.val + 3 < 5) (hj : j.val = i.val + 1)
    {γ : Fin (5 - 1) → ℤ} (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanB (5 - 1)) ∅)
    (hs : ∀ l, l ≠ i → l ≠ j → γ l = 0) :
    γ = sr i ∨ γ = -sr i ∨ γ = sr j ∨ γ = -sr j ∨ γ = sr i + sr j ∨ γ = -(sr i + sr j) := by
  rcases pos_or_neg₅ hγ with hp | hp
  · rcases minus_pos_roots_A2 (n := 5) hi hj hγ hs hp with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inr (Or.inr (Or.inl rfl))
  · rcases minus_pos_roots_A2 (n := 5) hi hj (neg_mem₅ hγ) (supp_neg hs) hp with h | h | h <;>
      rw [← neg_neg γ, h]
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))

theorem pairB2₅ {γ : Fin (5 - 1) → ℤ} (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanB (5 - 1)) ∅)
    (hs : ∀ l, l ≠ nd2 → l ≠ nd3 → γ l = 0) :
    γ = sr nd2 ∨ γ = -sr nd2 ∨ γ = sr nd3 ∨ γ = -sr nd3 ∨ γ = sr nd2 + sr nd3 ∨
      γ = -(sr nd2 + sr nd3) ∨ γ = sr nd2 + 2 • sr nd3 ∨ γ = -(sr nd2 + 2 • sr nd3) := by
  rcases pos_or_neg₅ hγ with hp | hp
  · rcases minus_pos_roots_B2 (n := 5) (i := nd2) (j := nd3) rfl hγ hs hp with
      rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · rcases minus_pos_roots_B2 (n := 5) (i := nd2) (j := nd3) rfl (neg_mem₅ hγ) (supp_neg hs)
      hp with h | h | h | h <;> rw [← neg_neg γ, h]
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))

theorem pairA1₅ {i j : Fin (5 - 1)} (hij : i.val + 2 ≤ j.val) {γ : Fin (5 - 1) → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanB (5 - 1)) ∅)
    (hs : ∀ l, l ≠ i → l ≠ j → γ l = 0) :
    γ = sr i ∨ γ = -sr i ∨ γ = sr j ∨ γ = -sr j := by
  rcases pos_or_neg₅ hγ with hp | hp
  · rcases minus_pos_roots_A1A1 (n := 5) hij hγ hs hp with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
  · rcases minus_pos_roots_A1A1 (n := 5) hij (neg_mem₅ hγ) (supp_neg hs) hp with h | h <;>
      rw [← neg_neg γ, h]
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr rfl))

end Nodes

section Maps

variable {G : Type} [Group G] {F : Type} [Field F]

@[expose] noncomputable def glueL (φ₀ φ₁ : SpecialLinearGroup (Fin 3) F →* G)
    (L : (Fin (5 - 1) → ℤ) → F → G) : (Fin (5 - 1) → ℤ) → F → G :=
  fun γ x =>
  if γ = sr nd0 then φ₀ (tv 0 1 x) else if γ = -sr nd0 then φ₀ (tv 1 0 x)
  else if γ = sr nd1 then φ₀ (tv 1 2 x) else if γ = -sr nd1 then φ₀ (tv 2 1 x)
  else if γ = sr nd0 + sr nd1 then φ₀ (tv 0 2 x) else if γ = -(sr nd0 + sr nd1) then φ₀ (tv 2 0 x)
  else if γ = sr nd1 + sr nd2 then φ₁ (tv 0 2 x) else if γ = -(sr nd1 + sr nd2) then φ₁ (tv 2 0 x)
  else L γ x

variable (φ₀ φ₁ : SpecialLinearGroup (Fin 3) F →* G) (L : (Fin (5 - 1) → ℤ) → F → G)

theorem glueL_d0 (x : F) : glueL φ₀ φ₁ L (sr nd0) x = φ₀ (tv 0 1 x) := by
  rw [glueL, ite_eq_left rfl]

theorem glueL_nd0 (x : F) : glueL φ₀ φ₁ L (-sr nd0) x = φ₀ (tv 1 0 x) := by
  rw [glueL, ite_eq_right (ne_of_apply_ne' nd0 (by simp)), ite_eq_left rfl]

theorem glueL_d1 (x : F) : glueL φ₀ φ₁ L (sr nd1) x = φ₀ (tv 1 2 x) := by
  rw [glueL, ite_eq_right (ne_of_apply_ne' nd0 (by simp)),
    ite_eq_right (ne_of_apply_ne' nd0 (by simp)), ite_eq_left rfl]

theorem glueL_nd1 (x : F) : glueL φ₀ φ₁ L (-sr nd1) x = φ₀ (tv 2 1 x) := by
  rw [glueL, ite_eq_right (ne_of_apply_ne' nd0 (by simp)),
    ite_eq_right (ne_of_apply_ne' nd0 (by simp)), ite_eq_right (ne_of_apply_ne' nd1 (by simp)),
    ite_eq_left rfl]

theorem glueL_d01 (x : F) : glueL φ₀ φ₁ L (sr nd0 + sr nd1) x = φ₀ (tv 0 2 x) := by
  rw [glueL, ite_eq_right (ne_of_apply_ne' nd1 (by simp)),
    ite_eq_right (ne_of_apply_ne' nd0 (by simp)), ite_eq_right (ne_of_apply_ne' nd0 (by simp)),
    ite_eq_right (ne_of_apply_ne' nd0 (by simp)), ite_eq_left rfl]

theorem glueL_nd01 (x : F) : glueL φ₀ φ₁ L (-(sr nd0 + sr nd1)) x = φ₀ (tv 2 0 x) := by
  rw [glueL, ite_eq_right (ne_of_apply_ne' nd0 (by simp)),
    ite_eq_right (ne_of_apply_ne' nd1 (by simp)), ite_eq_right (ne_of_apply_ne' nd0 (by simp)),
    ite_eq_right (ne_of_apply_ne' nd0 (by simp)), ite_eq_right (ne_of_apply_ne' nd0 (by simp)),
    ite_eq_left rfl]

theorem glueL_d12 (x : F) : glueL φ₀ φ₁ L (sr nd1 + sr nd2) x = φ₁ (tv 0 2 x) := by
  rw [glueL, ite_eq_right (ne_of_apply_ne' nd1 (by simp)),
    ite_eq_right (ne_of_apply_ne' nd1 (by simp)), ite_eq_right (ne_of_apply_ne' nd2 (by simp)),
    ite_eq_right (ne_of_apply_ne' nd1 (by simp)), ite_eq_right (ne_of_apply_ne' nd0 (by simp)),
    ite_eq_right (ne_of_apply_ne' nd1 (by simp)), ite_eq_left rfl]

theorem glueL_nd12 (x : F) : glueL φ₀ φ₁ L (-(sr nd1 + sr nd2)) x = φ₁ (tv 2 0 x) := by
  rw [glueL, ite_eq_right (ne_of_apply_ne' nd1 (by simp)),
    ite_eq_right (ne_of_apply_ne' nd1 (by simp)), ite_eq_right (ne_of_apply_ne' nd1 (by simp)),
    ite_eq_right (ne_of_apply_ne' nd2 (by simp)), ite_eq_right (ne_of_apply_ne' nd1 (by simp)),
    ite_eq_right (ne_of_apply_ne' nd0 (by simp)), ite_eq_right (ne_of_apply_ne' nd1 (by simp)),
    ite_eq_left rfl]

theorem glueL_of_last {γ : Fin (5 - 1) → ℤ} (h0 : γ nd0 = 0) (h1 : γ nd1 = 0) (x : F) :
    glueL φ₀ φ₁ L γ x = L γ x := by
  have hne0 : ∀ v : Fin (5 - 1) → ℤ, v nd0 ≠ 0 → γ ≠ v := fun v hv h =>
    hv (by rw [← h]; exact h0)
  have hne1 : ∀ v : Fin (5 - 1) → ℤ, v nd1 ≠ 0 → γ ≠ v := fun v hv h =>
    hv (by rw [← h]; exact h1)
  rw [glueL, ite_eq_right (hne0 _ (by simp)), ite_eq_right (hne0 _ (by simp)),
    ite_eq_right (hne1 _ (by simp)), ite_eq_right (hne1 _ (by simp)),
    ite_eq_right (hne0 _ (by simp)), ite_eq_right (hne0 _ (by simp)),
    ite_eq_right (hne1 _ (by simp)), ite_eq_right (hne1 _ (by simp))]

theorem glueL_d2 (x : F) : glueL φ₀ φ₁ L (sr nd2) x = L (sr nd2) x :=
  glueL_of_last φ₀ φ₁ L (by simp) (by simp) x

theorem glueL_nd2 (x : F) : glueL φ₀ φ₁ L (-sr nd2) x = L (-sr nd2) x :=
  glueL_of_last φ₀ φ₁ L (by simp) (by simp) x

theorem glueL_add (hL : ∀ γ x y, L γ (x + y) = L γ x * L γ y) (γ : Fin (5 - 1) → ℤ) (x y : F) :
    glueL φ₀ φ₁ L γ (x + y) = glueL φ₀ φ₁ L γ x * glueL φ₀ φ₁ L γ y := by
  unfold glueL
  split_ifs <;> first | rw [CaseOANSL.tv_add, map_mul] | exact hL γ x y

end Maps

section Hyp

variable {G : Type} [Group G] {F : Type} [Field F] {b c : F}

structure GlueHyp (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (φ₀ φ₁ : SpecialLinearGroup (Fin 3) F →* G) (ρ₀ ρ₁ : SpecialLinearGroup (Fin 2) F →* G)
    (L : (Fin (5 - 1) → ℤ) → F → G) (S : (Fin (5 - 1) → ℤ) → (Fin 2 → F) → G)
    (w : Fin (5 - 1) → G) (V₁ : Subgroup G) : Prop where
  φ₀01 : ∀ x, φ₀ (tv 0 1 x) = ρ₀ (tv 0 1 x)
  φ₀10 : ∀ x, φ₀ (tv 1 0 x) = ρ₀ (tv 1 0 x)
  φ₀12 : ∀ x, φ₀ (tv 1 2 x) = ρ₁ (tv 0 1 x)
  φ₀21 : ∀ x, φ₀ (tv 2 1 x) = ρ₁ (tv 1 0 x)
  φ₁01 : ∀ x, φ₁ (tv 0 1 x) = ρ₁ (tv 0 1 x)
  φ₁10 : ∀ x, φ₁ (tv 1 0 x) = ρ₁ (tv 1 0 x)
  φ₁12 : ∀ x, φ₁ (tv 1 2 x) = L (sr nd2) x
  φ₁21 : ∀ x, φ₁ (tv 2 1 x) = L (-sr nd2) x
  addL : ∀ γ x y, L γ (x + y) = L γ x * L γ y
  addS : ∀ γ p q, S γ (p + q) = S γ p * S γ q
  commB2 : ∀ (p : Fin 2 → F) (s : F), ⁅S (sr nd3) p, L (sr nd2) s⁆ =
    S (sr nd2 + sr nd3) (s • p) * L (sr nd2 + 2 • sr nd3) (s * planeNorm b c p)
  commB2' : ∀ p q : Fin 2 → F, ⁅S (sr nd3) p, S (sr nd2 + sr nd3) q⁆ =
    L (sr nd2 + 2 • sr nd3) (polarPlane b c p q)
  commuteB2_b_2ab : ∀ (p : Fin 2 → F) (s : F),
    Commute (S (sr nd3) p) (L (sr nd2 + 2 • sr nd3) s)
  commuteB2_ab_2ab : ∀ (p : Fin 2 → F) (s : F),
    Commute (S (sr nd2 + sr nd3) p) (L (sr nd2 + 2 • sr nd3) s)
  commuteB2_ab_a : ∀ (p : Fin 2 → F) (s : F), Commute (S (sr nd2 + sr nd3) p) (L (sr nd2) s)
  commuteB2_2ab_a : ∀ s t : F, Commute (L (sr nd2 + 2 • sr nd3) s) (L (sr nd2) t)
  weylV : ∀ k, (k = nd2 ∨ k = nd3) → ∀ γ ∈ pairRoots (minusDatum 5 hirr) nd2 nd3,
    (MinusLong 5 γ → ∀ a, w k * L γ a * (w k)⁻¹ = L (reflection (cartanB (5 - 1)) k γ) a) ∧
    (MinusShort 5 γ → ∀ p, w k * S γ p * (w k)⁻¹ = S (reflection (cartanB (5 - 1)) k γ)
      (if k.val + 2 = 5 then planeRefl b c planeOne p else p))
  w₂_eq : w nd2 = L (sr nd2) 1 * L (-sr nd2) 1 * L (sr nd2) 1
  w₃_eq : w nd3 = S (sr nd3) planeOne * S (-sr nd3) planeOne * S (sr nd3) planeOne
  memL : ∀ γ x, L γ x ∈ V₁
  memS : ∀ γ p, S γ p ∈ V₁
  V : ∀ g, ∀ y ∈ V₁, Commute (ρ₀ g) y
  E : ∀ g p, Commute (ρ₁ g) (S (sr nd3) p) ∧ Commute (ρ₁ g) (S (-sr nd3) p)
  rank₂ : ∃ Θ : SpecialLinearGroup (Fin 2) F →* G,
    (∀ x, Θ (sl2Upper x) = L (sr nd2) x) ∧ ∀ x, Θ (sl2Lower x) = L (-sr nd2) x
  genV : V₁ ≤ Subgroup.closure (Set.range (L (sr nd2)) ∪ Set.range (L (-sr nd2)) ∪
    Set.range (S (sr nd3)) ∪ Set.range (S (-sr nd3)))

variable [CharP F 2]

@[expose] noncomputable def glueN (ρ₀ ρ₁ : SpecialLinearGroup (Fin 2) F →* G)
    (w : Fin (5 - 1) → G) (k : Fin (5 - 1)) : G :=
  if k.val = 0 then ρ₀ (pmat (Equiv.swap 0 1)) else if k.val = 1 then ρ₁ (pmat (Equiv.swap 0 1))
  else w k

variable {hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0} {φ₀ φ₁ : SpecialLinearGroup (Fin 3) F →* G}
  {ρ₀ ρ₁ : SpecialLinearGroup (Fin 2) F →* G} {L : (Fin (5 - 1) → ℤ) → F → G}
  {S : (Fin (5 - 1) → ℤ) → (Fin 2 → F) → G} {w : Fin (5 - 1) → G} {V₁ : Subgroup G}
  (H : GlueHyp hirr φ₀ φ₁ ρ₀ ρ₁ L S w V₁)
include H

omit H in
theorem glueN_zero : glueN ρ₀ ρ₁ w nd0 = ρ₀ (pmat (Equiv.swap 0 1)) := by
  rw [glueN, ite_eq_left rfl]

omit H in
theorem glueN_one : glueN ρ₀ ρ₁ w nd1 = ρ₁ (pmat (Equiv.swap 0 1)) := by
  rw [glueN, ite_eq_right (show ¬ (1 = 0) by omega), ite_eq_left rfl]

omit H in
theorem glueN_two : glueN ρ₀ ρ₁ w nd2 = w nd2 := by
  rw [glueN, ite_eq_right (show ¬ (2 = 0) by omega), ite_eq_right (show ¬ (2 = 1) by omega)]

omit H in
theorem glueN_three : glueN ρ₀ ρ₁ w nd3 = w nd3 := by
  rw [glueN, ite_eq_right (show ¬ (3 = 0) by omega), ite_eq_right (show ¬ (3 = 1) by omega)]

omit [CharP F 2] in
theorem GlueHyp.v_d0 (x : F) : glueL φ₀ φ₁ L (sr nd0) x = ρ₀ (tv 0 1 x) :=
  (glueL_d0 φ₀ φ₁ L x).trans (H.φ₀01 x)

omit [CharP F 2] in
theorem GlueHyp.v_nd0 (x : F) : glueL φ₀ φ₁ L (-sr nd0) x = ρ₀ (tv 1 0 x) :=
  (glueL_nd0 φ₀ φ₁ L x).trans (H.φ₀10 x)

omit [CharP F 2] in
theorem GlueHyp.v_d1 (x : F) : glueL φ₀ φ₁ L (sr nd1) x = ρ₁ (tv 0 1 x) :=
  (glueL_d1 φ₀ φ₁ L x).trans (H.φ₀12 x)

omit [CharP F 2] in
theorem GlueHyp.v_nd1 (x : F) : glueL φ₀ φ₁ L (-sr nd1) x = ρ₁ (tv 1 0 x) :=
  (glueL_nd1 φ₀ φ₁ L x).trans (H.φ₀21 x)

omit [CharP F 2] in
theorem GlueHyp.w_d1 (x : F) : glueL φ₀ φ₁ L (sr nd1) x = φ₁ (tv 0 1 x) :=
  (H.v_d1 x).trans (H.φ₁01 x).symm

omit [CharP F 2] in
theorem GlueHyp.w_nd1 (x : F) : glueL φ₀ φ₁ L (-sr nd1) x = φ₁ (tv 1 0 x) :=
  (H.v_nd1 x).trans (H.φ₁10 x).symm

omit [CharP F 2] in
theorem GlueHyp.w_d2 (x : F) : glueL φ₀ φ₁ L (sr nd2) x = φ₁ (tv 1 2 x) :=
  (glueL_d2 φ₀ φ₁ L x).trans (H.φ₁12 x).symm

omit [CharP F 2] in
theorem GlueHyp.w_nd2 (x : F) : glueL φ₀ φ₁ L (-sr nd2) x = φ₁ (tv 2 1 x) :=
  (glueL_nd2 φ₀ φ₁ L x).trans (H.φ₁21 x).symm

theorem GlueHyp.glueN_zero_eq : glueN ρ₀ ρ₁ w nd0 = φ₀ (pmat (Equiv.swap 0 1)) := by
  rw [glueN_zero, pmat_swap (show (0 : Fin 2) ≠ 1 by decide),
    pmat_swap (show (0 : Fin 3) ≠ 1 by decide), map_mul, map_mul, map_mul, map_mul, H.φ₀01, H.φ₀10]

theorem GlueHyp.glueN_one_eq₀ : glueN ρ₀ ρ₁ w nd1 = φ₀ (pmat (Equiv.swap 1 2)) := by
  rw [glueN_one, pmat_swap (show (0 : Fin 2) ≠ 1 by decide),
    pmat_swap (show (1 : Fin 3) ≠ 2 by decide), map_mul, map_mul, map_mul, map_mul, H.φ₀12, H.φ₀21]

theorem GlueHyp.glueN_one_eq₁ : glueN ρ₀ ρ₁ w nd1 = φ₁ (pmat (Equiv.swap 0 1)) := by
  rw [glueN_one, pmat_swap (show (0 : Fin 2) ≠ 1 by decide),
    pmat_swap (show (0 : Fin 3) ≠ 1 by decide), map_mul, map_mul, map_mul, map_mul, H.φ₁01, H.φ₁10]

theorem GlueHyp.glueN_two_eq : glueN ρ₀ ρ₁ w nd2 = φ₁ (pmat (Equiv.swap 1 2)) := by
  rw [glueN_two, H.w₂_eq, pmat_swap (show (1 : Fin 3) ≠ 2 by decide), map_mul, map_mul, H.φ₁12,
    H.φ₁21]

omit [CharP F 2] in
theorem GlueHyp.mem_w₂ : w nd2 ∈ V₁ := by
  rw [H.w₂_eq]
  exact mul_mem (mul_mem (H.memL _ _) (H.memL _ _)) (H.memL _ _)

omit [CharP F 2] in
theorem GlueHyp.mem_w₃ : w nd3 ∈ V₁ := by
  rw [H.w₃_eq]
  exact mul_mem (mul_mem (H.memS _ _) (H.memS _ _)) (H.memS _ _)

omit [CharP F 2] in
theorem GlueHyp.commute_w₃ (g : SpecialLinearGroup (Fin 2) F) : Commute (ρ₁ g) (w nd3) := by
  rw [H.w₃_eq]
  exact (((H.E g _).1).mul_right (H.E g _).2).mul_right (H.E g _).1

end Hyp

section Weyl

variable {G : Type} [Group G] {F : Type} [Field F] [CharP F 2] {b c : F}
  {hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0} {φ₀ φ₁ : SpecialLinearGroup (Fin 3) F →* G}
  {ρ₀ ρ₁ : SpecialLinearGroup (Fin 2) F →* G} {L : (Fin (5 - 1) → ℤ) → F → G}
  {S : (Fin (5 - 1) → ℤ) → (Fin 2 → F) → G} {w : Fin (5 - 1) → G} {V₁ : Subgroup G}
  (H : GlueHyp hirr φ₀ φ₁ ρ₀ ρ₁ L S w V₁)
include H

omit H in
theorem refl01 :
    reflection (cartanB (5 - 1)) nd0 (sr nd0) = -sr nd0 ∧
    reflection (cartanB (5 - 1)) nd0 (sr nd1) = sr nd0 + sr nd1 ∧
    reflection (cartanB (5 - 1)) nd0 (sr nd0 + sr nd1) = sr nd1 ∧
    reflection (cartanB (5 - 1)) nd1 (sr nd0) = sr nd0 + sr nd1 ∧
    reflection (cartanB (5 - 1)) nd1 (sr nd1) = -sr nd1 ∧
    reflection (cartanB (5 - 1)) nd1 (sr nd0 + sr nd1) = sr nd0 :=
  reflectionB_A2 (N := 5 - 1) (p := nd0) (q := nd1) rfl (by simp)

omit H in
theorem refl12 :
    reflection (cartanB (5 - 1)) nd1 (sr nd1) = -sr nd1 ∧
    reflection (cartanB (5 - 1)) nd1 (sr nd2) = sr nd1 + sr nd2 ∧
    reflection (cartanB (5 - 1)) nd1 (sr nd1 + sr nd2) = sr nd2 ∧
    reflection (cartanB (5 - 1)) nd2 (sr nd1) = sr nd1 + sr nd2 ∧
    reflection (cartanB (5 - 1)) nd2 (sr nd2) = -sr nd2 ∧
    reflection (cartanB (5 - 1)) nd2 (sr nd1 + sr nd2) = sr nd1 :=
  reflectionB_A2 (N := 5 - 1) (p := nd1) (q := nd2) rfl (by simp)

omit H in
theorem refl_self (k : Fin (5 - 1)) : reflection (cartanB (5 - 1)) k (sr k) = -sr k :=
  reflection_single_self (cartanB_self _)

theorem GlueHyp.weyl01 {γ : Fin (5 - 1) → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanB (5 - 1)) ∅)
    (hs : ∀ l, l ≠ nd0 → l ≠ nd1 → γ l = 0) {k : Fin (5 - 1)} (hk : k = nd0 ∨ k = nd1) (x : F) :
    glueN ρ₀ ρ₁ w k * glueL φ₀ φ₁ L γ x * (glueN ρ₀ ρ₁ w k)⁻¹ =
      glueL φ₀ φ₁ L (reflection (cartanB (5 - 1)) k γ) x := by
  obtain ⟨r00, r01, r0s, r10, r11, r1s⟩ := refl01
  rcases hk with rfl | rfl
  · rw [H.glueN_zero_eq]
    rcases pairA2₅ (i := nd0) (j := nd1) (by simp) rfl hγ hs with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [r00, glueL_d0, glueL_nd0]
      exact conj_pmat φ₀ _ (by decide) (by decide) (by decide) x
    · rw [map_neg, r00, neg_neg, glueL_nd0, glueL_d0]
      exact conj_pmat φ₀ _ (by decide) (by decide) (by decide) x
    · rw [r01, glueL_d1, glueL_d01]
      exact conj_pmat φ₀ _ (by decide) (by decide) (by decide) x
    · rw [map_neg, r01, glueL_nd1, glueL_nd01]
      exact conj_pmat φ₀ _ (by decide) (by decide) (by decide) x
    · rw [r0s, glueL_d01, glueL_d1]
      exact conj_pmat φ₀ _ (by decide) (by decide) (by decide) x
    · rw [map_neg, r0s, glueL_nd01, glueL_nd1]
      exact conj_pmat φ₀ _ (by decide) (by decide) (by decide) x
  · rw [H.glueN_one_eq₀]
    rcases pairA2₅ (i := nd0) (j := nd1) (by simp) rfl hγ hs with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [r10, glueL_d0, glueL_d01]
      exact conj_pmat φ₀ _ (by decide) (by decide) (by decide) x
    · rw [map_neg, r10, glueL_nd0, glueL_nd01]
      exact conj_pmat φ₀ _ (by decide) (by decide) (by decide) x
    · rw [r11, glueL_d1, glueL_nd1]
      exact conj_pmat φ₀ _ (by decide) (by decide) (by decide) x
    · rw [map_neg, r11, neg_neg, glueL_nd1, glueL_d1]
      exact conj_pmat φ₀ _ (by decide) (by decide) (by decide) x
    · rw [r1s, glueL_d01, glueL_d0]
      exact conj_pmat φ₀ _ (by decide) (by decide) (by decide) x
    · rw [map_neg, r1s, glueL_nd01, glueL_nd0]
      exact conj_pmat φ₀ _ (by decide) (by decide) (by decide) x

theorem GlueHyp.weyl12 {γ : Fin (5 - 1) → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanB (5 - 1)) ∅)
    (hs : ∀ l, l ≠ nd1 → l ≠ nd2 → γ l = 0) {k : Fin (5 - 1)} (hk : k = nd1 ∨ k = nd2) (x : F) :
    glueN ρ₀ ρ₁ w k * glueL φ₀ φ₁ L γ x * (glueN ρ₀ ρ₁ w k)⁻¹ =
      glueL φ₀ φ₁ L (reflection (cartanB (5 - 1)) k γ) x := by
  obtain ⟨r11, r12, r1s, r21, r22, r2s⟩ := refl12
  rcases hk with rfl | rfl
  · rw [H.glueN_one_eq₁]
    rcases pairA2₅ (i := nd1) (j := nd2) (by simp) rfl hγ hs with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [r11, H.w_d1, H.w_nd1]
      exact conj_pmat φ₁ _ (by decide) (by decide) (by decide) x
    · rw [map_neg, r11, neg_neg, H.w_nd1, H.w_d1]
      exact conj_pmat φ₁ _ (by decide) (by decide) (by decide) x
    · rw [r12, H.w_d2, glueL_d12]
      exact conj_pmat φ₁ _ (by decide) (by decide) (by decide) x
    · rw [map_neg, r12, H.w_nd2, glueL_nd12]
      exact conj_pmat φ₁ _ (by decide) (by decide) (by decide) x
    · rw [r1s, glueL_d12, H.w_d2]
      exact conj_pmat φ₁ _ (by decide) (by decide) (by decide) x
    · rw [map_neg, r1s, glueL_nd12, H.w_nd2]
      exact conj_pmat φ₁ _ (by decide) (by decide) (by decide) x
  · rw [H.glueN_two_eq]
    rcases pairA2₅ (i := nd1) (j := nd2) (by simp) rfl hγ hs with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [r21, H.w_d1, glueL_d12]
      exact conj_pmat φ₁ _ (by decide) (by decide) (by decide) x
    · rw [map_neg, r21, H.w_nd1, glueL_nd12]
      exact conj_pmat φ₁ _ (by decide) (by decide) (by decide) x
    · rw [r22, H.w_d2, H.w_nd2]
      exact conj_pmat φ₁ _ (by decide) (by decide) (by decide) x
    · rw [map_neg, r22, neg_neg, H.w_nd2, H.w_d2]
      exact conj_pmat φ₁ _ (by decide) (by decide) (by decide) x
    · rw [r2s, glueL_d12, H.w_d1]
      exact conj_pmat φ₁ _ (by decide) (by decide) (by decide) x
    · rw [map_neg, r2s, glueL_nd12, H.w_nd1]
      exact conj_pmat φ₁ _ (by decide) (by decide) (by decide) x

omit H [CharP F 2] in
theorem mem_pairRoots23 {k : Fin (5 - 1)} (hk : k = nd2 ∨ k = nd3) :
    sr k ∈ pairRoots (minusDatum 5 hirr) nd2 nd3 := by
  refine ⟨?_, fun l h2 h3 => ?_⟩
  · rcases hk with rfl | rfl
    · exact (minusLong_single (n := 5) (k := nd2) (by decide)).mem_roots
    · exact (minusShort_single (n := 5) (k := nd3) (by decide)).mem_roots
  · rcases hk with rfl | rfl
    · exact Pi.single_eq_of_ne h2 1
    · exact Pi.single_eq_of_ne h3 1

omit H [CharP F 2] in
theorem mem_pairRoots23' {k : Fin (5 - 1)} (hk : k = nd2 ∨ k = nd3) :
    -sr k ∈ pairRoots (minusDatum 5 hirr) nd2 nd3 := by
  refine ⟨?_, fun l h2 h3 => ?_⟩
  · rcases hk with rfl | rfl
    · exact (minusLong_neg_single (n := 5) (k := nd2) (by decide)).mem_roots
    · exact (minusShort_neg_single (n := 5) (k := nd3) (by decide)).mem_roots
  · change -(sr k l) = 0
    rw [neg_eq_zero]
    rcases hk with rfl | rfl
    · exact Pi.single_eq_of_ne h2 1
    · exact Pi.single_eq_of_ne h3 1

theorem GlueHyp.weyl02 {γ : Fin (5 - 1) → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanB (5 - 1)) ∅)
    (hs : ∀ l, l ≠ nd0 → l ≠ nd2 → γ l = 0) {k : Fin (5 - 1)} (hk : k = nd0 ∨ k = nd2) (x : F) :
    glueN ρ₀ ρ₁ w k * glueL φ₀ φ₁ L γ x * (glueN ρ₀ ρ₁ w k)⁻¹ =
      glueL φ₀ φ₁ L (reflection (cartanB (5 - 1)) k γ) x := by
  obtain ⟨h02, h20⟩ := cartanB_far (N := 5 - 1) (i := nd0) (j := nd2) (by simp)
  have hL2 : MinusLong 5 (sr nd2) := minusLong_single (n := 5) (by simp)
  rcases pairA1₅ (i := nd0) (j := nd2) (by simp) hγ hs with rfl | rfl | rfl | rfl
  · rcases hk with rfl | rfl
    · rw [refl_self, H.v_d0, H.v_nd0, glueN_zero]
      exact conj_pmat ρ₀ _ (by decide) (by decide) (by decide) x
    · rw [reflectionB_far h20, H.v_d0, glueN_two]
      exact conj_of_commute' (H.V _ _ H.mem_w₂).symm
  · rcases hk with rfl | rfl
    · rw [map_neg, refl_self, neg_neg, H.v_nd0, H.v_d0, glueN_zero]
      exact conj_pmat ρ₀ _ (by decide) (by decide) (by decide) x
    · rw [map_neg, reflectionB_far h20, H.v_nd0, glueN_two]
      exact conj_of_commute' (H.V _ _ H.mem_w₂).symm
  · rcases hk with rfl | rfl
    · rw [reflectionB_far h02, glueN_zero, glueL_d2]
      exact conj_of_commute' (H.V _ _ (H.memL _ _))
    · have h := (H.weylV nd2 (Or.inl rfl) (sr nd2) (mem_pairRoots23 (Or.inl rfl))).1 hL2 x
      rw [glueN_two, glueL_d2, h, refl_self, glueL_nd2]
  · rcases hk with rfl | rfl
    · rw [map_neg, reflectionB_far h02, glueN_zero, glueL_nd2]
      exact conj_of_commute' (H.V _ _ (H.memL _ _))
    · have h := (H.weylV nd2 (Or.inl rfl) (-sr nd2) (mem_pairRoots23' (Or.inl rfl))).1
        (minusLong_neg' hL2) x
      rw [glueN_two, glueL_nd2, h, map_neg, refl_self, neg_neg, glueL_d2]

theorem GlueHyp.weyl03 {γ : Fin (5 - 1) → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanB (5 - 1)) ∅)
    (hs : ∀ l, l ≠ nd0 → l ≠ nd3 → γ l = 0) {k : Fin (5 - 1)} (hk : k = nd0 ∨ k = nd3) :
    (MinusLong 5 γ → ∀ x, glueN ρ₀ ρ₁ w k * glueL φ₀ φ₁ L γ x * (glueN ρ₀ ρ₁ w k)⁻¹ =
      glueL φ₀ φ₁ L (reflection (cartanB (5 - 1)) k γ) x) ∧
    (MinusShort 5 γ → ∀ p, glueN ρ₀ ρ₁ w k * S γ p * (glueN ρ₀ ρ₁ w k)⁻¹ =
      S (reflection (cartanB (5 - 1)) k γ)
        (if k.val + 2 = 5 then planeRefl b c planeOne p else p)) := by
  obtain ⟨h03, h30⟩ := cartanB_far (N := 5 - 1) (i := nd0) (j := nd3) (by simp)
  have hd0 : MinusLong 5 (sr nd0) := minusLong_single (n := 5) (by simp)
  have hS3 : MinusShort 5 (sr nd3) := minusShort_single (n := 5) (by simp)
  rcases pairA1₅ (i := nd0) (j := nd3) (by simp) hγ hs with rfl | rfl | rfl | rfl
  · refine ⟨fun _ x => ?_, fun h => absurd hd0 h.not_long⟩
    rcases hk with rfl | rfl
    · rw [refl_self, H.v_d0, H.v_nd0, glueN_zero]
      exact conj_pmat ρ₀ _ (by decide) (by decide) (by decide) x
    · rw [reflectionB_far h30, H.v_d0, glueN_three]
      exact conj_of_commute' (H.V _ _ H.mem_w₃).symm
  · refine ⟨fun _ x => ?_, fun h => absurd (minusLong_neg' hd0) h.not_long⟩
    rcases hk with rfl | rfl
    · rw [map_neg, refl_self, neg_neg, H.v_nd0, H.v_d0, glueN_zero]
      exact conj_pmat ρ₀ _ (by decide) (by decide) (by decide) x
    · rw [map_neg, reflectionB_far h30, H.v_nd0, glueN_three]
      exact conj_of_commute' (H.V _ _ H.mem_w₃).symm
  · refine ⟨fun h => absurd h hS3.not_long, fun _ p => ?_⟩
    rcases hk with rfl | rfl
    · rw [reflectionB_far h03, glueN_zero, ite_eq_right (by simp)]
      exact conj_of_commute' (H.V _ _ (H.memS _ _))
    · rw [glueN_three]
      exact (H.weylV nd3 (Or.inr rfl) (sr nd3) (mem_pairRoots23 (Or.inr rfl))).2 hS3 p
  · refine ⟨fun h => absurd h (minusShort_neg_single (n := 5) (k := nd3) (by simp)).not_long,
      fun _ p => ?_⟩
    rcases hk with rfl | rfl
    · rw [map_neg, reflectionB_far h03, glueN_zero, ite_eq_right (by simp)]
      exact conj_of_commute' (H.V _ _ (H.memS _ _))
    · rw [glueN_three]
      exact (H.weylV nd3 (Or.inr rfl) (-sr nd3) (mem_pairRoots23' (Or.inr rfl))).2
        (minusShort_neg_single (n := 5) (k := nd3) (by simp)) p

theorem GlueHyp.weyl13 {γ : Fin (5 - 1) → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanB (5 - 1)) ∅)
    (hs : ∀ l, l ≠ nd1 → l ≠ nd3 → γ l = 0) {k : Fin (5 - 1)} (hk : k = nd1 ∨ k = nd3) :
    (MinusLong 5 γ → ∀ x, glueN ρ₀ ρ₁ w k * glueL φ₀ φ₁ L γ x * (glueN ρ₀ ρ₁ w k)⁻¹ =
      glueL φ₀ φ₁ L (reflection (cartanB (5 - 1)) k γ) x) ∧
    (MinusShort 5 γ → ∀ p, glueN ρ₀ ρ₁ w k * S γ p * (glueN ρ₀ ρ₁ w k)⁻¹ =
      S (reflection (cartanB (5 - 1)) k γ)
        (if k.val + 2 = 5 then planeRefl b c planeOne p else p)) := by
  obtain ⟨h13, h31⟩ := cartanB_far (N := 5 - 1) (i := nd1) (j := nd3) (by simp)
  have hd1 : MinusLong 5 (sr nd1) := minusLong_single (n := 5) (by simp)
  have hS3 : MinusShort 5 (sr nd3) := minusShort_single (n := 5) (by simp)
  rcases pairA1₅ (i := nd1) (j := nd3) (by simp) hγ hs with rfl | rfl | rfl | rfl
  · refine ⟨fun _ x => ?_, fun h => absurd hd1 h.not_long⟩
    rcases hk with rfl | rfl
    · rw [refl_self, H.v_d1, H.v_nd1, glueN_one]
      exact conj_pmat ρ₁ _ (by decide) (by decide) (by decide) x
    · rw [reflectionB_far h31, H.v_d1, glueN_three]
      exact conj_of_commute' (H.commute_w₃ _).symm
  · refine ⟨fun _ x => ?_, fun h => absurd (minusLong_neg' hd1) h.not_long⟩
    rcases hk with rfl | rfl
    · rw [map_neg, refl_self, neg_neg, H.v_nd1, H.v_d1, glueN_one]
      exact conj_pmat ρ₁ _ (by decide) (by decide) (by decide) x
    · rw [map_neg, reflectionB_far h31, H.v_nd1, glueN_three]
      exact conj_of_commute' (H.commute_w₃ _).symm
  · refine ⟨fun h => absurd h hS3.not_long, fun _ p => ?_⟩
    rcases hk with rfl | rfl
    · rw [reflectionB_far h13, glueN_one, ite_eq_right (by simp)]
      exact conj_of_commute' (H.E _ p).1
    · rw [glueN_three]
      exact (H.weylV nd3 (Or.inr rfl) (sr nd3) (mem_pairRoots23 (Or.inr rfl))).2 hS3 p
  · refine ⟨fun h => absurd h (minusShort_neg_single (n := 5) (k := nd3) (by simp)).not_long,
      fun _ p => ?_⟩
    rcases hk with rfl | rfl
    · rw [map_neg, reflectionB_far h13, glueN_one, ite_eq_right (by simp)]
      exact conj_of_commute' (H.E _ p).2
    · rw [glueN_three]
      exact (H.weylV nd3 (Or.inr rfl) (-sr nd3) (mem_pairRoots23' (Or.inr rfl))).2
        (minusShort_neg_single (n := 5) (k := nd3) (by simp)) p

omit H in
theorem reflection_apply_of_ne {γ : Fin (5 - 1) → ℤ} {k l : Fin (5 - 1)} (hkl : l ≠ k) :
    reflection (cartanB (5 - 1)) k γ l = γ l := by
  rw [reflection_apply]
  simp [hkl]

theorem GlueHyp.weyl23 {γ : Fin (5 - 1) → ℤ} (hγ : γ ∈ pairRoots (minusDatum 5 hirr) nd2 nd3)
    {k : Fin (5 - 1)} (hk : k = nd2 ∨ k = nd3) :
    (MinusLong 5 γ → ∀ x, glueN ρ₀ ρ₁ w k * glueL φ₀ φ₁ L γ x * (glueN ρ₀ ρ₁ w k)⁻¹ =
      glueL φ₀ φ₁ L (reflection (cartanB (5 - 1)) k γ) x) ∧
    (MinusShort 5 γ → ∀ p, glueN ρ₀ ρ₁ w k * S γ p * (glueN ρ₀ ρ₁ w k)⁻¹ =
      S (reflection (cartanB (5 - 1)) k γ)
        (if k.val + 2 = 5 then planeRefl b c planeOne p else p)) := by
  have h0 : γ nd0 = 0 := hγ.2 nd0 nd0_ne_nd2 nd0_ne_nd3
  have h1 : γ nd1 = 0 := hγ.2 nd1 nd1_ne_nd2 nd1_ne_nd3
  have hk0 : nd0 ≠ k := by rcases hk with rfl | rfl <;> decide
  have hk1 : nd1 ≠ k := by rcases hk with rfl | rfl <;> decide
  have hN : glueN ρ₀ ρ₁ w k = w k := by
    rcases hk with rfl | rfl
    · exact glueN_two
    · exact glueN_three
  rw [hN]
  refine ⟨fun hL x => ?_, fun hS p => (H.weylV k hk γ hγ).2 hS p⟩
  rw [glueL_of_last φ₀ φ₁ L h0 h1, glueL_of_last φ₀ φ₁ L
    ((reflection_apply_of_ne hk0).trans h0) ((reflection_apply_of_ne hk1).trans h1)]
  exact (H.weylV k hk γ hγ).1 hL x

theorem GlueHyp.weyl (i j : Fin (5 - 1)) (hij : i.val < j.val) :
    ∃ ñ : Fin (5 - 1) → G, ∀ k, (k = i ∨ k = j) →
      ∀ γ ∈ pairRoots (minusDatum 5 hirr) i j,
        (MinusLong 5 γ → ∀ a, ñ k * glueL φ₀ φ₁ L γ a * (ñ k)⁻¹ =
          glueL φ₀ φ₁ L ((ΦMinus 5 hirr).refl k γ) a) ∧
        (MinusShort 5 γ → ∀ p, ñ k * S γ p * (ñ k)⁻¹ =
          S ((ΦMinus 5 hirr).refl k γ)
            (if k.val + 2 = 5 then planeRefl b c planeOne p else p)) := by
  refine ⟨glueN ρ₀ ρ₁ w, fun k hk γ hγ => ?_⟩
  have hγ' := hγ
  obtain ⟨hγR, hγs⟩ := hγ
  change γ ∈ RootSystem.roots (isFiniteType_cartanB (5 - 1)) ∅ at hγR
  change (MinusLong 5 γ → ∀ a, glueN ρ₀ ρ₁ w k * glueL φ₀ φ₁ L γ a * (glueN ρ₀ ρ₁ w k)⁻¹ =
      glueL φ₀ φ₁ L (reflection (cartanB (5 - 1)) k γ) a) ∧
    (MinusShort 5 γ → ∀ p, glueN ρ₀ ρ₁ w k * S γ p * (glueN ρ₀ ρ₁ w k)⁻¹ =
      S (reflection (cartanB (5 - 1)) k γ)
        (if k.val + 2 = 5 then planeRefl b c planeOne p else p))
  have hL01 : ∀ {γ : Fin (5 - 1) → ℤ}, γ ∈ RootSystem.roots (isFiniteType_cartanB (5 - 1)) ∅ →
      (∀ l, l ≠ nd0 → l ≠ nd1 → γ l = 0) → ¬ MinusShort 5 γ := fun hR hs h => by
    rcases pairA2₅ (i := nd0) (j := nd1) (by simp) rfl hR hs with
      rfl | rfl | rfl | rfl | rfl | rfl
    · exact h.not_long (minusLong_single (n := 5) (by simp))
    · exact h.not_long (minusLong_neg_single (n := 5) (by simp))
    · exact h.not_long (minusLong_single (n := 5) (by simp))
    · exact h.not_long (minusLong_neg_single (n := 5) (by simp))
    · exact h.not_long (minusLong_A2sum (n := 5) (i := nd0) (by simp))
    · exact h.not_long (minusLong_neg' (minusLong_A2sum (n := 5) (i := nd0) (by simp)))
  have hL12 : ∀ {γ : Fin (5 - 1) → ℤ}, γ ∈ RootSystem.roots (isFiniteType_cartanB (5 - 1)) ∅ →
      (∀ l, l ≠ nd1 → l ≠ nd2 → γ l = 0) → ¬ MinusShort 5 γ := fun hR hs h => by
    rcases pairA2₅ (i := nd1) (j := nd2) (by simp) rfl hR hs with
      rfl | rfl | rfl | rfl | rfl | rfl
    · exact h.not_long (minusLong_single (n := 5) (by simp))
    · exact h.not_long (minusLong_neg_single (n := 5) (by simp))
    · exact h.not_long (minusLong_single (n := 5) (by simp))
    · exact h.not_long (minusLong_neg_single (n := 5) (by simp))
    · exact h.not_long (minusLong_A2sum (n := 5) (i := nd1) (by simp))
    · exact h.not_long (minusLong_neg' (minusLong_A2sum (n := 5) (i := nd1) (by simp)))
  have hL02 : ∀ {γ : Fin (5 - 1) → ℤ}, γ ∈ RootSystem.roots (isFiniteType_cartanB (5 - 1)) ∅ →
      (∀ l, l ≠ nd0 → l ≠ nd2 → γ l = 0) → ¬ MinusShort 5 γ := fun hR hs h => by
    rcases pairA1₅ (i := nd0) (j := nd2) (by simp) hR hs with rfl | rfl | rfl | rfl
    · exact h.not_long (minusLong_single (n := 5) (by simp))
    · exact h.not_long (minusLong_neg_single (n := 5) (by simp))
    · exact h.not_long (minusLong_single (n := 5) (by simp))
    · exact h.not_long (minusLong_neg_single (n := 5) (by simp))
  rcases nd_cases i with rfl | rfl | rfl | rfl <;> rcases nd_cases j with rfl | rfl | rfl | rfl <;>
    first
    | exact absurd hij (by decide)
    | exact ⟨fun _ a => H.weyl01 hγR hγs hk a, fun hS => absurd hS (hL01 hγR hγs)⟩
    | exact ⟨fun _ a => H.weyl12 hγR hγs hk a, fun hS => absurd hS (hL12 hγR hγs)⟩
    | exact ⟨fun _ a => H.weyl02 hγR hγs hk a, fun hS => absurd hS (hL02 hγR hγs)⟩
    | exact H.weyl03 hγR hγs hk
    | exact H.weyl13 hγR hγs hk
    | exact H.weyl23 hγ' hk

end Weyl

section Main

variable {G : Type} [Group G] {F : Type} [Field F] [CharP F 2] {b c : F}
  {hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0} {φ₀ φ₁ : SpecialLinearGroup (Fin 3) F →* G}
  {ρ₀ ρ₁ : SpecialLinearGroup (Fin 2) F →* G} {L : (Fin (5 - 1) → ℤ) → F → G}
  {S : (Fin (5 - 1) → ℤ) → (Fin 2 → F) → G} {w : Fin (5 - 1) → G} {V₁ : Subgroup G}
  (H : GlueHyp hirr φ₀ φ₁ ρ₀ ρ₁ L S w V₁)
include H

omit [CharP F 2] in
theorem GlueHyp.commA2 (i : Fin (5 - 1)) (h : i.val + 3 < 5) (s t : F) :
    ⁅glueL φ₀ φ₁ L (Pi.single i 1) s,
      glueL φ₀ φ₁ L (Pi.single (⟨i.val + 1, by omega⟩ : Fin (5 - 1)) 1) t⁆ =
    glueL φ₀ φ₁ L (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (5 - 1)) 1) (s * t) := by
  rcases nd_cases i with rfl | rfl | rfl | rfl
  · show ⁅glueL φ₀ φ₁ L (sr nd0) s, glueL φ₀ φ₁ L (sr nd1) t⁆ =
      glueL φ₀ φ₁ L (sr nd0 + sr nd1) (s * t)
    rw [glueL_d0, glueL_d1, glueL_d01, ← map_commutatorElement,
      tv_comm (by decide) (by decide) (by decide)]
  · show ⁅glueL φ₀ φ₁ L (sr nd1) s, glueL φ₀ φ₁ L (sr nd2) t⁆ =
      glueL φ₀ φ₁ L (sr nd1 + sr nd2) (s * t)
    rw [H.w_d1, H.w_d2, glueL_d12, ← map_commutatorElement,
      tv_comm (by decide) (by decide) (by decide)]
  · exact absurd h (by decide)
  · exact absurd h (by decide)

omit [CharP F 2] in
theorem GlueHyp.commuteA2l (i : Fin (5 - 1)) (h : i.val + 3 < 5) (s t : F) :
    Commute (glueL φ₀ φ₁ L (Pi.single i 1) s)
      (glueL φ₀ φ₁ L (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (5 - 1)) 1) t) := by
  rcases nd_cases i with rfl | rfl | rfl | rfl
  · show Commute (glueL φ₀ φ₁ L (sr nd0) s) (glueL φ₀ φ₁ L (sr nd0 + sr nd1) t)
    rw [glueL_d0, glueL_d01]
    exact (tv_commute (by decide) (by decide) (by decide) (by decide) s t).map φ₀
  · show Commute (glueL φ₀ φ₁ L (sr nd1) s) (glueL φ₀ φ₁ L (sr nd1 + sr nd2) t)
    rw [H.w_d1, glueL_d12]
    exact (tv_commute (by decide) (by decide) (by decide) (by decide) s t).map φ₁
  · exact absurd h (by decide)
  · exact absurd h (by decide)

omit [CharP F 2] in
theorem GlueHyp.commuteA2r (i : Fin (5 - 1)) (h : i.val + 3 < 5) (s t : F) :
    Commute
      (glueL φ₀ φ₁ L (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (5 - 1)) 1) s)
      (glueL φ₀ φ₁ L (Pi.single (⟨i.val + 1, by omega⟩ : Fin (5 - 1)) 1) t) := by
  rcases nd_cases i with rfl | rfl | rfl | rfl
  · show Commute (glueL φ₀ φ₁ L (sr nd0 + sr nd1) s) (glueL φ₀ φ₁ L (sr nd1) t)
    rw [glueL_d01, glueL_d1]
    exact (tv_commute (by decide) (by decide) (by decide) (by decide) s t).map φ₀
  · show Commute (glueL φ₀ φ₁ L (sr nd1 + sr nd2) s) (glueL φ₀ φ₁ L (sr nd2) t)
    rw [glueL_d12, H.w_d2]
    exact (tv_commute (by decide) (by decide) (by decide) (by decide) s t).map φ₁
  · exact absurd h (by decide)
  · exact absurd h (by decide)

omit H [CharP F 2] in
theorem eq_nd2_of_B2 {i : Fin (5 - 1)} (h : i.val + 3 = 5) : i = nd2 := Fin.ext (by simp; omega)

omit [CharP F 2] in
theorem GlueHyp.relB2 (i : Fin (5 - 1)) (h : i.val + 3 = 5) (p q : Fin 2 → F) (s t : F) :
    ⁅S (Pi.single (⟨i.val + 1, by omega⟩ : Fin (5 - 1)) 1) p, glueL φ₀ φ₁ L (Pi.single i 1) s⁆ =
      S (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (5 - 1)) 1) (s • p) *
        glueL φ₀ φ₁ L (Pi.single i 1 + 2 • Pi.single (⟨i.val + 1, by omega⟩ : Fin (5 - 1)) 1)
          (s * planeNorm b c p) ∧
    ⁅S (Pi.single (⟨i.val + 1, by omega⟩ : Fin (5 - 1)) 1) p,
        S (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (5 - 1)) 1) q⁆ =
      glueL φ₀ φ₁ L (Pi.single i 1 + 2 • Pi.single (⟨i.val + 1, by omega⟩ : Fin (5 - 1)) 1)
        (polarPlane b c p q) ∧
    Commute (S (Pi.single (⟨i.val + 1, by omega⟩ : Fin (5 - 1)) 1) p)
      (glueL φ₀ φ₁ L (Pi.single i 1 + 2 • Pi.single (⟨i.val + 1, by omega⟩ : Fin (5 - 1)) 1) s) ∧
    Commute (S (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (5 - 1)) 1) p)
      (glueL φ₀ φ₁ L (Pi.single i 1 + 2 • Pi.single (⟨i.val + 1, by omega⟩ : Fin (5 - 1)) 1) s) ∧
    Commute (S (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (5 - 1)) 1) p)
      (glueL φ₀ φ₁ L (Pi.single i 1) s) ∧
    Commute (glueL φ₀ φ₁ L
        (Pi.single i 1 + 2 • Pi.single (⟨i.val + 1, by omega⟩ : Fin (5 - 1)) 1) s)
      (glueL φ₀ φ₁ L (Pi.single i 1) t) := by
  obtain rfl := eq_nd2_of_B2 h
  have e2 : ∀ x, glueL φ₀ φ₁ L (sr nd2 + 2 • sr nd3) x = L (sr nd2 + 2 • sr nd3) x := fun x =>
    glueL_of_last φ₀ φ₁ L (by simp) (by simp) x
  show ⁅S (sr nd3) p, glueL φ₀ φ₁ L (sr nd2) s⁆ =
      S (sr nd2 + sr nd3) (s • p) * glueL φ₀ φ₁ L (sr nd2 + 2 • sr nd3) (s * planeNorm b c p) ∧
    ⁅S (sr nd3) p, S (sr nd2 + sr nd3) q⁆ =
      glueL φ₀ φ₁ L (sr nd2 + 2 • sr nd3) (polarPlane b c p q) ∧
    Commute (S (sr nd3) p) (glueL φ₀ φ₁ L (sr nd2 + 2 • sr nd3) s) ∧
    Commute (S (sr nd2 + sr nd3) p) (glueL φ₀ φ₁ L (sr nd2 + 2 • sr nd3) s) ∧
    Commute (S (sr nd2 + sr nd3) p) (glueL φ₀ φ₁ L (sr nd2) s) ∧
    Commute (glueL φ₀ φ₁ L (sr nd2 + 2 • sr nd3) s) (glueL φ₀ φ₁ L (sr nd2) t)
  simp only [e2, glueL_d2]
  exact ⟨H.commB2 p s, H.commB2' p q, H.commuteB2_b_2ab p s, H.commuteB2_ab_2ab p s,
    H.commuteB2_ab_a p s, H.commuteB2_2ab_a s t⟩

omit [CharP F 2] in
theorem GlueHyp.commuteA1A1L (i j : Fin (5 - 1)) (hij : i.val + 2 ≤ j.val) (hj : j.val + 2 < 5)
    (s t : F) : Commute (glueL φ₀ φ₁ L (Pi.single i 1) s) (glueL φ₀ φ₁ L (Pi.single j 1) t) := by
  rcases nd_cases j with rfl | rfl | rfl | rfl
  · exact absurd hij (show ¬ (i.val + 2 ≤ 0) by omega)
  · exact absurd hij (show ¬ (i.val + 2 ≤ 1) by omega)
  · rcases nd_cases i with rfl | rfl | rfl | rfl
    · show Commute (glueL φ₀ φ₁ L (sr nd0) s) (glueL φ₀ φ₁ L (sr nd2) t)
      rw [H.v_d0, glueL_d2]
      exact H.V _ _ (H.memL _ _)
    · exact absurd hij (by decide)
    · exact absurd hij (by decide)
    · exact absurd hij (by decide)
  · exact absurd hj (by decide)

omit [CharP F 2] in
theorem GlueHyp.commuteA1A1S (i k : Fin (5 - 1)) (hik : i.val + 2 ≤ k.val) (hk : k.val + 2 = 5)
    (s : F) (p : Fin 2 → F) : Commute (glueL φ₀ φ₁ L (Pi.single i 1) s) (S (Pi.single k 1) p) := by
  obtain rfl : k = nd3 := Fin.ext (by simp; omega)
  rcases nd_cases i with rfl | rfl | rfl | rfl
  · show Commute (glueL φ₀ φ₁ L (sr nd0) s) (S (sr nd3) p)
    rw [H.v_d0]
    exact H.V _ _ (H.memS _ _)
  · show Commute (glueL φ₀ φ₁ L (sr nd1) s) (S (sr nd3) p)
    rw [H.v_d1]
    exact (H.E _ p).1
  · exact absurd hik (by decide)
  · exact absurd hik (by decide)

omit [CharP F 2] in
theorem GlueHyp.rankL (k : Fin (5 - 1)) (hk : k.val + 2 < 5) :
    ∃ Θk : SpecialLinearGroup (Fin 2) F →* G,
      (∀ x, Θk (sl2Upper x) = glueL φ₀ φ₁ L (Pi.single k 1) x) ∧
        ∀ x, Θk (sl2Lower x) = glueL φ₀ φ₁ L (-Pi.single k 1) x := by
  rcases nd_cases k with rfl | rfl | rfl | rfl
  · exact ⟨ρ₀, fun x => by rw [← LevisExtras.tv01_eq_sl2Upper]; exact (H.v_d0 x).symm,
      fun x => by rw [← LevisExtras.tv10_eq_sl2Lower]; exact (H.v_nd0 x).symm⟩
  · exact ⟨ρ₁, fun x => by rw [← LevisExtras.tv01_eq_sl2Upper]; exact (H.v_d1 x).symm,
      fun x => by rw [← LevisExtras.tv10_eq_sl2Lower]; exact (H.v_nd1 x).symm⟩
  · obtain ⟨Θ, hU, hL⟩ := H.rank₂
    exact ⟨Θ, fun x => by rw [hU]; exact (glueL_d2 φ₀ φ₁ L x).symm,
      fun x => by rw [hL]; exact (glueL_nd2 φ₀ φ₁ L x).symm⟩
  · exact absurd hk (by decide)

omit [CharP F 2] in
theorem GlueHyp.gen (hgen : ρ₀.range ⊔ ρ₁.range ⊔ V₁ = ⊤) :
    Subgroup.closure (⋃ k : Fin (5 - 1), if k.val + 2 < 5 then
      Set.range (glueL φ₀ φ₁ L (Pi.single k 1)) ∪ Set.range (glueL φ₀ φ₁ L (-Pi.single k 1))
    else Set.range (S (Pi.single k 1)) ∪ Set.range (S (-Pi.single k 1))) = ⊤ := by
  set T := Subgroup.closure (⋃ k : Fin (5 - 1), if k.val + 2 < 5 then
      Set.range (glueL φ₀ φ₁ L (Pi.single k 1)) ∪ Set.range (glueL φ₀ φ₁ L (-Pi.single k 1))
    else Set.range (S (Pi.single k 1)) ∪ Set.range (S (-Pi.single k 1))) with hT
  have hmemL : ∀ k : Fin (5 - 1), k.val + 2 < 5 → ∀ x,
      glueL φ₀ φ₁ L (Pi.single k 1) x ∈ T ∧ glueL φ₀ φ₁ L (-Pi.single k 1) x ∈ T :=
    fun k hk x => by
      refine ⟨Subgroup.subset_closure (Set.mem_iUnion.2 ⟨k, ?_⟩),
        Subgroup.subset_closure (Set.mem_iUnion.2 ⟨k, ?_⟩)⟩
      · rw [ite_eq_left hk]
        exact Or.inl ⟨x, rfl⟩
      · rw [ite_eq_left hk]
        exact Or.inr ⟨x, rfl⟩
  have hmemS : ∀ p, S (sr nd3) p ∈ T ∧ S (-sr nd3) p ∈ T := fun p => by
    refine ⟨Subgroup.subset_closure (Set.mem_iUnion.2 ⟨nd3, ?_⟩),
      Subgroup.subset_closure (Set.mem_iUnion.2 ⟨nd3, ?_⟩)⟩
    · rw [ite_eq_right (by decide)]
      exact Or.inl ⟨p, rfl⟩
    · rw [ite_eq_right (by decide)]
      exact Or.inr ⟨p, rfl⟩
  rw [eq_top_iff, ← hgen]
  refine sup_le (sup_le ?_ ?_) ?_
  · rintro _ ⟨g, rfl⟩
    refine CaseM.sl2_mem_of_tv ρ₀ (fun x => ?_) (fun x => ?_) g
    · rw [← H.v_d0]
      exact (hmemL nd0 (by decide) x).1
    · rw [← H.v_nd0]
      exact (hmemL nd0 (by decide) x).2
  · rintro _ ⟨g, rfl⟩
    refine CaseM.sl2_mem_of_tv ρ₁ (fun x => ?_) (fun x => ?_) g
    · rw [← H.v_d1]
      exact (hmemL nd1 (by decide) x).1
    · rw [← H.v_nd1]
      exact (hmemL nd1 (by decide) x).2
  · refine H.genV.trans (Subgroup.closure_le _ |>.2 ?_)
    rintro _ (((⟨x, rfl⟩ | ⟨x, rfl⟩) | ⟨p, rfl⟩) | ⟨p, rfl⟩)
    · rw [← glueL_d2 φ₀ φ₁ L]
      exact (hmemL nd2 (by decide) x).1
    · rw [← glueL_nd2 φ₀ φ₁ L]
      exact (hmemL nd2 (by decide) x).2
    · exact (hmemS p).1
    · exact (hmemS p).2

theorem GlueHyp.isMinusFrame [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)]
    (hrank₃ : ∃ Θ : SL2E b c →* G, (∀ t, Θ (sl2Upper t) = S (sr nd3) (fieldCoord t)) ∧
      ∀ t, Θ (sl2Lower t) = S (-sr nd3) (starCoord t))
    (hgen : ρ₀.range ⊔ ρ₁.range ⊔ V₁ = ⊤) (hnt : ρ₀ (tv 0 1 1) ≠ 1) :
    IsMinusFrame 5 hirr (glueL φ₀ φ₁ L) S where
  addL _ _ γ _ _ x y := glueL_add φ₀ φ₁ L H.addL γ x y
  addS _ _ γ _ _ p q := H.addS γ p q
  commA2 := H.commA2
  commuteA2l := H.commuteA2l
  commuteA2r := H.commuteA2r
  commB2 i h p s := (H.relB2 i h p p s s).1
  commB2' i h p q := (H.relB2 i h p q 0 0).2.1
  commuteB2_b_2ab i h p s := (H.relB2 i h p p s s).2.2.1
  commuteB2_ab_2ab i h p s := (H.relB2 i h p p s s).2.2.2.1
  commuteB2_ab_a i h p s := (H.relB2 i h p p s s).2.2.2.2.1
  commuteB2_2ab_a i h s t := (H.relB2 i h 0 0 s t).2.2.2.2.2
  commuteA1A1L := H.commuteA1A1L
  commuteA1A1S := H.commuteA1A1S
  weyl := H.weyl
  rankL := H.rankL
  rankS k hk := by
    obtain rfl : k = nd3 := Fin.ext (by simp; omega)
    exact hrank₃
  gen := H.gen hgen
  nt := ⟨nd0, by decide, 1, by
    rw [show (Pi.single nd0 1 : Fin (5 - 1) → ℤ) = sr nd0 from rfl, H.v_d0]
    exact hnt⟩

end Main

end CFSG.Timmesfeld.ARS.CaseOADeg
