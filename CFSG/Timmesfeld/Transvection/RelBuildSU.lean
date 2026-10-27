module

public import CFSG.Timmesfeld.Transvection.RelBuildSUData
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.Transvection.Pres
open scoped commutatorElement

namespace RelBuild

variable {r : ℕ} {F : Type*} [Field F] {σ : F ≃+* F} {G : Type*} [Group G]

theorem d7b_aux {y x u A B C L L' : G} (hA : x * ⁅y, u⁆ * x⁻¹ = A * ⁅y, u⁆)
    (hB : u * ⁅y, x⁆ * u⁻¹ = B * ⁅y, x⁆) (hc₁ : ⁅x, u⁆ * ⁅y, u⁆ = ⁅y, u⁆ * ⁅x, u⁆)
    (hc₂ : ⁅x, u⁆ * B = B * ⁅x, u⁆) (hc₃ : ⁅x, u⁆ * ⁅y, x⁆ = ⁅y, x⁆ * ⁅x, u⁆)
    (hyc : ⁅y, ⁅x, u⁆⁆ = C * L) (hAV : A * ⁅y, x⁆ = ⁅y, x⁆ * A)
    (hVV : ⁅y, x⁆ * ⁅y, u⁆ = L' * ⁅y, u⁆ * ⁅y, x⁆) (hBV : B * ⁅y, u⁆ = ⁅y, u⁆ * B)
    (hLB : L * B = B * L) : A * L' = C * B * L := by
  have e₁ : ⁅y, x * u⁆ = ⁅y, x⁆ * (A * ⁅y, u⁆) := by rw [comm_mul_right, hA]
  have e₂ : x * u = ⁅x, u⁆ * (u * x) := by simp only [commutatorElement_def]; group
  have e₃ : ⁅y, x * u⁆ = C * L * (⁅y, u⁆ * (B * ⁅y, x⁆)) := by
    rw [e₂, comm_mul_right, hyc, comm_mul_right, hB]
    congr 1
    calc ⁅x, u⁆ * (⁅y, u⁆ * (B * ⁅y, x⁆)) * ⁅x, u⁆⁻¹ =
          ⁅x, u⁆ * ⁅y, u⁆ * B * ⁅y, x⁆ * ⁅x, u⁆⁻¹ := by group
      _ = ⁅y, u⁆ * (⁅x, u⁆ * B) * ⁅y, x⁆ * ⁅x, u⁆⁻¹ := by rw [hc₁]; group
      _ = ⁅y, u⁆ * B * (⁅x, u⁆ * ⁅y, x⁆) * ⁅x, u⁆⁻¹ := by rw [hc₂]; group
      _ = ⁅y, u⁆ * (B * ⁅y, x⁆) := by rw [hc₃]; group
  have key : A * L' * (⁅y, u⁆ * ⁅y, x⁆) = C * B * L * (⁅y, u⁆ * ⁅y, x⁆) := by
    calc A * L' * (⁅y, u⁆ * ⁅y, x⁆) = A * (L' * ⁅y, u⁆ * ⁅y, x⁆) := by group
      _ = A * (⁅y, x⁆ * ⁅y, u⁆) := by rw [hVV]
      _ = ⁅y, x⁆ * (A * ⁅y, u⁆) := by rw [← mul_assoc, hAV, mul_assoc]
      _ = C * L * (⁅y, u⁆ * (B * ⁅y, x⁆)) := e₁.symm.trans e₃
      _ = C * (L * B) * (⁅y, u⁆ * ⁅y, x⁆) := by rw [← mul_assoc ⁅y, u⁆, ← hBV]; group
      _ = C * B * L * (⁅y, u⁆ * ⁅y, x⁆) := by rw [hLB]; group
  exact mul_right_cancel key

theorem mul_eq_of_mul_eq {X Y L L' : G} (h : X * L' = Y * L) (hY : Y * Y = 1)
    (hL : L' * L' = 1) : Y * X = L * L' := by
  calc Y * X = Y * (X * L') * L' := by rw [mul_assoc, mul_assoc, hL, mul_one]
    _ = Y * Y * L * L' := by rw [h]; group
    _ = L * L' := by rw [hY, one_mul]

theorem conj_eq_commutator_mul (x g : G) : x * g * x⁻¹ = ⁅x, g⁆ * g := by
  simp only [commutatorElement_def]
  group

@[expose] noncomputable def lamTw (hσ : ∀ c, σ (σ c) = c) (e : Bool) {l : F} (hl : l ≠ 0) :
    F ≃+ F where
  toFun b := l * tw σ e b
  invFun x := tw σ e (l⁻¹ * x)
  left_inv b := by
    simp only [tw_mul, tw_tw_self hσ]
    rw [← mul_assoc, ← tw_mul, inv_mul_cancel₀ hl, tw_one, one_mul]
  right_inv x := by
    simp only [tw_tw_self hσ]
    rw [← mul_assoc, mul_inv_cancel₀ hl, one_mul]
  map_add' b b' := by rw [tw_add, mul_add]

theorem lamTw_apply (hσ : ∀ c, σ (σ c) = c) (e : Bool) {l : F} (hl : l ≠ 0) (b : F) :
    lamTw hσ e hl b = l * tw σ e b := rfl

theorem lamTw_symm_apply (hσ : ∀ c, σ (σ c) = c) (e : Bool) {l : F} (hl : l ≠ 0) (x : F) :
    (lamTw hσ e hl).symm x = tw σ e (l⁻¹ * x) := rfl

theorem lamTw_smul (hσ : ∀ c, σ (σ c) = c) (e : Bool) {l : F} (hl : l ≠ 0) {c : F}
    (hc : σ c = c) (s : F) : lamTw hσ e hl (c * s) = c * lamTw hσ e hl s := by
  rw [lamTw_apply, lamTw_apply, tw_smul e hc]
  ring

theorem lamTw_norm (hσ : ∀ c, σ (σ c) = c) (e : Bool) {l : F} (hl : l ≠ 0) (hN : σ l * l = 1)
    (s : F) : σ (lamTw hσ e hl s) * lamTw hσ e hl s = σ s * s := by
  rw [lamTw_apply, map_mul, ← norm_tw hσ e s]
  linear_combination (σ (tw σ e s) * tw σ e s) * hN

variable [CharP F 2]

theorem d7b_final (hσ : ∀ c, σ (σ c) = c) (hne : ∃ θ, σ θ ≠ θ) {c : F} {e₁ e₂ : Bool}
    (h : ∀ a b s, c * tw σ e₁ (σ (s * b)) * tw σ e₂ a + c * tw σ e₁ (σ (s * a)) * tw σ e₂ b =
      σ s * (a * σ b + σ a * b)) : c = 1 ∧ e₁ = false ∧ e₂ = false := by
  obtain ⟨θ, hθ⟩ := hne
  have hT := trace_ne_zero hθ
  have h₁ := h 1 θ 1
  have h₂ := h 1 θ θ
  have hc1 : ∀ x : F, x * (θ + σ θ) = θ + σ θ → x = 1 := fun x hx =>
    mul_right_cancel₀ hT (by rw [hx, one_mul])
  cases e₁ <;> cases e₂ <;>
    simp only [tw_true, tw_false, map_one, one_mul, mul_one, map_mul, hσ] at h₁ h₂
  · exact ⟨hc1 c (by linear_combination h₁), rfl, rfl⟩
  · exfalso
    apply hT
    rw [← CharTwo.add_self_eq_zero (c * σ θ)]
    linear_combination -h₁
  · exfalso
    apply hT
    rw [← CharTwo.add_self_eq_zero (c * θ)]
    linear_combination -h₁
  · exfalso
    have hc : c = 1 := hc1 c (by linear_combination h₁)
    subst hc
    apply hθ
    have h₃ : θ * (θ + σ θ) = σ θ * (θ + σ θ) := by linear_combination h₂
    exact (mul_right_cancel₀ hT h₃).symm

end RelBuild

namespace RelBuild.Recoord

variable {r : ℕ} {F : Type*} [Field F] {σ : F ≃+* F}

@[expose] def conjσ (θ : F ≃+ F) : F ≃+ F :=
  (σ.toAddEquiv.trans θ).trans σ.toAddEquiv

theorem conjσ_apply (θ : F ≃+ F) (c : F) : conjσ (σ := σ) θ c = σ (θ (σ c)) := rfl

@[expose] def upperθ (σ : F ≃+* F) (ρ : Fin r → Fin r → F ≃+ F) (i j : Fin r) : F ≃+ F :=
  if i < j then ρ i j else if j < i then conjσ (σ := σ) (ρ j i) else AddEquiv.refl F

variable {ρ : Fin r → Fin r → F ≃+ F}

theorem upperθ_of_lt {i j : Fin r} (h : i < j) : upperθ σ ρ i j = ρ i j :=
  ite_eq_left h

theorem upperθ_of_gt {i j : Fin r} (h : j < i) : upperθ σ ρ i j = conjσ (σ := σ) (ρ j i) := by
  rw [upperθ, ite_eq_right (not_lt.2 h.le), ite_eq_left h]

theorem upperθ_self (i : Fin r) : upperθ σ ρ i i = AddEquiv.refl F := by
  rw [upperθ, ite_eq_right (lt_irrefl i), ite_eq_right (lt_irrefl i)]

theorem upperθ_swap (hσ : ∀ c, σ (σ c) = c) (i j : Fin r) (c : F) :
    upperθ σ ρ j i c = σ (upperθ σ ρ i j (σ c)) := by
  rcases lt_trichotomy i j with h | rfl | h
  · rw [upperθ_of_gt h, upperθ_of_lt h, conjσ_apply]
  · rw [upperθ_self]
    exact (hσ c).symm
  · rw [upperθ_of_lt h, upperθ_of_gt h, conjσ_apply, hσ, hσ]

theorem upperθ_smul (hK : ∀ i j, i < j → ∀ c s, σ c = c → ρ i j (c * s) = c * ρ i j s)
    (i j : Fin r) (c s : F) (hc : σ c = c) : upperθ σ ρ i j (c * s) = c * upperθ σ ρ i j s := by
  rcases lt_trichotomy i j with h | rfl | h
  · rw [upperθ_of_lt h]
    exact hK i j h c s hc
  · rw [upperθ_self]
    rfl
  · rw [upperθ_of_gt h, conjσ_apply, conjσ_apply, map_mul, hc, hK j i h c _ hc, map_mul, hc]

theorem upperθ_norm (hσ : ∀ c, σ (σ c) = c)
    (hN : ∀ i j, i < j → ∀ s, σ (ρ i j s) * ρ i j s = σ s * s) (i j : Fin r) (s : F) :
    σ (upperθ σ ρ i j s) * upperθ σ ρ i j s = σ s * s := by
  rcases lt_trichotomy i j with h | rfl | h
  · rw [upperθ_of_lt h]
    exact hN i j h s
  · rw [upperθ_self]
    rfl
  · rw [upperθ_of_gt h, conjσ_apply, hσ]
    have h' := hN j i h (σ s)
    rw [hσ] at h'
    linear_combination h'

@[expose] noncomputable def ofUpper (hσ : ∀ c, σ (σ c) = c) (ρ : Fin r → Fin r → F ≃+ F)
    (hK : ∀ i j, i < j → ∀ c s, σ c = c → ρ i j (c * s) = c * ρ i j s)
    (hN : ∀ i j, i < j → ∀ s, σ (ρ i j s) * ρ i j s = σ s * s) : Recoord r σ where
  θ := upperθ σ ρ
  swap := upperθ_swap hσ
  smul := upperθ_smul hK
  norm := upperθ_norm hσ hN

theorem ofUpper_θ (hσ : ∀ c, σ (σ c) = c) (ρ : Fin r → Fin r → F ≃+ F) (hK hN) :
    (ofUpper hσ ρ hK hN).θ = upperθ σ ρ := rfl

end RelBuild.Recoord

namespace RelBuild.SUData

variable {r : ℕ} {F : Type*} [Field F] {σ : F ≃+* F} {G : Type*} [Group G]
  (D : SUData r σ G)

theorem d7b_identity [CharP F 2] (hσ : ∀ c, σ (σ c) = c) (hne : ∃ θ, σ θ ≠ θ) {i j k : Fin r}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (hkji : D.ShortRel k j i (· * ·)) (a b s : F) :
    D.μ k i j (σ (s * b)) a + D.μ k i j (σ (s * a)) b = σ s * (a * σ b + σ a * b) := by
  have hM := D.shortRel_μ (i := k) (j := i) (k := j) hik.symm hij hjk.symm
  have iji : idx (Sum.inl j : Fin r ⊕ Fin r) ≠ idx (Sum.inr i) := by simpa using hij.symm
  have ijI : idx (Sum.inl j : Fin r ⊕ Fin r) ≠ idx (Sum.inl i) := by simpa using hij.symm
  have ikI : idx (Sum.inl k : Fin r ⊕ Fin r) ≠ idx (Sum.inl i) := by simpa using hik.symm
  have iki : idx (Sum.inl k : Fin r ⊕ Fin r) ≠ idx (Sum.inr i) := by simpa using hik.symm
  have ikj : idx (Sum.inl k : Fin r ⊕ Fin r) ≠ idx (Sum.inr j) := by simpa using hjk.symm
  have ijK : idx (Sum.inl j : Fin r ⊕ Fin r) ≠ idx (Sum.inl k) := by simpa using hjk
  set τ := a * σ b + σ a * b with hτ
  have hτσ : σ τ = τ := RelBuild.fixed_trace hσ a b
  have hyx : ⁅D.ξ (.inl k) (.inr j) s, D.ξ (.inl j) (.inr i) a⁆ =
      D.ξ (.inl k) (.inr i) (s * a) := hkji _ _ _ rfl rfl rfl s a
  have hyu : ⁅D.ξ (.inl k) (.inr j) s, D.ξ (.inl j) (.inl i) b⁆ =
      D.ξ (.inl k) (.inl i) (s * b) := hkji _ _ _ rfl rfl rfl s b
  have hxu : ⁅D.ξ (.inl j) (.inr i) a, D.ξ (.inl j) (.inl i) b⁆ = D.ξL (.inl j) τ :=
    D.trace' hσ iji a b
  have hA : ⁅D.ξ (.inl j) (.inr i) a, D.ξ (.inl k) (.inl i) (s * b)⁆ =
      D.ξ (.inl j) (.inl k) (D.μ k i j (σ (s * b)) a) := by
    rw [D.swap _ _ (Ne.symm ikI)]
    exact hM _ _ _ rfl rfl rfl a _
  have hB : ⁅D.ξ (.inl j) (.inl i) b, D.ξ (.inl k) (.inr i) (s * a)⁆ =
      D.ξ (.inl j) (.inl k) (D.μ k i j (σ (s * a)) b) := by
    rw [D.swap _ _ (by simpa using hik : idx (Sum.inr i : Fin r ⊕ Fin r) ≠ idx (Sum.inl k))]
    exact hM _ _ _ rfl rfl rfl b _
  have hyc : ⁅D.ξ (.inl k) (.inr j) s, D.ξL (.inl j) τ⁆ =
      D.ξ (.inl k) (.inl j) (s * τ) * D.ξL (.inl k) (σ s * s * τ) :=
    D.shortLong' hσ ikj s τ hτσ
  have hVV : ⁅D.ξ (.inl k) (.inr i) (s * a), D.ξ (.inl k) (.inl i) (s * b)⁆ =
      D.ξL (.inl k) (s * a * σ (s * b) + σ (s * a) * (s * b)) := D.trace' hσ iki _ _
  have key := RelBuild.d7b_aux (y := D.ξ (.inl k) (.inr j) s) (x := D.ξ (.inl j) (.inr i) a)
    (u := D.ξ (.inl j) (.inl i) b) (A := D.ξ (.inl j) (.inl k) (D.μ k i j (σ (s * b)) a))
    (B := D.ξ (.inl j) (.inl k) (D.μ k i j (σ (s * a)) b))
    (C := D.ξ (.inl k) (.inl j) (s * τ)) (L := D.ξL (.inl k) (σ s * s * τ))
    (L' := D.ξL (.inl k) (s * a * σ (s * b) + σ (s * a) * (s * b)))
    (by rw [hyu, RelBuild.conj_eq_commutator_mul, hA])
    (by rw [hyx, RelBuild.conj_eq_commutator_mul, hB])
    (by
      rw [hxu, hyu]
      exact commutatorElement_eq_one_iff_mul_comm.1 (D.commLS' ikI (by simp) (by simp) hτσ _))
    (commutatorElement_eq_one_iff_mul_comm.1 (by rw [hxu]; exact D.commLS_self ijK hτσ _))
    (by
      rw [hxu, hyx]
      exact commutatorElement_eq_one_iff_mul_comm.1
        (D.commLS' iki (by simp) (by simpa using hij) hτσ _))
    (by rw [hxu, hyc])
    (by
      rw [hyx]
      exact commutatorElement_eq_one_iff_mul_comm.1
        (D.commSS' ijK iki (by simp) (by simp) (by simpa using hij) (by simpa using hik) _ _))
    (by
      rw [hyx, hyu, ← hVV]
      simp only [commutatorElement_def]
      group)
    (by
      rw [hyu]
      exact commutatorElement_eq_one_iff_mul_comm.1
        (D.commSS' ijK ikI (by simp) (by simp) (by simp) (by simp) _ _))
    (commutatorElement_eq_one_iff_mul_comm.1
      (D.commLS' ijK (by simp) (by simp) (RelBuild.fixed_norm_mul hσ s hτσ) _))
  rw [D.swap _ _ ijK] at key
  have hf₁ : σ (σ s * s * τ) = σ s * s * τ := RelBuild.fixed_norm_mul hσ s hτσ
  have hf₂ := RelBuild.fixed_trace hσ (s * a) (s * b)
  have key' : D.ξ (.inl j) (.inl k) (D.μ k i j (σ (s * b)) a) *
      D.ξL (.inl k) (s * a * σ (s * b) + σ (s * a) * (s * b)) =
      D.ξ (.inl j) (.inl k) (σ (s * τ) + D.μ k i j (σ (s * a)) b) *
        D.ξL (.inl k) (σ s * s * τ) := by
    rw [D.add _ _ ijK]
    exact key
  have hY : D.ξ (.inl j) (.inl k) (σ (s * τ) + D.μ k i j (σ (s * a)) b) *
      D.ξ (.inl j) (.inl k) (σ (s * τ) + D.μ k i j (σ (s * a)) b) = 1 := by
    rw [← D.add _ _ ijK, CharTwo.add_self_eq_zero, D.map_zero ijK]
  have hL : D.ξL (.inl k) (s * a * σ (s * b) + σ (s * a) * (s * b)) *
      D.ξL (.inl k) (s * a * σ (s * b) + σ (s * a) * (s * b)) = 1 := by
    rw [← D.addL _ _ _ hf₂ hf₂, CharTwo.add_self_eq_zero, D.mapL_zero]
  have hJ := RelBuild.mul_eq_of_mul_eq key' hY hL
  rw [← D.add _ _ ijK, ← D.addL _ _ _ hf₁ hf₂] at hJ
  have h0 := D.eq_zero_of_ξ_eq_ξL hσ hne hjk (by rw [map_add, hf₁, hf₂]) hJ
  have hστ : σ (s * τ) = σ s * τ := by rw [map_mul, hτσ]
  rw [hστ] at h0
  linear_combination h0 - σ s * τ * (CharTwo.two_eq_zero : (2 : F) = 0)

theorem mul_of_d7b [Finite F] [CharP F 2] (hσ : ∀ c, σ (σ c) = c) (hne : ∃ θ, σ θ ≠ θ)
    {i j k : Fin r} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hkji : D.ShortRel k j i (· * ·)) (q p : F) : D.μ k i j q p = q * p := by
  obtain ⟨c, e₁, e₂, -, hc⟩ := RelBuild.exists_normal_form hσ hne
    (D.μ_add_left hik.symm hij hjk.symm) (D.μ_add_right hik.symm hij hjk.symm)
    (fun c s t hc => (D.hμK k i j hik.symm hij hjk.symm c s t hc).1)
    (fun c s t hc => (D.hμK k i j hik.symm hij hjk.symm c s t hc).2)
    (D.hμN k i j hik.symm hij hjk.symm)
  obtain ⟨rfl, rfl, rfl⟩ := RelBuild.d7b_final hσ hne (fun a b s => by
    rw [← hc, ← hc]
    exact D.d7b_identity hσ hne hij hjk hik hkji a b s)
  rw [hc]
  simp

theorem tw_ne_zero (e : Bool) {x : F} (hx : x ≠ 0) : RelBuild.tw σ e x ≠ 0 := by
  cases e
  · exact hx
  · exact (map_ne_zero σ).2 hx

theorem exists_reparam_star [Finite F] [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    (hne : ∃ θ, σ θ ≠ θ) (o : Fin r) (ho : ∀ i, o ≤ i) :
    ∃ D' : SUData r σ G, D'.Reparam D ∧ ∃ α : Fin r → Fin r → Bool,
      ∀ j k, o < j → j < k → ∀ s t, D'.μ o j k s t = RelBuild.tw σ (α j k) s * t := by
  have hnf : ∀ j k : Fin r, ∃ c : F, ∃ e₁ e₂ : Bool, c ≠ 0 ∧ (o < j → j < k →
      σ c * c = 1 ∧ ∀ s t, D.μ o j k s t = c * RelBuild.tw σ e₁ s * RelBuild.tw σ e₂ t) := by
    intro j k
    by_cases h : o < j ∧ j < k
    · have hoj : o ≠ j := h.1.ne
      have hjk : j ≠ k := h.2.ne
      have hok : o ≠ k := (h.1.trans h.2).ne
      obtain ⟨c, e₁, e₂, hc, hμ⟩ := RelBuild.exists_normal_form hσ hne
        (D.μ_add_left hoj hjk hok) (D.μ_add_right hoj hjk hok)
        (fun c s t hc => (D.hμK o j k hoj hjk hok c s t hc).1)
        (fun c s t hc => (D.hμK o j k hoj hjk hok c s t hc).2) (D.hμN o j k hoj hjk hok)
      exact ⟨c, e₁, e₂, fun h0 => by rw [h0, mul_zero] at hc; exact zero_ne_one hc,
        fun _ _ => ⟨hc, hμ⟩⟩
    · exact ⟨1, false, false, one_ne_zero, fun h₁ h₂ => absurd ⟨h₁, h₂⟩ h⟩
  choose c e₁ e₂ hc0 hnf using hnf
  have hl : ∀ j k, RelBuild.tw σ (e₂ j k) (c j k)⁻¹ ≠ 0 := fun j k =>
    tw_ne_zero _ (inv_ne_zero (hc0 j k))
  let ρ : Fin r → Fin r → F ≃+ F := fun j k =>
    if j = o then AddEquiv.refl F else RelBuild.lamTw hσ (e₂ j k) (hl j k)
  have hK : ∀ i j, i < j → ∀ c s, σ c = c → ρ i j (c * s) = c * ρ i j s := by
    intro i j _ c' s hc'
    by_cases hio : i = o
    · simp only [ρ, ite_eq_left hio, AddEquiv.refl_apply]
    · simp only [ρ, ite_eq_right hio]
      exact RelBuild.lamTw_smul hσ _ _ hc' s
  have hN : ∀ i j, i < j → ∀ s, σ (ρ i j s) * ρ i j s = σ s * s := by
    intro i j hij s
    by_cases hio : i = o
    · simp only [ρ, ite_eq_left hio, AddEquiv.refl_apply]
    · simp only [ρ, ite_eq_right hio]
      have hoi : o < i := lt_of_le_of_ne (ho i) (Ne.symm hio)
      refine RelBuild.lamTw_norm hσ _ _ ?_ s
      rw [RelBuild.norm_tw hσ, map_inv₀, ← mul_inv, (hnf i j hoi hij).1, inv_one]
  refine ⟨D.recoord hσ (Recoord.ofUpper hσ ρ hK hN), D.recoord_reparam hσ _, e₁,
    fun j k hj hk s t => ?_⟩
  have hoj : j ≠ o := hj.ne'
  rw [recoord_μ, Recoord.ofUpper_θ, Recoord.upperθ_of_lt (hj.trans hk), Recoord.upperθ_of_lt hj,
    Recoord.upperθ_of_lt hk]
  simp only [ρ, ite_eq_left (rfl : o = o), ite_eq_right hoj, AddEquiv.refl_symm,
    AddEquiv.refl_apply, RelBuild.lamTw_apply]
  rw [(hnf j k hj hk).2, RelBuild.tw_mul, RelBuild.tw_tw_self hσ, RelBuild.tw_tw_self hσ]
  field_simp [hc0 j k]

theorem star_consequences (hσ : ∀ c, σ (σ c) = c) (hne : ∃ θ, σ θ ≠ θ) (o : Fin r)
    {α : Fin r → Fin r → Bool}
    (hα : ∀ j k, o < j → j < k → ∀ s t, D.μ o j k s t = RelBuild.tw σ (α j k) s * t) :
    (∀ i j k, o < i → i < j → j < k → ∀ s t, D.μ i j k s t = RelBuild.tw σ (α j k) s * t) ∧
      ∀ i j k, o < i → i < j → j < k → α i k = xor (α j k) (α i j) := by
  have key : ∀ i j k, o < i → i < j → j < k → ∀ a b c, RelBuild.tw σ (α i k) a *
      D.μ i j k b c = RelBuild.tw σ (α j k) (RelBuild.tw σ (α i j) a * b) * c := by
    intro i j k hi hij hjk a b c
    have h := D.μ_tetra (i := o) (j := i) (k := j) (l := k) hi.ne (hi.trans hij).ne
      (hi.trans (hij.trans hjk)).ne hij.ne (hij.trans hjk).ne hjk.ne a b c
    rwa [hα i k hi (hij.trans hjk), hα j k (hi.trans hij) hjk, hα i j hi hij] at h
  have part₁ : ∀ i j k, o < i → i < j → j < k → ∀ s t,
      D.μ i j k s t = RelBuild.tw σ (α j k) s * t := by
    intro i j k hi hij hjk b c
    simpa using key i j k hi hij hjk 1 b c
  refine ⟨part₁, fun i j k hi hij hjk => RelBuild.eq_of_tw_eq hne fun a => ?_⟩
  have h := key i j k hi hij hjk a 1 1
  rw [part₁ i j k hi hij hjk, RelBuild.tw_one, mul_one, mul_one, mul_one, mul_one,
    RelBuild.tw_tw hσ] at h
  exact h

theorem exists_reparam_increasing [Finite F] [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    (hne : ∃ θ, σ θ ≠ θ) (h3 : 3 ≤ r) :
    ∃ D' : SUData r σ G, D'.Reparam D ∧ ∀ i j k, i < j → j < k → ∀ s t, D'.μ i j k s t = s * t := by
  let o : Fin r := ⟨0, by omega⟩
  let e : Fin r := ⟨1, by omega⟩
  have ho : ∀ i, o ≤ i := fun i => Fin.le_def.2 (Nat.zero_le _)
  have hoe : o < e := Fin.lt_def.2 Nat.zero_lt_one
  have he : ∀ j, o < j → j = e ∨ e < j := by
    intro j hj
    have hj' : 0 < j.val := hj
    rcases Nat.lt_or_ge 1 j.val with h | h
    · exact Or.inr h
    · exact Or.inl (Fin.ext (by simp only [e]; omega))
  obtain ⟨D₁, h₁, α, hα⟩ := D.exists_reparam_star hσ hne o ho
  obtain ⟨hμ₁, hcoc⟩ := D₁.star_consequences hσ hne o hα
  let τ : Fin r → Bool := fun k => if e < k then α e k else false
  have hτ : ∀ j k, o < j → j < k → α j k = xor (τ k) (τ j) := by
    intro j k hj hk
    rcases he j hj with rfl | hej
    · simp only [τ, ite_eq_left hk, ite_eq_right (lt_irrefl _), Bool.xor_false]
    · simp only [τ, ite_eq_left hej, ite_eq_left (hej.trans hk), hcoc e j k hoe hej hk,
        Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
  have hμ : ∀ i j k, i < j → j < k → ∀ s t, D₁.μ i j k s t = RelBuild.tw σ (α j k) s * t := by
    intro i j k hij hjk s t
    by_cases hio : i = o
    · subst hio
      exact hα j k hij hjk s t
    · exact hμ₁ i j k (lt_of_le_of_ne (ho i) (Ne.symm hio)) hij hjk s t
  let ρ : Fin r → Fin r → F ≃+ F := fun _ k => RelBuild.lamTw hσ (τ k) one_ne_zero
  have hK : ∀ i j, i < j → ∀ c s, σ c = c → ρ i j (c * s) = c * ρ i j s :=
    fun _ _ _ _ s hc => RelBuild.lamTw_smul hσ _ _ hc s
  have hN : ∀ i j, i < j → ∀ s, σ (ρ i j s) * ρ i j s = σ s * s :=
    fun _ _ _ s => RelBuild.lamTw_norm hσ _ _ (by rw [map_one, one_mul]) s
  refine ⟨D₁.recoord hσ (Recoord.ofUpper hσ ρ hK hN), (D₁.recoord_reparam hσ _).trans h₁,
    fun i j k hij hjk s t => ?_⟩
  rw [recoord_μ, Recoord.ofUpper_θ, Recoord.upperθ_of_lt (hij.trans hjk), Recoord.upperθ_of_lt hij,
    Recoord.upperθ_of_lt hjk]
  simp only [ρ, RelBuild.lamTw_apply, RelBuild.lamTw_symm_apply, one_mul, inv_one]
  rw [hμ i j k hij hjk, hτ j k (lt_of_le_of_lt (ho i) hij) hjk, RelBuild.tw_tw hσ]
  simp only [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
  rw [RelBuild.tw_mul, RelBuild.tw_tw_self hσ, RelBuild.tw_tw_self hσ]

theorem mul_of_increasing [Finite F] [CharP F 2] (hσ : ∀ c, σ (σ c) = c) (hne : ∃ θ, σ θ ≠ θ)
    (h : ∀ i j k, i < j → j < k → ∀ s t, D.μ i j k s t = s * t) :
    ∀ i j k, i ≠ j → j ≠ k → i ≠ k → ∀ s t, D.μ i j k s t = s * t := by
  have hrev : ∀ i j k, i ≠ j → j ≠ k → i ≠ k → (∀ s t, D.μ i j k s t = s * t) →
      ∀ s t, D.μ k j i s t = s * t := by
    intro i j k hij hjk hik hμ t s
    rw [D.μ_rev hij hjk hik, hμ, map_mul, hσ, hσ, mul_comm]
  have hsr : ∀ i j k, i ≠ j → j ≠ k → i ≠ k → (∀ s t, D.μ i j k s t = s * t) →
      D.ShortRel k j i (· * ·) := by
    intro i j k hij hjk hik hμ a b d ha hb hd s t
    rw [D.shortRel_μ hij hjk hik a b d ha hb hd s t]
    simp only [hμ, mul_comm]
  have hall : ∀ i j k, i < j → j < k →
      (∀ s t, D.μ k j i s t = s * t) ∧ (∀ s t, D.μ k i j s t = s * t) ∧
        (∀ s t, D.μ i k j s t = s * t) ∧ (∀ s t, D.μ j i k s t = s * t) ∧
          (∀ s t, D.μ j k i s t = s * t) := by
    intro i j k hij hjk
    have hik := hij.trans hjk
    have h₁ := hrev i j k hij.ne hjk.ne hik.ne (h i j k hij hjk)
    have h₂ : ∀ s t, D.μ k i j s t = s * t := fun q p =>
      D.mul_of_d7b hσ hne hij.ne hjk.ne hik.ne
        (hsr i j k hij.ne hjk.ne hik.ne (h i j k hij hjk)) q p
    have h₃ : ∀ s t, D.μ i k j s t = s * t := fun q p =>
      D.mul_of_d7b hσ hne hjk.ne' hij.ne' hik.ne' (hsr k j i hjk.ne' hij.ne' hik.ne' h₁) q p
    exact ⟨h₁, h₂, h₃, hrev k i j hik.ne' hij.ne hjk.ne' h₂, hrev i k j hik.ne hjk.ne' hij.ne h₃⟩
  intro p m q hpm hmq hpq s t
  rcases lt_or_gt_of_ne hpm with h₁ | h₁ <;> rcases lt_or_gt_of_ne hmq with h₂ | h₂ <;>
    rcases lt_or_gt_of_ne hpq with h₃ | h₃
  · exact h p m q h₁ h₂ s t
  · exact absurd (h₁.trans h₂) (not_lt.2 h₃.le)
  · exact (hall p q m h₃ h₂).2.2.1 s t
  · exact (hall q p m h₃ h₁).2.2.2.2 s t
  · exact (hall m p q h₁ h₃).2.2.2.1 s t
  · exact (hall m q p h₂ h₃).2.1 s t
  · exact absurd (h₂.trans h₁) (not_lt.2 h₃.le)
  · exact (hall q m p h₂ h₁).1 s t

theorem exists_reparam_mul [Finite F] [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    (hne : ∃ θ, σ θ ≠ θ) :
    ∃ D' : SUData r σ G, D'.Reparam D ∧
      ∀ i j k, i ≠ j → j ≠ k → i ≠ k → ∀ s t, D'.μ i j k s t = s * t := by
  by_cases h3 : 3 ≤ r
  · obtain ⟨D', hD', hinc⟩ := D.exists_reparam_increasing hσ hne h3
    exact ⟨D', hD', D'.mul_of_increasing hσ hne hinc⟩
  · refine ⟨D, D.reparam_refl, fun i j k hij hjk hik => absurd ?_ h3⟩
    have h₁ : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have h₂ : j.val ≠ k.val := fun h => hjk (Fin.ext h)
    have h₃ : i.val ≠ k.val := fun h => hik (Fin.ext h)
    have := i.isLt
    have := j.isLt
    have := k.isLt
    omega

end RelBuild.SUData

variable {r : ℕ} {F : Type*} [Field F] {σ : F ≃+* F} {G : Type*} [Group G]

theorem PreSURelations.exists_suRelations [Finite F] [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    (hne : ∃ c, σ c ≠ c) (P : PreSURelations r σ G) :
    ∃ R : SURelations r σ G, R.ξL = P.ξL ∧
      ∀ a b, idx a ≠ idx b → ∃ θ : F ≃+ F, ∀ c, R.ξ a b c = P.ξ a b (θ c) := by
  obtain ⟨D, ⟨hL, hξ⟩, hmul⟩ := P.toData.exists_reparam_mul hσ hne
  exact ⟨D.toPreRelations.toSURelations hσ fun i j k hij hjk hik s t => by
    rw [D.hμ i j k hij hjk hik, hmul i j k hij hjk hik], hL, hξ⟩

end CFSG.Timmesfeld.Transvection
