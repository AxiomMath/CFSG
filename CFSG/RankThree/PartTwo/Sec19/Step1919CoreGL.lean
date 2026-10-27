module

public import CFSG.RankThree.PartTwo.Sec19.Step1919NarrowRank
import CFSG.RankThree.PartTwo.Sec6.Item612Plus

public section

namespace CFSG.RankThree.PartTwo.Sec19

namespace Step1919CoreProof

variable {V : Type} [Group V] [Finite V]

theorem mem_of_apply_mem {B : Subgroup V} {σ : MulAut V} (hσB : ∀ b ∈ B, σ b ∈ B) {x : V}
    (hx : σ x ∈ B) : x ∈ B := by
  have hle : B.map σ.toMonoidHom ≤ B := by
    rintro _ ⟨y, hy, rfl⟩
    exact hσB y hy
  have heq : B.map σ.toMonoidHom = B :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Subgroup.card_map_of_injective σ.injective])
  rw [← heq] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := σ.injective hyx
  rwa [← this]

omit [Finite V] in
theorem pow_apply_mem {B : Subgroup V} {σ : MulAut V} (hσB : ∀ b ∈ B, σ b ∈ B) (j : ℕ) :
    ∀ b ∈ B, (σ ^ j) b ∈ B := by
  induction j with
  | zero => intro b hb; simpa using hb
  | succ j ih =>
    intro b hb
    rw [pow_succ', MulAut.mul_apply]
    exact hσB _ (ih b hb)

theorem mul_inv_mem_of_index_three (hV : ∀ a b : V, a * b = b * a) (hVe : ∀ v : V, v ^ 3 = 1)
    {B C : Subgroup V} (hBC : B ≤ C) (hC : Nat.card C = 3 * Nat.card B)
    {σ : MulAut V} (hσ3 : ∃ k : ℕ, σ ^ 3 ^ k = 1) (hσB : ∀ b ∈ B, σ b ∈ B)
    (hσC : ∀ x ∈ C, σ x ∈ C) {x : V} (hx : x ∈ C) : σ x * x⁻¹ ∈ B := by
  classical
  obtain ⟨k, hk⟩ := hσ3
  by_cases hxB : x ∈ B
  · exact B.mul_mem (hσB x hxB) (B.inv_mem hxB)
  have hx1 : x ≠ 1 := fun h => hxB (h ▸ B.one_mem)
  have hxo : orderOf x = 3 := orderOf_eq_prime (hVe x) hx1
  have hCeq : B ⊔ Subgroup.zpowers x = C := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le hBC (Subgroup.zpowers_le.mpr hx))
    rw [Step1919NarrowRank.card_sup_zpowers_of_orderOf B hxo hxB (fun z _ => hV z x), hC,
      mul_comm]
  have hBN : Subgroup.zpowers x ≤ Subgroup.normalizer (B : Set V) := fun g _ => by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hV g h, mul_inv_cancel_right]
  have hσx : σ x ∈ ((B ⊔ Subgroup.zpowers x : Subgroup V) : Set V) := by
    rw [SetLike.mem_coe, hCeq]
    exact hσC x hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left B _ hBN] at hσx
  obtain ⟨b, hb, w, hw, hbw⟩ := hσx
  beta_reduce at hbw
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hw)
  rw [hxo, Finset.mem_range] at hm
  interval_cases m
  ·
    rw [pow_zero, mul_one] at hbw
    exact absurd (mem_of_apply_mem hσB (hbw ▸ hb)) hxB
  ·
    rw [← hbw, pow_one, mul_inv_cancel_right]
    exact hb
  ·
    have hsq : (b * x ^ 2) ^ 2 = b * b * x := by
      calc (b * x ^ 2) ^ 2 = b * (x ^ 2 * b) * x ^ 2 := by rw [pow_two]; group
        _ = b * (b * x ^ 2) * x ^ 2 := by rw [hV (x ^ 2) b]
        _ = b * b * (x ^ 3 * x) := by group
        _ = b * b * x := by rw [hVe x, one_mul]
    have hσσ : (σ ^ 2) x * x⁻¹ ∈ B := by
      have e : (σ ^ 2) x = σ b * (b * b * x) := by
        rw [pow_two, MulAut.mul_apply, ← hbw, map_mul, map_pow, ← hbw, hsq]
      rw [e, show σ b * (b * b * x) * x⁻¹ = σ b * (b * b) by group]
      exact B.mul_mem (hσB b hb) (B.mul_mem hb hb)
    have hσ2B : ∀ c ∈ B, (σ ^ 2) c ∈ B := pow_apply_mem hσB 2
    have hj : ∀ j : ℕ, ((σ ^ 2) ^ j) x * x⁻¹ ∈ B := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        set β := ((σ ^ 2) ^ j) x * x⁻¹ with hβ
        set γ := (σ ^ 2) x * x⁻¹ with hγ
        have e1 : ((σ ^ 2) ^ j) x = β * x := by rw [hβ]; group
        have e2 : (σ ^ 2) x = γ * x := by rw [hγ]; group
        rw [pow_succ', MulAut.mul_apply, e1, map_mul, e2,
          show (σ ^ 2) β * (γ * x) * x⁻¹ = (σ ^ 2) β * γ by group]
        exact B.mul_mem (hσ2B β ih) hσσ
    have hodd : Odd (3 ^ k) := Odd.pow (by decide)
    have h2 : 2 * ((3 ^ k + 1) / 2) = 3 ^ k + 1 :=
      Nat.two_mul_div_two_of_even (Odd.add_one hodd)
    have hσeq : (σ ^ 2) ^ ((3 ^ k + 1) / 2) = σ := by
      rw [← pow_mul, h2, pow_succ, hk, one_mul]
    have := hj ((3 ^ k + 1) / 2)
    rwa [hσeq] at this

omit [Finite V] in
theorem eq_on_sup_zpowers {τ₁ τ₂ : MulAut V} {W : Subgroup V} (hW : ∀ w ∈ W, τ₁ w = τ₂ w)
    {f : V} (hf : τ₁ f = τ₂ f) :
    ∀ v ∈ W ⊔ Subgroup.zpowers f, τ₁ v = τ₂ v := by
  have hle : W ⊔ Subgroup.zpowers f ≤ τ₁.toMonoidHom.eqLocus τ₂.toMonoidHom :=
    sup_le (fun w hw => hW w hw) (Subgroup.zpowers_le.mpr hf)
  exact fun v hv => hle hv

theorem card_sup_zpowers (hV : ∀ a b : V, a * b = b * a) (hVe : ∀ v : V, v ^ 3 = 1)
    {W : Subgroup V} {f : V} (hf : f ∉ W) :
    Nat.card (W ⊔ Subgroup.zpowers f : Subgroup V) = 3 * Nat.card W := by
  have hf1 : f ≠ 1 := fun h => hf (h ▸ W.one_mem)
  rw [Step1919NarrowRank.card_sup_zpowers_of_orderOf W (orderOf_eq_prime (hVe f) hf1) hf
    (fun z _ => hV z f), mul_comm]

theorem card_closure_le_of_flag (hV : ∀ a b : V, a * b = b * a) (hVe : ∀ v : V, v ^ 3 = 1)
    (hV27 : Nat.card V = 27) {W F : Subgroup V} (hWF : W ≤ F) (hW3 : Nat.card W = 3)
    (hF9 : Nat.card F = 9) {S : Set (MulAut V)} (hS3 : ∀ σ ∈ S, ∃ k : ℕ, σ ^ 3 ^ k = 1)
    (hSW : ∀ σ ∈ S, ∀ w ∈ W, σ w ∈ W) (hSF : ∀ σ ∈ S, ∀ f ∈ F, σ f ∈ F) :
    Nat.card (Subgroup.closure S) ≤ 27 := by
  classical
  set P : MulAut V → Prop := fun τ => (∀ w ∈ W, τ w = w) ∧ (∀ f ∈ F, τ f * f⁻¹ ∈ W) ∧
    (∀ v, τ v * v⁻¹ ∈ F) with hP
  have hPS : ∀ σ ∈ S, P σ := by
    intro σ hσ
    refine ⟨fun w hw => ?_, fun f hf => ?_, fun v => ?_⟩
    · have h := mul_inv_mem_of_index_three hV hVe (bot_le : (⊥ : Subgroup V) ≤ W)
        (by rw [hW3, Subgroup.card_bot]) (hS3 σ hσ)
        (fun b hb => by rw [Subgroup.mem_bot.mp hb, map_one]; exact Subgroup.one_mem _)
        (hSW σ hσ) hw
      rwa [Subgroup.mem_bot, mul_inv_eq_one] at h
    · exact mul_inv_mem_of_index_three hV hVe hWF (by rw [hF9, hW3]) (hS3 σ hσ) (hSW σ hσ)
        (hSF σ hσ) hf
    · exact mul_inv_mem_of_index_three hV hVe le_top (by rw [Subgroup.card_top, hV27, hF9])
        (hS3 σ hσ) (hSF σ hσ) (fun _ _ => Subgroup.mem_top _) (Subgroup.mem_top v)
  have hPF : ∀ τ, P τ → ∀ f ∈ F, τ f ∈ F := fun τ hτ f hf => by
    have := F.mul_mem (hWF (hτ.2.1 f hf)) hf
    rwa [inv_mul_cancel_right] at this
  have hP1 : P 1 := ⟨fun w _ => rfl, fun f _ => by simp, fun v => by simp⟩
  have hPmul : ∀ τ₁ τ₂, P τ₁ → P τ₂ → P (τ₁ * τ₂) := by
    intro τ₁ τ₂ h₁ h₂
    refine ⟨fun w hw => ?_, fun f hf => ?_, fun v => ?_⟩
    · rw [MulAut.mul_apply, h₂.1 w hw, h₁.1 w hw]
    · rw [MulAut.mul_apply]
      have e : τ₂ f = (τ₂ f * f⁻¹) * f := by group
      rw [e, map_mul, h₁.1 _ (h₂.2.1 f hf),
        show (τ₂ f * f⁻¹) * τ₁ f * f⁻¹ = (τ₂ f * f⁻¹) * (τ₁ f * f⁻¹) by group]
      exact W.mul_mem (h₂.2.1 f hf) (h₁.2.1 f hf)
    · rw [MulAut.mul_apply]
      have e : τ₂ v = (τ₂ v * v⁻¹) * v := by group
      rw [e, map_mul,
        show τ₁ (τ₂ v * v⁻¹) * τ₁ v * v⁻¹ = τ₁ (τ₂ v * v⁻¹) * (τ₁ v * v⁻¹) by group]
      exact F.mul_mem (hPF τ₁ h₁ _ (h₂.2.2 v)) (h₁.2.2 v)
  have hPinv : ∀ τ, P τ → P τ⁻¹ := by
    intro τ h
    have hτF : ∀ f ∈ F, τ⁻¹ f ∈ F := fun f hf =>
      mem_of_apply_mem (hPF τ h) (by rw [MulAut.apply_inv_self]; exact hf)
    refine ⟨fun w hw => ?_, fun f hf => ?_, fun v => ?_⟩
    · calc τ⁻¹ w = τ⁻¹ (τ w) := by rw [h.1 w hw]
        _ = w := MulAut.inv_apply_self _ τ w
    · have h1 := h.2.1 _ (hτF f hf)
      rw [MulAut.apply_inv_self] at h1
      have := W.inv_mem h1
      rwa [mul_inv_rev, inv_inv] at this
    · have h1 := h.2.2 (τ⁻¹ v)
      rw [MulAut.apply_inv_self] at h1
      have := F.inv_mem h1
      rwa [mul_inv_rev, inv_inv] at this
  have hPcl : ∀ τ ∈ Subgroup.closure S, P τ := by
    intro τ hτ
    induction hτ using Subgroup.closure_induction with
    | mem σ hσ => exact hPS σ hσ
    | one => exact hP1
    | mul a b _ _ ha hb => exact hPmul a b ha hb
    | inv a _ ha => exact hPinv a ha
  obtain ⟨f₀, hf₀F, hf₀W⟩ : ∃ f ∈ F, f ∉ W := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (show F ≤ W from h)
    omega
  obtain ⟨v₀, hv₀⟩ : ∃ v : V, v ∉ F := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (show (⊤ : Subgroup V) ≤ F from fun v _ => h v)
    rw [Subgroup.card_top] at this
    omega
  have hWf : W ⊔ Subgroup.zpowers f₀ = F :=
    Subgroup.eq_of_le_of_card_ge (sup_le hWF (Subgroup.zpowers_le.mpr hf₀F))
      (by rw [card_sup_zpowers hV hVe hf₀W, hW3, hF9])
  have hFv : F ⊔ Subgroup.zpowers v₀ = ⊤ :=
    Subgroup.eq_of_le_of_card_ge le_top
      (by rw [card_sup_zpowers hV hVe hv₀, hF9, Subgroup.card_top, hV27])
  have hgen : ∀ τ₁ τ₂ : MulAut V, P τ₁ → P τ₂ → τ₁ f₀ = τ₂ f₀ → τ₁ v₀ = τ₂ v₀ → τ₁ = τ₂ := by
    intro τ₁ τ₂ h₁ h₂ hf hv
    have hW : ∀ w ∈ W, τ₁ w = τ₂ w := fun w hw => (h₁.1 w hw).trans (h₂.1 w hw).symm
    have hF := eq_on_sup_zpowers hW hf
    rw [hWf] at hF
    have hall := eq_on_sup_zpowers hF hv
    rw [hFv] at hall
    exact MulEquiv.ext fun v => hall v (Subgroup.mem_top v)
  have hinj : Function.Injective (fun τ : Subgroup.closure S =>
      ((⟨τ.1 f₀ * f₀⁻¹, (hPcl τ.1 τ.2).2.1 f₀ hf₀F⟩ : W),
        (⟨τ.1 v₀ * v₀⁻¹, (hPcl τ.1 τ.2).2.2 v₀⟩ : F))) := by
    intro τ₁ τ₂ h
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
    exact Subtype.ext (hgen _ _ (hPcl _ τ₁.2) (hPcl _ τ₂.2) (mul_right_cancel h.1)
      (mul_right_cancel h.2))
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_prod, hW3, hF9] at this

theorem card_closure_le_of_compl (hV : ∀ a b : V, a * b = b * a) (hVe : ∀ v : V, v ^ 3 = 1)
    (hV27 : Nat.card V = 27) {W F : Subgroup V} (hWF : W ⊓ F = ⊥) (hW3 : Nat.card W = 3)
    (hF9 : Nat.card F = 9) {S : Set (MulAut V)} (hS3 : ∀ σ ∈ S, ∃ k : ℕ, σ ^ 3 ^ k = 1)
    (hSW : ∀ σ ∈ S, ∀ w ∈ W, σ w ∈ W) (hSF : ∀ σ ∈ S, ∀ f ∈ F, σ f ∈ F) :
    Nat.card (Subgroup.closure S) ≤ 81 := by
  classical
  set P : MulAut V → Prop := fun τ => (∀ w ∈ W, τ w = w) ∧ (∀ f ∈ F, τ f ∈ F) with hP
  have hPS : ∀ σ ∈ S, P σ := by
    intro σ hσ
    refine ⟨fun w hw => ?_, hSF σ hσ⟩
    have h := mul_inv_mem_of_index_three hV hVe (bot_le : (⊥ : Subgroup V) ≤ W)
      (by rw [hW3, Subgroup.card_bot]) (hS3 σ hσ)
      (fun b hb => by rw [Subgroup.mem_bot.mp hb, map_one]; exact Subgroup.one_mem _)
      (hSW σ hσ) hw
    rwa [Subgroup.mem_bot, mul_inv_eq_one] at h
  have hP1 : P 1 := ⟨fun w _ => rfl, fun f hf => hf⟩
  have hPmul : ∀ τ₁ τ₂, P τ₁ → P τ₂ → P (τ₁ * τ₂) := by
    intro τ₁ τ₂ h₁ h₂
    refine ⟨fun w hw => ?_, fun f hf => ?_⟩
    · rw [MulAut.mul_apply, h₂.1 w hw, h₁.1 w hw]
    · rw [MulAut.mul_apply]
      exact h₁.2 _ (h₂.2 f hf)
  have hPinv : ∀ τ, P τ → P τ⁻¹ := by
    intro τ h
    refine ⟨fun w hw => ?_, fun f hf => ?_⟩
    · calc τ⁻¹ w = τ⁻¹ (τ w) := by rw [h.1 w hw]
        _ = w := MulAut.inv_apply_self _ τ w
    · exact mem_of_apply_mem h.2 (by rw [MulAut.apply_inv_self]; exact hf)
  have hPcl : ∀ τ ∈ Subgroup.closure S, P τ := by
    intro τ hτ
    induction hτ using Subgroup.closure_induction with
    | mem σ hσ => exact hPS σ hσ
    | one => exact hP1
    | mul a b _ _ ha hb => exact hPmul a b ha hb
    | inv a _ ha => exact hPinv a ha
  obtain ⟨f₁, hf₁F, hf₁⟩ : ∃ f ∈ F, f ∉ (⊥ : Subgroup V) := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (show F ≤ ⊥ from h)
    rw [Subgroup.card_bot] at this
    omega
  obtain ⟨f₂, hf₂F, hf₂⟩ : ∃ f ∈ F, f ∉ (⊥ : Subgroup V) ⊔ Subgroup.zpowers f₁ := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (show F ≤ (⊥ : Subgroup V) ⊔ Subgroup.zpowers f₁ from h)
    rw [card_sup_zpowers hV hVe hf₁, Subgroup.card_bot] at this
    omega
  have hF12 : (⊥ : Subgroup V) ⊔ Subgroup.zpowers f₁ ⊔ Subgroup.zpowers f₂ = F :=
    Subgroup.eq_of_le_of_card_ge
      (sup_le (sup_le bot_le (Subgroup.zpowers_le.mpr hf₁F)) (Subgroup.zpowers_le.mpr hf₂F))
      (by rw [card_sup_zpowers hV hVe hf₂, card_sup_zpowers hV hVe hf₁, Subgroup.card_bot, hF9])
  have hFW : F ⊔ W = ⊤ := by
    have hWN : F ≤ Subgroup.normalizer (W : Set V) := fun g _ => by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      rw [hV g h, mul_inv_cancel_right]
    have h1 := Sec6.card_sup_mul_card_inf hWN
    rw [inf_comm, hWF, Subgroup.card_bot, mul_one, hF9, hW3] at h1
    exact Subgroup.eq_of_le_of_card_ge le_top (by rw [h1, Subgroup.card_top, hV27])
  have hgen : ∀ τ₁ τ₂ : MulAut V, P τ₁ → P τ₂ → τ₁ f₁ = τ₂ f₁ → τ₁ f₂ = τ₂ f₂ → τ₁ = τ₂ := by
    intro τ₁ τ₂ h₁ h₂ h1 h2
    have h0 : ∀ v ∈ (⊥ : Subgroup V), τ₁ v = τ₂ v := fun v hv => by
      rw [Subgroup.mem_bot.mp hv, map_one, map_one]
    have hF := eq_on_sup_zpowers (eq_on_sup_zpowers h0 h1) h2
    rw [hF12] at hF
    have hW : ∀ w ∈ W, τ₁ w = τ₂ w := fun w hw => (h₁.1 w hw).trans (h₂.1 w hw).symm
    have hle : F ⊔ W ≤ τ₁.toMonoidHom.eqLocus τ₂.toMonoidHom :=
      sup_le (fun v hv => hF v hv) (fun w hw => hW w hw)
    rw [hFW] at hle
    exact MulEquiv.ext fun v => hle (Subgroup.mem_top v)
  have hinj : Function.Injective (fun τ : Subgroup.closure S =>
      ((⟨τ.1 f₁, (hPcl τ.1 τ.2).2 f₁ hf₁F⟩ : F), (⟨τ.1 f₂, (hPcl τ.1 τ.2).2 f₂ hf₂F⟩ : F))) := by
    intro τ₁ τ₂ h
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
    exact Subtype.ext (hgen _ _ (hPcl _ τ₁.2) (hPcl _ τ₂.2) h.1 h.2)
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_prod, hF9] at this

theorem eq_or_eq_top_of_invariant (hV : ∀ a b : V, a * b = b * a) (hVe : ∀ v : V, v ^ 3 = 1)
    (hV27 : Nat.card V = 27) {F : Subgroup V} (hF9 : Nat.card F = 9) {S : Set (MulAut V)}
    (hS3 : ∀ σ ∈ S, ∃ k : ℕ, σ ^ 3 ^ k = 1) (hSF : ∀ σ ∈ S, ∀ f ∈ F, σ f ∈ F)
    (hX : 81 < Nat.card (Subgroup.closure S)) {W : Subgroup V}
    (hSW : ∀ σ ∈ S, ∀ w ∈ W, σ w ∈ W) (hW1 : W ≠ ⊥) : W = F ∨ W = ⊤ := by
  classical
  have hWdvd : Nat.card W ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hV27, ← Subgroup.card_top (G := V)]
    exact Subgroup.card_dvd_of_le le_top
  have hWFN : W ≤ Subgroup.normalizer (F : Set V) := fun g _ => by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hV g h, mul_inv_cancel_right]
  have hcard := Sec6.card_sup_mul_card_inf hWFN
  have hsup : Nat.card (W ⊔ F : Subgroup V) ≤ 27 := by
    rw [← hV27, ← Subgroup.card_top (G := V)]
    exact Subgroup.card_le_of_le le_top
  obtain ⟨j, hj3, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hWdvd
  interval_cases j
  · exact absurd (Subgroup.card_eq_one.mp (by rw [hj]; rfl)) hW1
  ·
    rw [pow_one] at hj
    exfalso
    by_cases hWF : W ≤ F
    · have := card_closure_le_of_flag hV hVe hV27 hWF hj hF9 hS3 hSW hSF
      omega
    · have hinf : W ⊓ F = ⊥ := by
        have hdvd : Nat.card (W ⊓ F : Subgroup V) ∣ 3 := hj ▸ Subgroup.card_dvd_of_le inf_le_left
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
        · exact Subgroup.card_eq_one.mp h
        · exfalso
          apply hWF
          have heq : W ⊓ F = W := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hj])
          rw [← heq]
          exact inf_le_right
      have := card_closure_le_of_compl hV hVe hV27 hinf hj hF9 hS3 hSW hSF
      omega
  ·
    left
    by_contra hWF
    have hinf3 : Nat.card (W ⊓ F : Subgroup V) = 3 := by
      have hdvd : Nat.card (W ⊓ F : Subgroup V) ∣ 3 ^ 2 := by
        rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hF9]
        exact Subgroup.card_dvd_of_le inf_le_right
      obtain ⟨i, hi2, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
      rw [hj, hF9] at hcard
      interval_cases i
      · rw [hi] at hcard
        omega
      · rw [hi, pow_one]
      · exfalso
        apply hWF
        have h1 : W ⊓ F = W := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hi, hj])
        have h2 : W ⊓ F = F :=
          Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hi, hF9]; norm_num)
        exact h1.symm.trans h2
    have := card_closure_le_of_flag hV hVe hV27 inf_le_right hinf3 hF9 hS3
      (fun σ hσ w hw => ⟨hSW σ hσ w hw.1, hSF σ hσ w hw.2⟩) hSF
    omega
  ·
    right
    exact Subgroup.eq_of_le_of_card_ge le_top (by rw [hj, Subgroup.card_top, hV27]; norm_num)

end Step1919CoreProof

end CFSG.RankThree.PartTwo.Sec19
