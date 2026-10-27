module

public import CFSG.Quasithin.Vol2.Ch3Sec1L319SevenBlk

public section

namespace CFSG.Quasithin.H13.L319

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.Ch3z G6

section Block

variable {V : Type} [CommGroup V]

theorem exists_order_three_of_block_five_cv {H₁ M D : Subgroup (MulAut V)}
    (θ : ↥H₁ ≃* Equiv.Perm (Fin 5))
    (hstab : ∃ p : Fin 5, ((M ⊓ H₁).subgroupOf H₁).map θ.toMonoidHom =
      MulAction.stabilizer (Equiv.Perm (Fin 5)) p)
    {a : MulAut V} (haH : a ∈ H₁) (haM : a ∈ M) (haD : a ∈ D) (ha2 : a * a = 1)
    (hsg : Equiv.Perm.sign (θ ⟨a, haH⟩) = -1)
    (hDM : ∀ g ∈ M, ∀ d ∈ D, g * d * g⁻¹ ∈ D) :
    ∃ x : MulAut V, x ∈ H₁ ∧ x ∈ D ∧ orderOf x = 3 := by
  obtain ⟨p, hp⟩ := hstab
  set a₀ : ↥H₁ := ⟨a, haH⟩ with ha₀
  set τ : Equiv.Perm (Fin 5) := θ a₀ with hτ
  have hτp : τ p = p := by
    have h1 : θ a₀ ∈ ((M ⊓ H₁).subgroupOf H₁).map θ.toMonoidHom :=
      ⟨a₀, Subgroup.mem_subgroupOf.mpr ⟨haM, haH⟩, rfl⟩
    rw [hp, MulAction.mem_stabilizer_iff] at h1
    exact h1
  have hτ2 : τ * τ = 1 := by
    rw [hτ, ← map_mul]
    have : a₀ * a₀ = 1 := Subtype.ext ha2
    rw [this, map_one]
  obtain ⟨γ, hγp, hγ3, hγ1⟩ := perm5_fact p τ hτp hτ2 hsg
  have hγst : γ ∈ ((M ⊓ H₁).subgroupOf H₁).map θ.toMonoidHom := by
    rw [hp, MulAction.mem_stabilizer_iff]
    exact hγp
  obtain ⟨g₀, hg₀, hθg₀⟩ := hγst
  have hg₀M : (g₀ : MulAut V) ∈ M := (Subgroup.mem_subgroupOf.mp hg₀).1
  set x₀ : ↥H₁ := g₀ * a₀ * g₀⁻¹ * a₀⁻¹ with hx₀
  have hθx : θ x₀ = γ * τ * γ⁻¹ * τ⁻¹ := by
    have hθg : θ g₀ = γ := hθg₀
    rw [hx₀, map_mul, map_mul, map_mul, map_inv, map_inv, hθg]
  have hord : orderOf x₀ = 3 := by
    have h1 : orderOf (θ x₀) = 3 := by
      rw [hθx]
      exact orderOf_eq_prime hγ3 hγ1
    rwa [MulEquiv.orderOf_eq] at h1
  have hxD : (x₀ : MulAut V) ∈ D := by
    have e : (x₀ : MulAut V) = (g₀ : MulAut V) * a * (g₀ : MulAut V)⁻¹ * a⁻¹ := rfl
    rw [e]
    exact D.mul_mem (hDM _ hg₀M a haD) (D.inv_mem haD)
  exact ⟨(x₀ : MulAut V), x₀.2, hxD, by rw [Subgroup.orderOf_coe, hord]⟩

end Block

section Main

variable {V : Type} [CommGroup V] [Finite V] {X T M : Subgroup (MulAut V)}
  {𝓗 : Finset (Subgroup (MulAut V))}

theorem BlkCtx.cover_dichotomy_cv (h : BlkCtx X T M 𝓗) (hX : IsRankTwoQuotient ↥X)
    (hsym : ∀ H ∈ 𝓗, ∃ m, SymBlk M H m) (hstrong : ¬ IsStrongFFModule X)
    {A D : Subgroup (MulAut V)} (hAT : A ≤ T) (hAe : IsElemAbelian2 A) (hA1 : A ≠ ⊥)
    (hoff : Nat.card V ≤ Nat.card A * Nat.card (fixV A))
    (hAD : A ≤ D) (hDM : ∀ g ∈ M, ∀ d ∈ D, g * d * g⁻¹ ∈ D)
    (h5 : ∃ x ∈ ffJ X, orderOf x = 5) :
    (∃ _ : ↥X ≃* Equiv.Perm (Fin 5), ∃ x : MulAut V, x ∈ X ∧ x ∈ D ∧ orderOf x = 3) ∨
    (∃ x t : MulAut V, x ∈ X ∧ x ∈ D ∧ orderOf x = 3 ∧ t ∈ T ∧ Commute x (t * x * t⁻¹) ∧
      t * x * t⁻¹ ∉ Subgroup.zpowers x) := by
  classical
  obtain ⟨x5, hx5J, hx5⟩ := h5
  have hTM : T ≤ M := h.mp.le
  have hAX : A ≤ X := hAT.trans h.mp.isSylow.1
  have hle2 := h.card_le_two hX hsym
  have hpos : 0 < 𝓗.card := Finset.card_pos.mpr h.nonempty
  have h1or2 : 𝓗.card = 1 ∨ 𝓗.card = 2 := by omega
  have hcardperm : ∀ (m : ℕ) (H : Subgroup (MulAut V)) (θ : ↥H ≃* Equiv.Perm (Fin m)),
      Nat.card H = Nat.factorial m := fun m H θ => by
    rw [Nat.card_congr θ.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rcases h1or2 with hcard | hcard
  ·
    obtain ⟨H₁, h𝓗⟩ := Finset.card_eq_one.mp hcard
    have hH₁ : H₁ ∈ 𝓗 := by rw [h𝓗]; exact Finset.mem_singleton_self _
    obtain ⟨m, hm3, hmodd, θ, β, hβeq, hβr, hβk, hst⟩ := BlkCtx.symBlkS h hH₁ (hsym H₁ hH₁)
    have hH₁X : H₁ ≤ X := h.mem_le hH₁
    have hm9 : m < 9 := by
      by_contra hge
      push Not at hge
      exact false_of_one_block hX hH₁X θ hge
    have hmcases : m = 3 ∨ m = 5 ∨ m = 7 := by
      obtain ⟨k, hk⟩ := hmodd
      omega
    have hJ : ffJ X = H₁ := by rw [h.ffJ_eq, h𝓗]; simp
    have hV : commV H₁ = ⊤ := by
      have := h.iSup_comm
      rw [h𝓗] at this
      simpa using this
    have hXH : X = H₁ := by
      refine le_antisymm (fun x hx => ?_) hH₁X
      have hnorm : x ∈ Subgroup.normalizer (H₁ : Set (MulAut V)) := hJ ▸ B6.le_normalizer_ffJ X hx
      obtain ⟨y, hyH, hxy⟩ := exists_mem_eq_on_of_normalizes hmcases ⟨θ, β, hβeq, hβr, hβk⟩ x
        (fun w _ => by rw [hV]; trivial) (fun w _ => by rw [hV]; trivial) hnorm
      have : x = y := MulEquiv.ext fun w => hxy w (by rw [hV]; trivial)
      rw [this]
      exact hyH
    subst hXH
    rcases hmcases with rfl | rfl | rfl
    · exfalso
      have hc6 : Nat.card ↥X = 6 := by rw [hcardperm 3 X θ]; rfl
      have hxX : x5 ∈ X := hJ ▸ hx5J
      have h1 : x5 = 1 := eq_one_of_pow_five_of_card_six hc6 hxX (by rw [← hx5]; exact pow_orderOf_eq_one x5)
      rw [h1, orderOf_one] at hx5
      exact absurd hx5 (by norm_num)
    · left
      obtain ⟨a, haA, ha, hsg⟩ := exists_odd_sym (Or.inr rfl) θ β hβeq (by rw [hβr, hV]) hβk hAX hAe hA1 hoff
      obtain ⟨x₀, hx₀X, hx₀D, hx₀⟩ := exists_order_three_of_block_five_cv θ (hst (by norm_num)) ha
        (hTM (hAT haA)) (hAD haA) (by simpa [sq] using hAe.2 a haA) hsg hDM
      exact ⟨θ, x₀, hx₀X, hx₀D, hx₀⟩
    · exfalso
      obtain ⟨p, hp⟩ := hst (by norm_num)
      have hMX : M ≤ X := h.mp.maximal.1.le
      rw [inf_eq_left.mpr hMX] at hp
      exact false_of_sym7 h.mp.subgroupOf θ p hp
  ·
    right
    obtain ⟨H₁, H₂, hne, h𝓗⟩ := Finset.card_eq_two.mp hcard
    have h₁ : H₁ ∈ 𝓗 := by rw [h𝓗]; simp
    have h₂ : H₂ ∈ 𝓗 := by rw [h𝓗]; simp
    obtain ⟨m₁, hm₁3, hm₁odd, θ₁, β₁, hβ₁eq, hβ₁r, hβ₁k, hst₁⟩ := BlkCtx.symBlkS h h₁ (hsym H₁ h₁)
    obtain ⟨m₂, hm₂3, hm₂odd, θ₂, β₂, hβ₂eq, hβ₂r, hβ₂k, hst₂⟩ := BlkCtx.symBlkS h h₂ (hsym H₂ h₂)
    obtain ⟨t₀, ht₀T, ht₀⟩ := h.trans h₁ h₂
    obtain ⟨t₀', ht₀'T, ht₀'⟩ := h.trans h₂ h₁
    have hcardeq : Nat.card H₁ = Nat.card H₂ := by
      rw [← ht₀]
      exact (Ch3z.card_conjSub t₀ H₁).symm
    have hm : m₁ = m₂ := by
      have h1 := hcardperm m₁ H₁ θ₁
      have h2 := hcardperm m₂ H₂ θ₂
      rw [h1, h2] at hcardeq
      exact (Nat.factorial_inj (by omega)).mp hcardeq
    subst hm
    have hcomm : ∀ a ∈ H₁, ∀ b ∈ H₂, a * b = b * a := fun a ha b hb => h.comm_of_ne h₁ h₂ hne ha hb
    have hinf : H₁ ⊓ H₂ = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      exact (h.indep₂ h₁ h₂ hne hx.1 (H₂.inv_mem hx.2) (mul_inv_cancel x)).1
    have hm35 : m₁ = 3 ∨ m₁ = 5 := by
      by_contra hcon
      push Not at hcon
      have hge : 6 ≤ m₁ := by
        obtain ⟨k, hk⟩ := hm₁odd
        omega
      exact false_of_two_blocks hX (h.mem_le h₁) (h.mem_le h₂) θ₁ θ₂ hge hm₂3 hcomm
        (fun a ha b hb hab => h.indep₂ h₁ h₂ hne ha hb hab)
    have hJ : ffJ X = H₁ ⊔ H₂ := by
      rw [h.ffJ_eq, h𝓗, Finset.iSup_insert, Finset.iSup_singleton]
    have hsupV : commV H₁ ⊔ commV H₂ = ⊤ := by
      have := h.iSup_comm
      rwa [h𝓗, Finset.iSup_insert, Finset.iSup_singleton] at this
    have hinfV : commV H₁ ⊓ commV H₂ = ⊥ := by
      have := h.inf_iSup_comm h₁
      rw [h𝓗, Finset.iSup_insert, Finset.iSup_singleton, iSup_pos hne.symm] at this
      have e : (⨆ (_ : H₁ ≠ H₁), commV H₁) = ⊥ := by simp
      rwa [e, bot_sup_eq] at this
    have hact₁ : ∀ a ∈ H₁, ∀ v ∈ commV H₂, a v = v := fun a ha v hv =>
      h.act_commV_of_ne h₂ h₁ hne.symm ha hv
    have hact₂ : ∀ a ∈ H₂, ∀ v ∈ commV H₁, a v = v := fun a ha v hv =>
      h.act_commV_of_ne h₁ h₂ hne ha hv
    have htb : TwoBlk X H₁ H₂ m₁ :=
      { m35 := hm35
        h1X := h.mem_le h₁
        h2X := h.mem_le h₂
        Ynorm := fun x hx y hy => by
          rw [← hJ] at hy ⊢
          exact (Subgroup.mem_normalizer_iff.mp (B6.le_normalizer_ffJ X hx) y).mp hy
        comm := hcomm
        inf := hinf
        supV := hsupV
        infV := hinfV
        act₁ := hact₁
        act₂ := hact₂
        sym₁ := ⟨θ₁, β₁, hβ₁eq, hβ₁r, hβ₁k⟩
        sym₂ := ⟨θ₂, β₂, hβ₂eq, hβ₂r, hβ₂k⟩ }
    have hAJ : A ≤ H₁ ⊔ H₂ := hJ ▸ le_ffJ_of_offender hstrong hAX hAe hA1 hoff
    have hconj : ∀ (Ha Hb : Subgroup (MulAut V)) (t : MulAut V), B6.conjSub t Ha = Hb →
        ∀ x ∈ Ha, t * x * t⁻¹ ∈ Hb := by
      intro Ha Hb t ht x hx
      rw [← ht, B6.mem_conjSub]
      have e : t⁻¹ * (t * x * t⁻¹) * t = x := by group
      rw [e]
      exact hx
    rcases hm35 with rfl | rfl
    · exfalso
      have hmem : x5 ∈ H₁ ⊔ H₂ := hJ ▸ hx5J
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hcomm hmem
      have hc₁ : Nat.card H₁ = 6 := by rw [hcardperm 3 H₁ θ₁]; rfl
      have hc₂ : Nat.card H₂ = 6 := by rw [hcardperm 3 H₂ θ₂]; rfl
      have hpow : a ^ 5 * b ^ 5 = 1 := by
        have h1 : (a * b) ^ 5 = 1 := by rw [← hx5]; exact pow_orderOf_eq_one _
        rwa [Commute.mul_pow (show Commute a b from hcomm a ha b hb)] at h1
      have ha5 : a ^ 5 ∈ H₁ ⊓ H₂ := by
        refine ⟨H₁.pow_mem ha 5, ?_⟩
        have : a ^ 5 = (b ^ 5)⁻¹ := eq_inv_of_mul_eq_one_left hpow
        rw [this]
        exact H₂.inv_mem (H₂.pow_mem hb 5)
      rw [hinf, Subgroup.mem_bot] at ha5
      have hb5 : b ^ 5 = 1 := by
        rw [ha5, one_mul] at hpow
        exact hpow
      have ha1 : a = 1 := eq_one_of_pow_five_of_card_six hc₁ ha ha5
      have hb1 : b = 1 := eq_one_of_pow_five_of_card_six hc₂ hb hb5
      rw [ha1, hb1, mul_one, orderOf_one] at hx5
      exact absurd hx5 (by norm_num)
    · rcases htb.exists_odd_offender θ₁ θ₂ β₁ β₂ hβ₁eq hβ₁r hβ₁k hβ₂eq hβ₂r hβ₂k hstrong hAJ hAe
          hA1 hoff with ⟨a, haA, ha, hsg⟩ | ⟨a, haA, ha, hsg⟩
      · obtain ⟨x₀, hx₀H, hx₀D, hx₀⟩ := exists_order_three_of_block_five_cv θ₁ (hst₁ (by norm_num)) ha
          (hTM (hAT haA)) (hAD haA) (by simpa [sq] using hAe.2 a haA) hsg hDM
        have hx₀2 : t₀ * x₀ * t₀⁻¹ ∈ H₂ := hconj H₁ H₂ t₀ ht₀ x₀ hx₀H
        refine ⟨x₀, t₀, h.mem_le h₁ hx₀H, hx₀D, hx₀, ht₀T, hcomm x₀ hx₀H _ hx₀2, ?_⟩
        intro hz
        have hz1 : t₀ * x₀ * t₀⁻¹ ∈ H₁ := (Subgroup.zpowers_le.mpr hx₀H) hz
        have hz0 : t₀ * x₀ * t₀⁻¹ ∈ H₁ ⊓ H₂ := ⟨hz1, hx₀2⟩
        rw [hinf, Subgroup.mem_bot] at hz0
        have hx1 : x₀ = 1 := by
          have e : x₀ = t₀⁻¹ * (t₀ * x₀ * t₀⁻¹) * t₀ := by group
          rw [hz0] at e
          simpa using e
        rw [hx1, orderOf_one] at hx₀
        exact absurd hx₀ (by norm_num)
      · obtain ⟨x₀, hx₀H, hx₀D, hx₀⟩ := exists_order_three_of_block_five_cv θ₂ (hst₂ (by norm_num)) ha
          (hTM (hAT haA)) (hAD haA) (by simpa [sq] using hAe.2 a haA) hsg hDM
        have hx₀1 : t₀' * x₀ * t₀'⁻¹ ∈ H₁ := hconj H₂ H₁ t₀' ht₀' x₀ hx₀H
        refine ⟨x₀, t₀', h.mem_le h₂ hx₀H, hx₀D, hx₀, ht₀'T,
          (hcomm _ hx₀1 x₀ hx₀H).symm, ?_⟩
        intro hz
        have hz2 : t₀' * x₀ * t₀'⁻¹ ∈ H₂ := (Subgroup.zpowers_le.mpr hx₀H) hz
        have hz0 : t₀' * x₀ * t₀'⁻¹ ∈ H₁ ⊓ H₂ := ⟨hx₀1, hz2⟩
        rw [hinf, Subgroup.mem_bot] at hz0
        have hx1 : x₀ = 1 := by
          have e : x₀ = t₀'⁻¹ * (t₀' * x₀ * t₀'⁻¹) * t₀' := by group
          rw [hz0] at e
          simpa using e
        rw [hx1, orderOf_one] at hx₀
        exact absurd hx₀ (by norm_num)

end Main

end CFSG.Quasithin.H13.L319
