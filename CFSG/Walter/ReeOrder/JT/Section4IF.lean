module

public import CFSG.Walter.ReeOrder.JT.Section4IE

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups
open CFSG

variable {G : Type} [Group G] [Finite G]

section General

variable {X : Type*} [Group X] [Finite X]

theorem card_modEq_of_fixed {r : ℕ} [Fact r.Prime] {k : X} (hk : orderOf k = r)
    {A B : Subgroup X} (hkA : k ∈ Subgroup.normalizer (A : Set X)) (hBA : B ≤ A)
    (hB : ∀ y ∈ A, y * k = k * y ↔ y ∈ B) : Nat.card A ≡ Nat.card B [MOD r] := by
  classical
  have hKA : Subgroup.zpowers k ≤ Subgroup.normalizer (A : Set X) :=
    (Subgroup.zpowers_le).mpr hkA
  let := conjAct (Subgroup.zpowers k) A hKA
  have hp : IsPGroup r (Subgroup.zpowers k) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hk, pow_one] :
      Nat.card (Subgroup.zpowers k) = r ^ 1)
  have hmod := hp.card_modEq_card_fixedPoints A
  set F := FixedPoints.subgroup (Subgroup.zpowers k) A with hFdef
  have hFcard : Nat.card (MulAction.fixedPoints (Subgroup.zpowers k) A) = Nat.card F := rfl
  have hFB : F.map A.subtype = B := by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      have h1 := (FixedPoints.mem_subgroup _ _ _).mp ha ⟨k, Subgroup.mem_zpowers k⟩
      have h2 : k * a * k⁻¹ = a := congrArg Subtype.val h1
      refine (hB a a.2).mp ?_
      calc (a : X) * k = k * a * k⁻¹ * k := by rw [h2]
        _ = k * a := by group
    · intro hy
      refine ⟨⟨y, hBA hy⟩, (FixedPoints.mem_subgroup _ _ _).mpr fun g => ?_, rfl⟩
      obtain ⟨g, hg⟩ := g
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      apply Subtype.ext
      change k ^ j * y * (k ^ j)⁻¹ = y
      have hyk : y * k = k * y := (hB y (hBA hy)).mpr hy
      rw [((Commute.zpow_left (hyk.symm : Commute k y) j)).eq, mul_inv_cancel_right]
  rw [← hFB, Subgroup.card_map_of_injective A.subtype_injective, ← hFcard]
  exact hmod

end General

theorem false_of_lemma_4_6_arith {Q m e d M r : ℕ} (hr : r.Prime) (hrQ : r ∣ Q) (hQ : Odd Q)
    (hm : m = 2 * Q + 1 ∨ m + 1 = 2 * Q) (hM : M = m * e) (hd : m = e * d)
    (hd13 : d = 1 ∨ d = 3) (hmod : M ≡ 3 [MOD r]) : False := by
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hQ) (even_iff_two_dvd.mpr hrQ)
  have h1 : (r : ℤ) ∣ (m : ℤ) ^ 2 - 1 := by
    have hrQ' : (r : ℤ) ∣ 2 * (Q : ℤ) := Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mpr hrQ) 2
    rcases hm with hm | hm
    · have : (m : ℤ) ^ 2 - 1 = 2 * Q * (m + 1) := by
        have hm' : (m : ℤ) = 2 * Q + 1 := by exact_mod_cast hm
        rw [hm']
        ring
      rw [this]
      exact Dvd.dvd.mul_right hrQ' _
    · have : (m : ℤ) ^ 2 - 1 = 2 * Q * (m - 1) := by
        have hm' : (m : ℤ) + 1 = 2 * Q := by exact_mod_cast hm
        rw [← hm']
        ring
      rw [this]
      exact Dvd.dvd.mul_right hrQ' _
  have h2 : (r : ℤ) ∣ 3 - (M : ℤ) := by
    have := Nat.modEq_iff_dvd.mp hmod
    exact_mod_cast this
  have hM' : (M : ℤ) = m * e := by exact_mod_cast hM
  have hd' : (m : ℤ) = e * d := by exact_mod_cast hd
  have h8 : (r : ℤ) ∣ 8 := by
    rcases hd13 with rfl | rfl
    · have : (8 : ℤ) = 4 * (((m : ℤ) ^ 2 - 1) + (3 - M)) := by
        rw [hM']
        have : (m : ℤ) = e := by rw [hd']; push_cast; ring
        rw [this]
        ring
      rw [this]
      exact Dvd.dvd.mul_left (dvd_add h1 h2) 4
    · have : (8 : ℤ) = ((m : ℤ) ^ 2 - 1) + 3 * (3 - M) := by
        rw [hM']
        have : (m : ℤ) = e * 3 := by rw [hd']; push_cast; ring
        rw [this]
        ring
      rw [this]
      exact dvd_add h1 (Dvd.dvd.mul_left h2 3)
  have h8' : r ∣ 2 ^ 3 := by exact_mod_cast h8
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h8'))

namespace L46Data

variable {h : JTHyp G} {c : Config h} (D : L46Data c) (hp : h.p ≠ 2) (hp3 : h.p ≠ 3)
  (hS : SuzukiFourGroupTheorem) (h3Q : ¬ 3 ∣ Nat.card c.Q)
include D hp hp3 hS h3Q

theorem false_of_ne_one
    {x₀ : G} (hx₀Q : x₀ ∈ c.Q) (hx₀μ : c.μ * x₀ = x₀ * c.μ)
    (hx₀1 : x₀ ≠ 1) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ht₁t₁ : c.t₁ * c.t₁ = 1 := by rw [← pow_two, ← c.orderOf_t₁, pow_orderOf_eq_one]
  have ht₂t₂ : D.t₂ * D.t₂ = 1 := by rw [← pow_two, ← D.orderOf_t₂, pow_orderOf_eq_one]
  have ht₁1 : c.t₁ ≠ 1 := by
    intro h0
    have := c.orderOf_t₁
    rw [h0, orderOf_one] at this
    omega
  have ht₂1 : D.t₂ ≠ 1 := by
    intro h0
    have := D.orderOf_t₂
    rw [h0, orderOf_one] at this
    omega
  have hμN : c.μ ∈ Subgroup.normalizer (c.Q : Set G) :=
    c.toSetup.normalizer_T_le_normalizer_Q hp c.μ_mem_NT
  have hmQ := c.toSetup.coprime_m_card_Q hp
  have hQodd := c.toSetup.odd_card_Q hp
  have hm9 := c.toSetup.nine_le_m hp hp3 h3Q
  have hmodd := c.toSetup.odd_m hp
  have hMo : ∀ y ∈ D.M, Odd (orderOf y) := fun y hy =>
    Odd.of_dvd_nat D.odd (Subgroup.orderOf_dvd_natCard _ hy)
  obtain ⟨R, hRM, ht₁R, ht₂R, hR1, hRπ, hconj⟩ := D.exists_R hp hS h3Q hx₀Q hx₀μ hx₀1
  obtain ⟨x, hxM, hxR⟩ := hconj R hRM hRπ
  have hxμ := D.commute_μ hxM
  have hRo : ∀ k ∈ R, orderOf k ∣ Nat.card c.Q := fun k hk => by
    have := Subgroup.orderOf_dvd_natCard c.Q (hxR k hk)
    rwa [show x⁻¹ * k * x = x⁻¹ * k * x⁻¹⁻¹ by rw [inv_inv], ← MulAut.conj_apply,
      MulEquiv.orderOf_eq] at this
  have hRfix : ∀ y ∈ R, c.t₁ * y * c.t₁⁻¹ = y → y = 1 := by
    intro y hy hyt
    have hyt' : y * c.t₁ = c.t₁ * y := by
      calc y * c.t₁ = c.t₁ * y * c.t₁⁻¹ * c.t₁ := by rw [hyt]
        _ = c.t₁ * y := by group
    have h1 := D.orderOf_dvd_m (D.inf_t₁ y (hRM hy) hyt')
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hmQ h1 (hRo y hy))
  have hRinv := inv_of_fpf_involution ht₁t₁ ht₁R hRfix
  have hRodd : Odd (Nat.card R) := Odd.of_dvd_nat D.odd (Subgroup.card_dvd_of_le hRM)
  obtain ⟨σ, hσ, hK1⟩ : ∃ σ : G, (σ = D.t₂ ∨ σ = c.t₁ * D.t₂) ∧
      R ⊓ Subgroup.centralizer ({σ} : Set G) ≠ ⊥ := by
    by_contra hne
    push Not at hne
    have hBW := card_mul_card_sq_eq_mul ht₁t₁ ht₂t₂ ht₁1 ht₂1 (Ne.symm D.ne) D.comm.symm R
      ht₁R ht₂R hRodd
    have hR₁ : R ⊓ Subgroup.centralizer ({c.t₁} : Set G) = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      exact Subgroup.mem_bot.mpr (hRfix y hy.1 (by
        rw [(Subgroup.mem_centralizer_singleton_iff.mp hy.2).symm, mul_inv_cancel_right]))
    rw [hR₁, hne _ (Or.inl rfl), hne _ (Or.inr rfl), bot_inf_eq, Subgroup.card_bot] at hBW
    have : Nat.card R = 1 := by simpa using hBW
    exact hR1 (Subgroup.eq_bot_of_card_eq R this)
  have hτ : c.t₁ * σ = D.t₂ ∨ c.t₁ * σ = c.t₁ * D.t₂ := by
    rcases hσ with rfl | rfl
    · exact Or.inr rfl
    · left
      rw [← mul_assoc, ht₁t₁, one_mul]
  obtain ⟨hσσ, hσt₁, hσ1, hσne, hσL, hσM⟩ := D.inv_props hσ
  obtain ⟨hττ, hτt₁, hτ1, hτne, hτL, hτM⟩ := D.inv_props hτ
  set τ := c.t₁ * σ with hτdef
  have ht₁τ : c.t₁ * τ = σ := by rw [hτdef, ← mul_assoc, ht₁t₁, one_mul]
  set K := R ⊓ Subgroup.centralizer ({σ} : Set G) with hKdef
  have hKR : K ≤ R := inf_le_left
  have hKM : K ≤ D.M := hKR.trans hRM
  have hKcard : Nat.card K ∣ Nat.card c.Q := by
    have hle : K.map (MulAut.conj x⁻¹).toMonoidHom ≤ c.Q := by
      rintro _ ⟨k, hk, rfl⟩
      have := hxR k hk.1
      simpa [MulAut.conj_apply] using this
    have := Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective] at this
  have hKodd : Odd (Nat.card K) := Odd.of_dvd_nat D.odd (Subgroup.card_dvd_of_le hKM)
  have hτK : ∀ k ∈ K, τ * k * τ⁻¹ = k⁻¹ := by
    intro k hk
    have hkσ : k * σ = σ * k := Subgroup.mem_centralizer_singleton_iff.mp hk.2
    calc τ * k * τ⁻¹ = c.t₁ * (σ * k * σ⁻¹) * c.t₁⁻¹ := by rw [hτdef]; group
      _ = c.t₁ * k * c.t₁⁻¹ := by rw [← hkσ, mul_inv_cancel_right]
      _ = k⁻¹ := hRinv k hk.1
  obtain ⟨k₀, hk₀K, hk₀1⟩ := (Subgroup.bot_or_exists_ne_one K).resolve_left hK1
  have hCσ : ∀ y ∈ D.M, y * σ = σ * y → orderOf y ∣ 2 * Nat.card c.Q := by
    set Cσ := D.M ⊓ Subgroup.centralizer ({σ} : Set G) with hCσdef
    have ht₁Cσ : c.t₁ ∈ Subgroup.normalizer (Cσ : Set G) := by
      refine mem_normalizer_of_conj_mem fun y hy => Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp D.t₁_mem_normalizer y).mp hy.1
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have hyσ := Subgroup.mem_centralizer_singleton_iff.mp hy.2
        have h1 : Commute σ c.t₁ := hσt₁
        have h2 : Commute σ y := hyσ.symm
        exact ((h1.mul_right h2).mul_right h1.inv_right).symm.eq
    have hfix : ∀ y ∈ Cσ, c.t₁ * y * c.t₁⁻¹ = y → y = 1 := by
      intro y hy hyt
      have hyt' : y * c.t₁ = c.t₁ * y := by
        calc y * c.t₁ = c.t₁ * y * c.t₁⁻¹ * c.t₁ := by rw [hyt]
          _ = c.t₁ * y := by group
      exact D.eq_one_of_commute hσ hy.1 hyt' (Subgroup.mem_centralizer_singleton_iff.mp hy.2)
    have hCσc := commute_of_fpf_involution ht₁t₁ ht₁Cσ hfix
    have hCσodd : Odd (Nat.card Cσ) :=
      Odd.of_dvd_nat D.odd (Subgroup.card_dvd_of_le inf_le_left)
    have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hσσ) hσ1
    have hk₀Cσ : k₀ ∈ Cσ := ⟨hKM hk₀K, hk₀K.2⟩
    have hk₀Q := hRo k₀ hk₀K.1
    have hk₀o : orderOf k₀ ≠ 1 := fun h1 => hk₀1 (orderOf_eq_one_iff.mp h1)
    have hk₀C := Subgroup.orderOf_dvd_natCard _ hk₀Cσ
    rcases h.abelian_odd_cases hp hσ2 (inf_le_right : Cσ ≤ _) hCσc hCσodd with
      hpg | ⟨-, hdvd⟩
    · exfalso
      obtain ⟨n, hn⟩ := hpg.exists_card_eq
      have h1 : orderOf k₀ ∣ h.p ^ n := by rw [← hn]; exact hk₀C
      have hcop : Nat.Coprime (h.p ^ n) (Nat.card c.Q) :=
        Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr
          (c.toSetup.not_dvd_card_Q hp))
      exact hk₀o (Nat.eq_one_of_dvd_coprimes hcop h1 hk₀Q)
    · intro y hy hyσ
      have hyC : y ∈ Cσ := ⟨hy, Subgroup.mem_centralizer_singleton_iff.mpr hyσ⟩
      have hyd := Subgroup.orderOf_dvd_natCard _ hyC
      rcases c.toSetup.tori_cases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at hdvd <;>
        rcases hdvd with hd | hd
      · exact absurd (Nat.eq_one_of_dvd_coprimes hmQ (hk₀C.trans hd) hk₀Q) hk₀o
      · exact hyd.trans hd
      · exact hyd.trans hd
      · exact absurd (Nat.eq_one_of_dvd_coprimes hmQ (hk₀C.trans hd) hk₀Q) hk₀o
  obtain ⟨M₁, hM₁M, hM₁o, hM₁mem, hM₁N⟩ := D.exists_M₁ hp hS h3Q hconj
  have hM₁odd : Odd (Nat.card M₁) := Odd.of_dvd_nat D.odd (Subgroup.card_dvd_of_le hM₁M)
  have hσM₁ := hM₁N σ hσM
  have hτM₁ := hM₁N τ hτM
  have ht₁M₁ := hM₁N c.t₁ D.t₁_mem_normalizer
  have hσfix : ∀ y ∈ M₁, σ * y * σ⁻¹ = y → y = 1 := by
    intro y hy hyσ
    have hyσ' : y * σ = σ * y := by
      calc y * σ = σ * y * σ⁻¹ * σ := by rw [hyσ]
        _ = σ * y := by group
    have h1 := hCσ y (hM₁M hy) hyσ'
    have h2 : orderOf y ∣ Nat.card c.Q :=
      Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm (Nat.coprime_two_left.mpr
        (hMo y (hM₁M hy)))) h1
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (hM₁o y hy) h2)
  have hM₁c := commute_of_fpf_involution hσσ hσM₁ hσfix
  have hLM := D.L_le_M hp
  have hLM₁ : D.L ≤ M₁ := fun y hy => hM₁mem y (hLM hy)
    (Nat.Coprime.coprime_dvd_left (D.orderOf_dvd_m hy) hmQ)
  have hμM₁ : c.μ ∈ M₁ := hLM₁ D.μ_mem_L
  have hM₁t₁ : M₁ ⊓ Subgroup.centralizer ({c.t₁} : Set G) = D.L :=
    le_antisymm (fun y hy => D.inf_t₁ y (hM₁M hy.1)
      (Subgroup.mem_centralizer_singleton_iff.mp hy.2)) (le_inf hLM₁ D.L_le)
  set L₁ := M₁ ⊓ Subgroup.centralizer ({τ} : Set G) with hL₁def
  have hLτ : ∀ y ∈ D.L, y * τ = τ * y → y = 1 := fun y hy hyτ =>
    D.eq_one_of_commute hτ (hLM hy) (Subgroup.mem_centralizer_singleton_iff.mp (D.L_le hy)) hyτ
  have hM₁card : Nat.card M₁ = c.toSetup.m * Nat.card L₁ := by
    have hBW := card_mul_card_sq_eq_mul ht₁t₁ hττ ht₁1 hτ1 (Ne.symm hτne) hτt₁.symm M₁ ht₁M₁
      hτM₁ hM₁odd
    rw [hM₁t₁, ht₁τ] at hBW
    have h1 : D.L ⊓ Subgroup.centralizer ({τ} : Set G) = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      exact Subgroup.mem_bot.mpr (hLτ y hy.1 (Subgroup.mem_centralizer_singleton_iff.mp hy.2))
    have h2 : M₁ ⊓ Subgroup.centralizer ({σ} : Set G) = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      exact Subgroup.mem_bot.mpr (hσfix y hy.1 (by
        rw [(Subgroup.mem_centralizer_singleton_iff.mp hy.2).symm, mul_inv_cancel_right]))
    rw [h1, h2, Subgroup.card_bot, D.card_L, one_pow, mul_one, mul_one] at hBW
    exact hBW
  have hmp : Nat.Coprime c.toSetup.m h.p := by
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr fun hpm => ?_)
    have hq := c.toSetup.m_add hp
    have hpq : h.p ∣ h.q := by rw [JTHyp.q_eq]; exact dvd_pow_self _ h.f_pos
    have h2Q : h.p ∣ 2 * Nat.card c.Q := (Nat.dvd_add_right hpm).mp (by rw [hq]; exact hpq)
    have : h.p ∣ Nat.card c.Q := ((Nat.Prime.dvd_mul Fact.out).mp h2Q).resolve_left
      (fun h2 => hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h2))
    exact c.toSetup.not_dvd_card_Q hp this
  have hm2Q : Nat.Coprime c.toSetup.m (2 * Nat.card c.Q) :=
    Nat.Coprime.mul_right (Nat.Coprime.symm (Nat.coprime_two_left.mpr hmodd)) hmQ
  have hL₁c : ∀ a ∈ L₁, ∀ b ∈ L₁, a * b = b * a := fun a ha b hb => hM₁c a ha.1 b hb.1
  have hL₁odd : Odd (Nat.card L₁) := Odd.of_dvd_nat hM₁odd (Subgroup.card_dvd_of_le inf_le_left)
  have hτ2 : orderOf τ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hττ) hτ1
  have hL₁m : Nat.Coprime c.toSetup.m (Nat.card L₁) ∨ Nat.card L₁ ∣ c.toSetup.m := by
    rcases h.abelian_odd_cases hp hτ2 (inf_le_right : L₁ ≤ _) hL₁c hL₁odd with
      hpg | ⟨-, hdvd⟩
    · left
      obtain ⟨n, hn⟩ := hpg.exists_card_eq
      rw [hn]
      exact Nat.Coprime.pow_right n hmp
    · rcases c.toSetup.tori_cases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at hdvd <;>
        rcases hdvd with hd | hd
      · exact Or.inr hd
      · exact Or.inl (Nat.Coprime.coprime_dvd_right hd hm2Q)
      · exact Or.inl (Nat.Coprime.coprime_dvd_right hd hm2Q)
      · exact Or.inr hd
  have hfixK : ∀ k ∈ K, k ≠ 1 → ∀ y ∈ M₁, y * k = k * y → y ∈ Subgroup.zpowers c.μ := by
    intro k hk hk1 y hy hyk
    have hkQ : ∀ z ∈ Subgroup.zpowers k, x⁻¹ * z * x ∈ c.Q := fun z hz =>
      hxR z ((Subgroup.zpowers_le).mpr hk.1 hz)
    have hk1' : Subgroup.zpowers k ≠ ⊥ := by
      rw [Ne, Subgroup.zpowers_eq_bot]
      exact hk1
    exact c.toSetup.mem_zpowers_of_conj hp hS h3Q hμN c.orderOf_μ hkQ hk1' hxμ
      (mem_normalizer_zpowers_of_commute hyk) (D.commute_μ (hM₁M hy)) (hMo y (hM₁M hy))
      (hM₁o y hy)
  have htrick : ∀ Y : Subgroup G, Y ≤ D.L → K ≤ Subgroup.normalizer (Y : Set G) →
      Y ≤ Subgroup.zpowers c.μ := by
    intro Y hYL hKY y hy
    have hYm : Nat.card Y ∣ c.toSetup.m := by
      rw [← D.card_L]
      exact Subgroup.card_dvd_of_le hYL
    have hYodd : Odd (Nat.card Y) := Odd.of_dvd_nat hmodd hYm
    have hcop : Nat.Coprime (Nat.card K) (Nat.card Y) :=
      Nat.Coprime.coprime_dvd_left hKcard (Nat.Coprime.coprime_dvd_right hYm hmQ.symm)
    have hcomm := commute_of_inv_of_inv hττ hKY hKodd hYodd hcop hτK
      (fun z hz => hτL z (hYL hz))
    exact hfixK k₀ hk₀K hk₀1 y (hLM₁ (hYL hy)) (hcomm k₀ hk₀K y hy).symm
  have hK1' : Nat.card K ≠ 1 := fun h1 => hK1 (Subgroup.eq_bot_of_card_eq K h1)
  obtain ⟨r, hr, hrK⟩ := Nat.exists_prime_and_dvd hK1'
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨⟨k₁, hk₁K⟩, hk₁⟩ := exists_prime_orderOf_dvd_card' (G := K) r hrK
  have hk₁o : orderOf k₁ = r := by rw [← hk₁, Subgroup.orderOf_mk]
  have hk₁1 : k₁ ≠ 1 := fun h0 => by
    rw [h0, orderOf_one] at hk₁o
    exact hr.one_lt.ne hk₁o
  have hrQ : r ∣ Nat.card c.Q := hrK.trans hKcard
  have hfix₁ : ∀ y ∈ M₁, y * k₁ = k₁ * y ↔ y ∈ Subgroup.zpowers c.μ := by
    intro y hy
    refine ⟨hfixK k₁ hk₁K hk₁1 y hy, fun hyμ => ?_⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hyμ
    exact (Commute.zpow_left ((D.commute_μ (hKM hk₁K)).symm : Commute c.μ k₁) j).eq
  have hmod := card_modEq_of_fixed hk₁o (hM₁N k₁ (Subgroup.le_normalizer (hKM hk₁K)))
    ((Subgroup.zpowers_le).mpr hμM₁) hfix₁
  rw [Nat.card_zpowers, c.orderOf_μ] at hmod
  have hdisj : Disjoint D.L L₁ := by
    rw [Subgroup.disjoint_def]
    intro y hyL hyL₁
    exact hLτ y hyL (Subgroup.mem_centralizer_singleton_iff.mp hyL₁.2)
  have hLN : D.L ≤ Subgroup.normalizer (L₁ : Set G) := fun a ha =>
    mem_normalizer_of_conj_mem fun b hb => by
      rw [hM₁c a (hLM₁ ha) b hb.1, mul_inv_cancel_right]
      exact hb
  have hdec : ∀ z ∈ M₁, ∃ a ∈ D.L, ∃ b ∈ L₁, a * b = z := by
    have hsup : D.L ⊔ L₁ = M₁ := by
      apply Subgroup.eq_of_le_of_card_ge (sup_le hLM₁ inf_le_left)
      rw [card_sup_eq_mul_of_disjoint hLN hdisj, hM₁card, D.card_L]
    intro z hz
    rw [← hsup, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hLN] at hz
    exact hz
  have := D.L_cyclic
  obtain ⟨⟨gL, hgL⟩, hgen⟩ := IsCyclic.exists_generator (α := D.L)
  have hLg : ∀ y ∈ D.L, ∃ i : ℤ, gL ^ i = y := by
    intro y hy
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨y, hy⟩)
    exact ⟨i, by simpa using congrArg Subtype.val hi⟩
  have hgLo : orderOf gL = c.toSetup.m := by
    rw [← D.card_L, ← orderOf_eq_card_of_forall_mem_zpowers hgen, Subgroup.orderOf_mk]
  set e := Nat.card L₁ with hedef
  set Y := Subgroup.zpowers (gL ^ e) with hYdef
  have hYL : Y ≤ D.L := (Subgroup.zpowers_le).mpr (D.L.pow_mem hgL e)
  have hbe : ∀ b ∈ L₁, b ^ e = 1 := fun b hb => by
    have := pow_card_eq_one' (G := L₁) (x := ⟨b, hb⟩)
    exact congrArg Subtype.val this
  have hKY : K ≤ Subgroup.normalizer (Y : Set G) := by
    intro k hk
    refine mem_normalizer_of_conj_mem fun y hy => ?_
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hkg : k * gL * k⁻¹ ∈ M₁ :=
      (Subgroup.mem_normalizer_iff.mp (hM₁N k (Subgroup.le_normalizer (hKM hk))) gL).mp
        (hLM₁ hgL)
    obtain ⟨a, ha, b, hb, hab⟩ := hdec _ hkg
    obtain ⟨i, rfl⟩ := hLg a ha
    have hcomm : Commute (gL ^ i) b := hM₁c _ (hLM₁ ha) b hb.1
    have h1 : k * (gL ^ e) ^ j * k⁻¹ = ((k * gL * k⁻¹) ^ e) ^ j := by
      rw [← conj_zpow, ← conj_pow]
    have h2 : (gL ^ i) ^ e = (gL ^ e) ^ i := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
    rw [h1, ← hab, hcomm.mul_pow, hbe b hb, mul_one, h2]
    exact Subgroup.zpow_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _) _
  have hY3 : orderOf (gL ^ e) ∣ 3 := by
    have := Subgroup.card_dvd_of_le (htrick Y hYL hKY)
    rwa [Nat.card_zpowers, Nat.card_zpowers, c.orderOf_μ] at this
  have he0 : e ≠ 0 := Nat.card_pos.ne'
  rw [orderOf_pow' gL he0, hgLo] at hY3
  have hm : c.toSetup.m = 2 * Nat.card c.Q + 1 ∨ c.toSetup.m + 1 = 2 * Nat.card c.Q := by
    have h1 := c.toSetup.m_add hp
    rcases c.toSetup.four_mul_card_Q_cases hp with ⟨-, h4⟩ | ⟨-, h4⟩
    · right; omega
    · left; omega
  rcases hL₁m with hcop | hdvd
  · rw [Nat.Coprime.gcd_eq_one hcop, Nat.div_one] at hY3
    have := Nat.le_of_dvd (by norm_num) hY3
    omega
  · rw [Nat.gcd_eq_right hdvd] at hY3
    obtain ⟨d, hd⟩ := hdvd
    have hY3' : d ∣ 3 := by
      rwa [hd, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero he0)] at hY3
    exact false_of_lemma_4_6_arith hr hrQ hQodd hm hM₁card hd
      ((Nat.dvd_prime Nat.prime_three).mp hY3') hmod

end L46Data

namespace Config

variable {h : JTHyp G} (c : Config h) (hp : h.p ≠ 2) (hp3 : h.p ≠ 3)
  (hS : SuzukiFourGroupTheorem)
include hp hp3 hS

theorem eq_one_of_commute_μ
    (h3Q : ¬ 3 ∣ Nat.card c.Q) :
    ∀ x ∈ c.Q, c.μ * x = x * c.μ → x = 1 := by
  intro x hxQ hxμ
  by_contra hx1
  obtain ⟨D⟩ := c.nonempty_l46Data hp hp3 h3Q
  exact D.false_of_ne_one hp hp3 hS h3Q hxQ hxμ hx1

theorem lemma_4_6_a
    (hH : HuppertMetacyclicTheorem) :
    ∀ x ∈ c.Q, c.μ * x = x * c.μ → x = 1 :=
  c.eq_one_of_commute_μ hp hp3 hS (c.toSetup.lemma_4_5 hp hS hH)

end Config

namespace Setup

variable {h : JTHyp G} (s : Setup h) (hp : h.p ≠ 2) (hp3 : h.p ≠ 3)
  (hS : SuzukiFourGroupTheorem) (hH : HuppertMetacyclicTheorem)
include s hp hp3 hS hH

theorem lemma_4_6_b :
    Subgroup.normalizer (s.Q : Set G) = Subgroup.normalizer (s.T : Set G) := by
  classical
  obtain ⟨c, rfl⟩ := s.exists_config hp
  have h3Q := c.toSetup.lemma_4_5 hp hS hH
  rcases c.toSetup.lemma_4_4 hp hS with h1 | ⟨L, D, -, hQD, -, hD, hLD⟩
  · exact h1
  exfalso
  have hμN : c.μ ∈ Subgroup.normalizer (c.Q : Set G) :=
    c.toSetup.normalizer_T_le_normalizer_Q hp c.μ_mem_NT
  obtain ⟨a₀, ha₀, d₀, hd₀, hμad⟩ := hLD.exists_mul hμN
  have hd₀1 : d₀ = 1 := by
    have h3 : (a₀ * d₀) ^ 3 = 1 := by rw [hμad, ← c.orderOf_μ, pow_orderOf_eq_one]
    have hd3 := (hLD.pow_eq_one_of_mul ha₀ hd₀ h3).2
    have h2 : orderOf d₀ ∣ 3 := orderOf_dvd_of_pow_eq_one hd3
    have hd₀Q : d₀ ∈ c.Q :=
      c.toSetup.mem_Q_of_mem_D_of_odd hp hQD hD hd₀ (Odd.of_dvd_nat (by decide) h2)
    have h1 : orderOf d₀ ∣ Nat.card c.Q := Subgroup.orderOf_dvd_natCard _ hd₀Q
    have hcop : Nat.Coprime 3 (Nat.card c.Q) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3Q
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h2 h1)
  rw [hd₀1, mul_one] at hμad
  have hfix := c.lemma_4_6_a hp hp3 hS hH
  have hQ1 : c.Q = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    refine hfix z hz ?_
    rw [← hμad]
    exact hLD.commute ha₀ (hQD hz)
  exact c.toSetup.card_Q_ne_one hp (by rw [hQ1, Subgroup.card_bot])

theorem lemma_4_6_c :
    h.q % 8 = 5 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, rfl⟩ := s.exists_config hp
  rcases h.mod_eight hp with h8 | h8
  · exfalso
    have hfix := c.lemma_4_6_a hp hp3 hS hH
    have hμN : c.μ ∈ Subgroup.normalizer (c.Q : Set G) :=
      c.toSetup.normalizer_T_le_normalizer_Q hp c.μ_mem_NT
    have hmod := card_modEq_of_fixed c.orderOf_μ hμN (bot_le : (⊥ : Subgroup G) ≤ c.Q)
      (fun y hy => ⟨fun hyμ => Subgroup.mem_bot.mpr (hfix y hy hyμ.symm),
        fun hy1 => by rw [Subgroup.mem_bot.mp hy1, one_mul, mul_one]⟩)
    rw [Subgroup.card_bot] at hmod
    have h4 := c.toSetup.four_mul_card_Q_cases hp
    have hq3 : h.q % 3 = 0 := by
      have hm : Nat.card c.Q % 3 = 1 % 3 := hmod
      rcases h4 with ⟨-, h4⟩ | ⟨h4', -⟩
      · omega
      · omega
    have h3q : 3 ∣ h.q := Nat.dvd_of_mod_eq_zero hq3
    rw [JTHyp.q_eq] at h3q
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three (Fact.out : h.p.Prime)).mp
      (Nat.prime_three.dvd_of_dvd_pow h3q)).symm
  · exact h8

end Setup

namespace JTHyp

variable (h : JTHyp G) (hp : h.p ≠ 2)
include hp

theorem nonempty_setup :
    Nonempty (Setup h) := by
  have hT := h.isKleinFour_inf_F hp
  obtain ⟨S, htS⟩ : ∃ S : Sylow 2 G, h.t ∈ S := by
    have h2 : IsPGroup 2 (Subgroup.zpowers h.t) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.orderOf_t, pow_one])
    obtain ⟨S, hS⟩ := h2.exists_le_sylow
    exact ⟨S, hS (Subgroup.mem_zpowers _)⟩
  obtain ⟨s, -⟩ := h.exists_setup_card_normalizer hp (hT S htS)
  exact ⟨s⟩

theorem lemma_4_6_c
    (hp3 : h.p ≠ 3) (hS : SuzukiFourGroupTheorem)
    (hH : HuppertMetacyclicTheorem) : h.q % 8 = 5 := by
  obtain ⟨s⟩ := h.nonempty_setup hp
  exact s.lemma_4_6_c hp hp3 hS hH

end JTHyp

end CFSG.Walter.JT
