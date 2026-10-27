module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2NineteenFourBad

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open scoped Pointwise

variable {W : Type} [CommGroup W] [Finite W]

private theorem s16c167_mem_zpowers_eq_one_or {e x : MulAut W} (he2 : e * e = 1) (he1 : e ≠ 1)
    (hx : x ∈ Subgroup.zpowers e) : x = 1 ∨ x = e := by
  have hord : orderOf e = 2 := orderOf_eq_prime (by rwa [pow_two]) he1
  rw [Subgroup.mem_zpowers_iff] at hx
  obtain ⟨k, rfl⟩ := hx
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left
    obtain ⟨m, rfl⟩ : 2 ∣ k := Int.dvd_of_emod_eq_zero hk
    rw [zpow_mul, zpow_ofNat, pow_two, he2, one_zpow]
  · right
    have hk' : k = 2 * (k / 2) + 1 := by omega
    rw [hk', zpow_add, zpow_mul, zpow_ofNat, pow_two, he2, one_zpow, one_mul, zpow_one]

private theorem s16c167_isPGroup_two {E : Subgroup (MulAut W)} (hE : ∀ e ∈ E, e * e = 1) :
    IsPGroup 2 ↥E :=
  fun g => ⟨1, Subtype.ext (by simpa [pow_two] using hE g.1 g.2)⟩

theorem s16c167_four_mQuot_sup_zpowers {E H : Subgroup (MulAut W)}
    (hsq : ∀ x ∈ E, x * x = 1) (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hHE : H ≤ E)
    {e : MulAut W} (heE : e ∈ E) (heH : e ∉ H) :
    H ⊔ Subgroup.zpowers e ≤ E ∧
      E3.mQuot E (H ⊔ Subgroup.zpowers e) + 1 = E3.mQuot E H := by
  have he2 : e * e = 1 := hsq e heE
  have he1 : e ≠ 1 := fun h => heH (h ▸ H.one_mem)
  refine ⟨sup_le hHE (Subgroup.zpowers_le.mpr heE), ?_⟩
  have hinf : H ⊓ Subgroup.zpowers e = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxH, hxZ⟩ := hx
    rcases s16c167_mem_zpowers_eq_one_or he2 he1 hxZ with h | h
    · rw [Subgroup.mem_bot]; exact h
    · exact absurd (h ▸ hxH) heH
  have hcardz : Nat.card ↥(Subgroup.zpowers e) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (by rwa [pow_two]) he1]
  have hcommZ : ∀ a ∈ H, ∀ b ∈ Subgroup.zpowers e, a * b = b * a := by
    intro a ha b hb
    rcases s16c167_mem_zpowers_eq_one_or he2 he1 hb with hb1 | hbe
    · rw [hb1, mul_one, one_mul]
    · rw [hbe]
      exact hcomm a (hHE ha) e heE
  have hcardK : Nat.card ↥(H ⊔ Subgroup.zpowers e) = 2 * Nat.card ↥H := by
    set φ := MonoidHom.noncommCoprod H.subtype (Subgroup.zpowers e).subtype
      (fun a b => hcommZ a a.2 b b.2) with hφ
    have hrange : φ.range = H ⊔ Subgroup.zpowers e := by
      have h := MonoidHom.noncommCoprod_range H.subtype (Subgroup.zpowers e).subtype
        (fun a b => hcommZ a a.2 b b.2)
      rwa [Subgroup.range_subtype, Subgroup.range_subtype] at h
    have hinj : Function.Injective φ := by
      rw [injective_iff_map_eq_one]
      rintro ⟨a, b⟩ h1
      have h1' : (a : MulAut W) * (b : MulAut W) = 1 := h1
      have hb : (b : MulAut W) = (a : MulAut W)⁻¹ := eq_inv_of_mul_eq_one_right h1'
      have hbH : (b : MulAut W) ∈ H := hb ▸ H.inv_mem a.2
      have hb1 : (b : MulAut W) = 1 := by
        have hmem : (b : MulAut W) ∈ H ⊓ Subgroup.zpowers e := ⟨hbH, b.2⟩
        rw [hinf] at hmem
        exact Subgroup.mem_bot.mp hmem
      have ha1 : (a : MulAut W) = 1 := by
        rw [hb1, mul_one] at h1'
        exact h1'
      exact Prod.ext (Subtype.ext ha1) (Subtype.ext hb1)
    rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_prod,
      hcardz, Nat.mul_comm]
  have hrel : H.relIndex (H ⊔ Subgroup.zpowers e) = 2 := by
    have h := Subgroup.relIndex_mul_card H (H ⊔ Subgroup.zpowers e)
    rw [inf_eq_left.mpr le_sup_left, hcardK] at h
    exact Nat.mul_right_cancel Nat.card_pos h
  have hm : E3.mQuot (H ⊔ Subgroup.zpowers e) H = 1 := by
    show padicValNat 2 (H.relIndex (H ⊔ Subgroup.zpowers e)) = 1
    rw [hrel]
    exact padicValNat.self (by norm_num)
  have hKle : H ⊔ Subgroup.zpowers e ≤ E := sup_le hHE (Subgroup.zpowers_le.mpr heE)
  have hadd := E3.mQuot_add (V := E) (U := H) (U' := H ⊔ Subgroup.zpowers e) le_sup_left hKle
  rw [hm] at hadd
  omega

theorem s16c167_four_two_of_ker_inf {E : Subgroup (MulAut W)} (hsq : ∀ x ∈ E, x * x = 1)
    (hrk : 3 ≤ rk ↥E) {ι : Type} (N : ι → Subgroup (MulAut W)) (hNE : ∀ i, N i ≤ E)
    (hN : ∀ i, N i = E ∨ E3.mQuot E (N i) = 1) (hbot : ∀ x ∈ E, (∀ i, x ∈ N i) → x = 1) :
    ∃ i j, N i ≠ N j ∧ E3.mQuot E (N i) = 1 ∧ E3.mQuot E (N j) = 1 := by
  by_contra hno
  have hpair : ∀ i j, E3.mQuot E (N i) = 1 → E3.mQuot E (N j) = 1 → N i = N j := by
    intro i j hi hj
    by_contra hne
    exact hno ⟨i, j, hne, hi, hj⟩
  have hEgrp : IsPGroup 2 ↥E := s16c167_isPGroup_two hsq
  by_cases hcase : ∃ i, E3.mQuot E (N i) = 1
  · obtain ⟨i₀, hi₀⟩ := hcase
    have hle : ∀ j, N i₀ ≤ N j := by
      intro j
      by_cases hj : E3.mQuot E (N j) = 1
      · exact le_of_eq (hpair i₀ j hi₀ hj)
      · rcases hN j with h | h
        · rw [h]; exact hNE i₀
        · exact absurd h hj
    have hNbot : N i₀ = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      exact hbot x (hNE i₀ hx) (fun j => hle j hx)
    have hcard : Nat.card ↥E = 2 * Nat.card ↥(N i₀) := by
      have h := E3.card_eq_two_pow_mul hEgrp (hNE i₀)
      rw [hi₀] at h
      simpa using h
    have hEcard : Nat.card ↥E = 2 ^ rk ↥E := card_eq_two_pow_of_isPGroup hEgrp
    have hNcard : Nat.card ↥(N i₀) = 2 ^ rk ↥(N i₀) :=
      card_eq_two_pow_of_isPGroup (hEgrp.to_le (hNE i₀))
    have hpow : 2 ^ rk ↥E = 2 ^ (rk ↥(N i₀) + 1) := by
      rw [← hEcard, hcard, hNcard, pow_succ, Nat.mul_comm]
    have hrk_eq : rk ↥E = rk ↥(N i₀) + 1 := Nat.pow_right_injective (le_refl 2) hpow
    have h2 : 2 ≤ rk ↥(N i₀) := by omega
    have hNne : N i₀ ≠ ⊥ := by
      intro hb
      have hzero : rk ↥(N i₀) = 0 := by rw [hb]; exact rk_bot
      omega
    exact hNne hNbot
  · push Not at hcase
    have hEall : ∀ i, N i = E := by
      intro i
      rcases hN i with h | h
      · exact h
      · exact absurd h (hcase i)
    have hEbot : E = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      exact hbot x hx (fun i => by rw [hEall i]; exact hx)
    have hzero : rk ↥E = 0 := by rw [hEbot]; exact rk_bot
    omega

theorem s16c167_two_bad_four {E : Subgroup (MulAut W)} {𝒴 : Set (Subgroup W)}
    (F : Four19 E 𝒴) (hrk : 3 ≤ rk ↥E) :
    ∃ F₁ F₂ : Subgroup (MulAut W), F₁ ≤ E ∧ F₂ ≤ E ∧ F₁ ≠ F₂ ∧
      E3.mQuot E F₁ = 1 ∧ E3.mQuot E F₂ = 1 ∧ fixV F₁ ≠ fixV E ∧ fixV F₂ ≠ fixV E := by
  classical
  have hEgrp : IsPGroup 2 ↥E := s16c167_isPGroup_two F.sq_E
  by_cases hcase1 : ∃ Y ∈ 𝒴, E3.mQuot E (E ⊓ stabSub Y) = 2
  · obtain ⟨Y, hY, hY2⟩ := hcase1
    set EY := E ⊓ stabSub Y with hEYdef
    have hEYle : EY ≤ E := by rw [hEYdef]; exact inf_le_left
    have hEYne : EY ≠ E := by
      intro h
      have h0 : E3.mQuot E EY = 0 := by rw [h]; exact E3.mQuot_self E
      omega
    obtain ⟨e₁, he₁E, he₁Y⟩ : ∃ e ∈ E, e ∉ EY := by
      by_contra h
      have hle : E ≤ EY := fun x hx => by
        by_contra hxY
        exact h ⟨x, hx, hxY⟩
      exact hEYne (le_antisymm hEYle hle)
    obtain ⟨hK₁le, hK₁m⟩ := s16c167_four_mQuot_sup_zpowers (E := E) (H := EY)
      F.sq_E F.comm hEYle he₁E he₁Y
    have hK₁one : E3.mQuot E (EY ⊔ Subgroup.zpowers e₁) = 1 := by omega
    have hK₁ne : EY ⊔ Subgroup.zpowers e₁ ≠ E := by
      intro h
      have h0 : E3.mQuot E (EY ⊔ Subgroup.zpowers e₁) = 0 := by
        rw [h]; exact E3.mQuot_self E
      omega
    obtain ⟨e₂, he₂E, he₂K₁⟩ : ∃ e ∈ E, e ∉ EY ⊔ Subgroup.zpowers e₁ := by
      by_contra h
      have hle : E ≤ EY ⊔ Subgroup.zpowers e₁ := fun x hx => by
        by_contra hxK
        exact h ⟨x, hx, hxK⟩
      exact hK₁ne (le_antisymm hK₁le hle)
    have he₂Y : e₂ ∉ EY := fun h => he₂K₁ (Subgroup.mem_sup_left h)
    obtain ⟨hK₂le, hK₂m⟩ := s16c167_four_mQuot_sup_zpowers (E := E) (H := EY)
      F.sq_E F.comm hEYle he₂E he₂Y
    have hK₂one : E3.mQuot E (EY ⊔ Subgroup.zpowers e₂) = 1 := by omega
    have hKne : EY ⊔ Subgroup.zpowers e₁ ≠ EY ⊔ Subgroup.zpowers e₂ := by
      intro h
      apply he₂K₁
      rw [h]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers e₂)
    exact ⟨EY ⊔ Subgroup.zpowers e₁, EY ⊔ Subgroup.zpowers e₂, hK₁le, hK₂le, hKne,
      hK₁one, hK₂one, s16c167_four_bad_stab F hY hK₁le hK₁one le_sup_left,
      s16c167_four_bad_stab F hY hK₂le hK₂one le_sup_left⟩
  · by_cases hcase2 : ∃ Y ∈ 𝒴, E3.mQuot E (E ⊓ stabSub Y) = 1 ∧
        E ⊓ centSub Y ≠ E ⊓ stabSub Y
    · obtain ⟨Y, hY, hY1, hne⟩ := hcase2
      have hidx : E3.mQuot E (E ⊓ stabSub Y) ≤ 1 := by
        have hle := s16c167_four_index_stab F hY
        have hne2 : E3.mQuot E (E ⊓ stabSub Y) ≠ 2 := fun h => hcase1 ⟨Y, hY, h⟩
        omega
      have hEYle : E ⊓ stabSub Y ≤ E := inf_le_left
      have hNYle : E ⊓ centSub Y ≤ E := inf_le_left
      have hNYEY : E ⊓ centSub Y ≤ E ⊓ stabSub Y := inf_le_inf_left E (centSub_le_stabSub Y)
      have hEYne : E ⊓ stabSub Y ≠ E := by
        intro h
        have h0 : E3.mQuot E (E ⊓ stabSub Y) = 0 := by rw [h]; exact E3.mQuot_self E
        rw [h0] at hY1
        omega
      obtain ⟨f, hfE, hfY⟩ : ∃ f ∈ E, f ∉ E ⊓ stabSub Y := by
        by_contra h
        have hle : E ≤ E ⊓ stabSub Y := fun x hx => by
          by_contra hxY
          exact h ⟨x, hx, hxY⟩
        exact hEYne (le_antisymm hEYle hle)
      have hfNY : f ∉ E ⊓ centSub Y := fun h => hfY (hNYEY h)
      have hf1 : f ≠ 1 := fun h => hfY (h ▸ (E ⊓ stabSub Y).one_mem)
      have hf2 : f * f = 1 := F.sq_E f hfE
      have hNYgrp : IsPGroup 2 ↥(E ⊓ stabSub Y) := hEgrp.to_le hEYle
      have hNYm0 : E3.mQuot (E ⊓ stabSub Y) (E ⊓ centSub Y) ≠ 0 := fun h0 =>
        hne ((E3.mQuot_eq_zero_iff hNYgrp hNYEY).mp h0)
      have hNY1 : E3.mQuot (E ⊓ stabSub Y) (E ⊓ centSub Y) = 1 := by
        have hker := s16c167_four_index_ker F hY
        have hpos : 0 < E3.mQuot (E ⊓ stabSub Y) (E ⊓ centSub Y) := Nat.pos_of_ne_zero hNYm0
        omega
      have hNYm : E3.mQuot E (E ⊓ centSub Y) = 2 := by
        have hadd := E3.mQuot_add (V := E) (U := E ⊓ centSub Y) (U' := E ⊓ stabSub Y)
          hNYEY hEYle
        rw [hNY1, hY1] at hadd
        omega
      obtain ⟨hF₂le, hF₂m⟩ := s16c167_four_mQuot_sup_zpowers (E := E) (H := E ⊓ centSub Y)
        F.sq_E F.comm hNYle hfE hfNY
      have hF₂one : E3.mQuot E (E ⊓ centSub Y ⊔ Subgroup.zpowers f) = 1 := by omega
      have hcent : E ⊓ centSub Y ≤
          Subgroup.centralizer ((Subgroup.zpowers f : Subgroup (MulAut W)) : Set (MulAut W)) := by
        intro n hn
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rcases s16c167_mem_zpowers_eq_one_or hf2 hf1 hz with hz1 | hzf
        · rw [hz1, one_mul, mul_one]
        · rw [hzf]
          exact (F.comm n (hNYle hn) f hfE).symm
      have hnorm : E ⊓ centSub Y ≤
          Subgroup.normalizer ((Subgroup.zpowers f : Subgroup (MulAut W)) : Set (MulAut W)) :=
        hcent.trans (Subgroup.centralizer_le_normalizer _)
      have hcut : (E ⊓ centSub Y ⊔ Subgroup.zpowers f) ⊓ (E ⊓ stabSub Y) = E ⊓ centSub Y := by
        refine le_antisymm ?_ (le_inf le_sup_left hNYEY)
        intro x hx
        rw [Subgroup.mem_inf] at hx
        obtain ⟨hxsup, hxEY⟩ := hx
        have hxmul : x ∈ (↑((E ⊓ centSub Y) ⊔ Subgroup.zpowers f) : Set (MulAut W)) := by
          simpa using hxsup
        rw [Subgroup.coe_mul_of_left_le_normalizer_right (E ⊓ centSub Y)
          (Subgroup.zpowers f) hnorm] at hxmul
        rw [Set.mem_mul] at hxmul
        obtain ⟨n, hnNY, z, hzZ, hxeq⟩ := hxmul
        rw [← hxeq]
        rcases s16c167_mem_zpowers_eq_one_or hf2 hf1 hzZ with hz1 | hzf
        · rw [hz1, mul_one]; exact hnNY
        · have hnfEY : n * f ∈ E ⊓ stabSub Y := by
            have hxEY' : n * z ∈ E ⊓ stabSub Y := by simpa [hxeq] using hxEY
            rwa [hzf] at hxEY'
          have hfEY : f ∈ E ⊓ stabSub Y := by
            have hfeq : f = n⁻¹ * (n * f) := by group
            rw [hfeq]
            exact (E ⊓ stabSub Y).mul_mem ((E ⊓ stabSub Y).inv_mem (hNYEY hnNY)) hnfEY
          exact absurd hfEY hfY
      have hFne : E ⊓ stabSub Y ≠ E ⊓ centSub Y ⊔ Subgroup.zpowers f := by
        intro h
        apply hfY
        rw [h]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers f)
      exact ⟨E ⊓ stabSub Y, E ⊓ centSub Y ⊔ Subgroup.zpowers f, hEYle, hF₂le, hFne, hY1,
        hF₂one, s16c167_four_bad_stab F hY hEYle hY1 le_rfl,
        s16c167_four_bad_cent F hY hne hidx hF₂le hF₂one hcut⟩
    · have hEYle1 : ∀ Y ∈ 𝒴, E3.mQuot E (E ⊓ stabSub Y) ≤ 1 := by
        intro Y hY
        have hle := s16c167_four_index_stab F hY
        have hne2 : E3.mQuot E (E ⊓ stabSub Y) ≠ 2 := fun h => hcase1 ⟨Y, hY, h⟩
        omega
      have hNYeq : ∀ Y ∈ 𝒴, E3.mQuot E (E ⊓ stabSub Y) = 1 →
          E ⊓ centSub Y = E ⊓ stabSub Y := by
        intro Y hY h1
        by_contra hne
        exact hcase2 ⟨Y, hY, h1, hne⟩
      let N : ↥𝒴 → Subgroup (MulAut W) := fun Y => E ⊓ centSub Y
      have hNE : ∀ Y, N Y ≤ E := fun _ => inf_le_left
      have hN : ∀ Y, N Y = E ∨ E3.mQuot E (N Y) = 1 := by
        intro Y
        have hY : (Y : Subgroup W) ∈ 𝒴 := Y.2
        have hle1 : E3.mQuot E (E ⊓ stabSub Y) ≤ 1 := hEYle1 Y hY
        have hker : E3.mQuot (E ⊓ stabSub Y) (E ⊓ centSub Y) ≤ 1 :=
          s16c167_four_index_ker F hY
        rcases Nat.eq_zero_or_pos (E3.mQuot E (E ⊓ stabSub Y)) with h0 | hpos
        · have hEYeq : E ⊓ stabSub Y = E :=
            (E3.mQuot_eq_zero_iff hEgrp inf_le_left).mp h0
          have hNle : E3.mQuot E (N Y) ≤ 1 := by
            show E3.mQuot E (E ⊓ centSub Y) ≤ 1
            rw [hEYeq] at hker
            exact hker
          by_cases hz : E3.mQuot E (N Y) = 0
          · left
            exact (E3.mQuot_eq_zero_iff hEgrp (hNE Y)).mp hz
          · right
            have hzpos : 0 < E3.mQuot E (N Y) := Nat.pos_of_ne_zero hz
            omega
        · right
          have h1 : E3.mQuot E (E ⊓ stabSub Y) = 1 := by omega
          have heq := hNYeq Y hY h1
          show E3.mQuot E (E ⊓ centSub Y) = 1
          rw [heq]
          exact h1
      have hbot : ∀ x ∈ E, (∀ Y : ↥𝒴, x ∈ N Y) → x = 1 := by
        intro x _ hxN
        exact s16c167_four_faithful F (fun Y hY => (hxN ⟨Y, hY⟩).2)
      obtain ⟨Y₁, Y₂, hNYne, hN1, hN2⟩ :=
        s16c167_four_two_of_ker_inf F.sq_E hrk N hNE hN hbot
      have hbad : ∀ Y : ↥𝒴, E3.mQuot E (N Y) = 1 → fixV (N Y) ≠ fixV E := by
        intro Y hNY1
        have hY : (Y : Subgroup W) ∈ 𝒴 := Y.2
        by_cases hEYE : E ⊓ stabSub Y = E
        · refine s16c167_four_bad_cent F hY ?_ ?_ (hNE Y) hNY1 ?_
          · intro h
            have h0 : E3.mQuot E (N Y) = 0 := by
              show E3.mQuot E (E ⊓ centSub Y) = 0
              rw [h, hEYE, E3.mQuot_self]
            omega
          · rw [hEYE, E3.mQuot_self]; omega
          · show E ⊓ centSub Y ⊓ (E ⊓ stabSub Y) = E ⊓ centSub Y
            rw [hEYE]
            exact inf_eq_left.mpr inf_le_left
        · have hle1 : E3.mQuot E (E ⊓ stabSub Y) ≤ 1 := hEYle1 Y hY
          have hEY1 : E3.mQuot E (E ⊓ stabSub Y) = 1 := by
            rcases Nat.eq_zero_or_pos (E3.mQuot E (E ⊓ stabSub Y)) with h0 | hpos
            · exact absurd ((E3.mQuot_eq_zero_iff hEgrp inf_le_left).mp h0) hEYE
            · omega
          have hNeq : N Y = E ⊓ stabSub Y := hNYeq Y hY hEY1
          rw [hNeq]
          exact s16c167_four_bad_stab F hY inf_le_left hEY1 le_rfl
      exact ⟨N Y₁, N Y₂, hNE Y₁, hNE Y₂, hNYne, hN1, hN2, hbad Y₁ hN1, hbad Y₂ hN2⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
