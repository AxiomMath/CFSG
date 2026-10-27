module

public import CFSG.Quasithin.Vol2.Ch6H11Fix

public section

noncomputable section

namespace CFSG.Quasithin.H13.H11M

open CFSG.Quasithin (fixV mem_fixV rk rkIdx IsElemAbelian2 frobPow)
open CFSG.Quasithin.JonesParshall (sig sig_apply)
open CFSG.Quasithin.H13.H11P (Mat uu Uu)
open CFSG.RankThree.PartOne.KCRootAxis (SL₂)
open scoped Matrix

variable {F : Type} [Field F] [CharP F 2] {a : ℕ} (hσ : SigInv a F)

instance [Finite F] : Finite (VH a F) :=
  Finite.of_injective (fun v : VH a F => (hm v : Fin 2 → Fin 2 → F)) hm_injective

abbrev UH : Subgroup (MulAut (VH a F)) := (Uu F).map (rhoH hσ)

abbrev NH : Subgroup (MulAut (VH a F)) :=
  Subgroup.normalizer ((LH hσ : Subgroup (MulAut (VH a F))) : Set (MulAut (VH a F)))

abbrev Ws (B : Subgroup (MulAut (VH a F))) : Set F := {s | rhoH hσ (uu s) ∈ B}

theorem card_eq_card_Ws {B : Subgroup (MulAut (VH a F))} (hB : B ≤ UH hσ) :
    Nat.card B = Nat.card (Ws hσ B) := by
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective (fun s => ⟨rhoH hσ (uu s.1), s.2⟩) ⟨?_, ?_⟩
  · intro s s' h
    exact Subtype.ext (H11P.uu_injective (rhoH_injective hσ (congrArg Subtype.val h)))
  · rintro ⟨b, hb⟩
    obtain ⟨g, ⟨s, rfl⟩, rfl⟩ := hB hb
    exact ⟨⟨s, hb⟩, rfl⟩

theorem card_fix_le_of_uuH [Fintype F] (ha : 1 ≤ a) (hF : Fintype.card F = 2 ^ (2 * a))
    {B : Subgroup (MulAut (VH a F))} (hB : B ≤ UH hσ) (hB1 : B ≠ ⊥) :
    Nat.card B * Nat.card (fixV B) * 2 ^ a ≤ (2 ^ a) ^ 4 ∧ Nat.card B ≤ (2 ^ a) ^ 2 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hBW := card_eq_card_Ws hσ hB
  have hK := card_KS (a := a) (F := F) ha hF
  have hFc : Nat.card F = (2 ^ a) ^ 2 := by
    rw [Nat.card_eq_fintype_card, hF, ← pow_mul, mul_comm]
  have hW2 : Nat.card (Ws hσ B) ≤ (2 ^ a) ^ 2 := by
    rw [← hFc]
    exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hfix : ∀ v ∈ fixV B, ∀ s ∈ Ws hσ B, s * hm v 1 1 = 0 ∧
      s * hm v 1 0 + sig a s * hm v 0 1 + s * sig a s * hm v 1 1 = 0 :=
    fun v hv s hs => fix_uu_eqs hσ (hv _ hs)
  obtain ⟨s₀, hs₀, hs₀0⟩ : ∃ s ∈ Ws hσ B, s ≠ 0 := by
    by_contra hne
    push Not at hne
    apply hB1
    rw [eq_bot_iff]
    intro b hb
    obtain ⟨g, ⟨s, rfl⟩, rfl⟩ := hB hb
    rw [hne s hb, H11P.uu_zero, map_one]
    exact Subgroup.one_mem _
  have h11 : ∀ v ∈ fixV B, hm v 1 1 = 0 := fun v hv =>
    (mul_eq_zero.mp (hfix v hv s₀ hs₀).1).resolve_left hs₀0
  by_cases hind : ∃ s ∈ Ws hσ B, ∃ s' ∈ Ws hσ B, s * sig a s' ≠ sig a s * s'
  ·
    obtain ⟨s, hs, s', hs', hss'⟩ := hind
    have h01 : ∀ u ∈ fixV B, hm u 0 1 = 0 := by
      intro u hu
      have e1 := (hfix u hu s hs).2
      have e2 := (hfix u hu s' hs').2
      rw [h11 u hu, mul_zero, add_zero] at e1 e2
      have e3 : (sig a s * s' - s * sig a s') * hm u 0 1 = 0 := by
        linear_combination s' * e1 - s * e2
      exact (mul_eq_zero.mp e3).resolve_left (sub_ne_zero.mpr (Ne.symm hss'))
    have hC : Nat.card (fixV B) ≤ 2 ^ a := by
      rw [← hK]
      refine Nat.card_le_card_of_injective
        (fun v => (⟨hm v.1 0 0, sig_diag (hm_mem _) 0⟩ : KS a F)) fun v w hvw => ?_
      have e : hm v.1 0 0 = hm w.1 0 0 := congrArg Subtype.val hvw
      exact Subtype.ext (hm_ext e (by rw [h01 _ v.2, h01 _ w.2]) (by rw [h11 _ v.2, h11 _ w.2]))
    refine ⟨?_, hBW ▸ hW2⟩
    calc Nat.card B * Nat.card (fixV B) * 2 ^ a ≤ (2 ^ a) ^ 2 * 2 ^ a * 2 ^ a := by
          gcongr
          exact hBW ▸ hW2
      _ = (2 ^ a) ^ 4 := by ring
  ·
    push Not at hind
    have hσs₀ : sig a s₀ ≠ 0 := by
      rw [sig_apply]
      exact pow_ne_zero _ hs₀0
    have hWq : Nat.card (Ws hσ B) ≤ 2 ^ a := by
      rw [← hK]
      refine Nat.card_le_card_of_injective (fun s => (⟨s.1 / s₀, ?_⟩ : KS a F))
        fun s s' h => ?_
      · rw [map_div₀, div_eq_div_iff hσs₀ hs₀0]
        linear_combination -(hind s.1 s.2 s₀ hs₀)
      · have e : s.1 / s₀ = s'.1 / s₀ := congrArg Subtype.val h
        exact Subtype.ext ((div_left_inj' hs₀0).mp e)
    have hC : Nat.card (fixV B) ≤ (2 ^ a) ^ 2 := by
      rw [← hK, sq, ← Nat.card_prod]
      have hmem : ∀ v ∈ fixV B, sig a (s₀ * sig a (hm v 0 1)) = s₀ * sig a (hm v 0 1) := by
        intro v hv
        have e := (hfix v hv s₀ hs₀).2
        rw [h11 v hv, sig_offdiag (hm_mem v)] at e
        rw [map_mul, hσ]
        linear_combination e - s₀ * sig a (hm v 0 1) * h2
      refine Nat.card_le_card_of_injective (fun v => ((⟨hm v.1 0 0, sig_diag (hm_mem _) 0⟩ :
        KS a F), (⟨s₀ * sig a (hm v.1 0 1), hmem v.1 v.2⟩ : KS a F))) fun v w hvw => ?_
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at hvw
      obtain ⟨e1, e2⟩ := hvw
      have e3 : hm v.1 0 1 = hm w.1 0 1 :=
        sig_injective (mul_left_cancel₀ hs₀0 e2)
      exact Subtype.ext (hm_ext e1 e3 (by rw [h11 _ v.2, h11 _ w.2]))
    refine ⟨?_, hBW ▸ hWq.trans (Nat.le_self_pow (by norm_num) _)⟩
    calc Nat.card B * Nat.card (fixV B) * 2 ^ a ≤ 2 ^ a * (2 ^ a) ^ 2 * 2 ^ a := by
          gcongr
          exact hBW ▸ hWq
      _ = (2 ^ a) ^ 4 := by ring

theorem caseH [Fintype F] (ha : 1 < a) (hF : Fintype.card F = 2 ^ (2 * a)) {θ₀ : F}
    (hθ₀ : sig a θ₀ ≠ θ₀) {A : Subgroup (MulAut (VH a F))} (hAN : A ≤ NH hσ) (hA1 : A ≠ ⊥)
    (hA : IsElemAbelian2 A) (hB : A ⊓ LH hσ ≤ UH hσ) :
    Nat.card A * Nat.card (fixV A) * 2 ^ a ≤ 2 * (2 ^ a) ^ 4 ∧
    (Nat.card A * Nat.card (fixV A) * 4 ≤ (2 ^ a) ^ 4 ∨
      (a = 2 ∧ ∃ t ∈ A, Nat.card (fixV (Subgroup.zpowers t)) * 2 ^ a = (2 ^ a) ^ 4)) ∧
    (A ≤ LH hσ → Nat.card A * Nat.card (fixV A) * 2 ^ a ≤ (2 ^ a) ^ 4) := by
  have ha1 : 1 ≤ a := ha.le
  have h4 : 4 ≤ 2 ^ a := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have hsq : ∀ x ∈ A, x * x = 1 := fun x hx => by rw [← sq]; exact hA.2 x hx
  by_cases hAL : A ≤ LH hσ
  · have hBA : A ⊓ LH hσ = A := inf_eq_left.mpr hAL
    rw [hBA] at hB
    obtain ⟨hb1, -⟩ := card_fix_le_of_uuH hσ ha1 hF hB hA1
    refine ⟨hb1.trans (Nat.le_mul_of_pos_left _ (by norm_num)), Or.inl ?_, fun _ => hb1⟩
    calc Nat.card A * Nat.card (fixV A) * 4 ≤ Nat.card A * Nat.card (fixV A) * 2 ^ a :=
          Nat.mul_le_mul_left _ h4
      _ ≤ (2 ^ a) ^ 4 := hb1
  · obtain ⟨f, hfA, hfL⟩ := Set.not_subset.mp hAL
    have hform : ∀ x ∈ A, x ∉ LH hσ → ∃ M, FormS x M := fun x hx hxL =>
      (mem_LH_or_formS hσ ha1 hF hθ₀ (hAN hx) (hsq x hx)).resolve_left hxL
    obtain ⟨Mf, hMf⟩ := hform f hfA hfL
    set B := A ⊓ LH hσ with hBdef
    have hfB : f ∉ B := fun h => hfL h.2
    have hout : ∀ g ∈ A, g ∉ B → f * g ∈ B := by
      intro g hg hgB
      obtain ⟨Mg, hMg⟩ := hform g hg (fun h => hgB ⟨hg, h⟩)
      exact ⟨A.mul_mem hfA hg, mul_mem_LH_of_formS hσ hMf hMg⟩
    have hcard : Nat.card A = 2 * Nat.card B :=
      H11P.card_eq_two_mul inf_le_left hfA hfB (fun g hg => hA.1 f hfA g hg) hout
    have hft : Nat.card (fixV (Subgroup.zpowers f)) = (2 ^ a) ^ 3 :=
      card_fix_formS hσ ha1 hF hθ₀ hMf
    have hCf : Nat.card (fixV A) ≤ (2 ^ a) ^ 3 := by
      rw [← hft]
      exact Subgroup.card_le_of_le (fixV_anti (Subgroup.zpowers_le.mpr hfA))
    have key : Nat.card B * Nat.card (fixV A) * 2 ^ a ≤ (2 ^ a) ^ 4 := by
      by_cases hB1 : B = ⊥
      · rw [hB1, Subgroup.card_bot, one_mul]
        calc Nat.card (fixV A) * 2 ^ a ≤ (2 ^ a) ^ 3 * 2 ^ a := Nat.mul_le_mul_right _ hCf
          _ = (2 ^ a) ^ 4 := by ring
      · obtain ⟨hb1, -⟩ := card_fix_le_of_uuH hσ ha1 hF hB hB1
        have hle : Nat.card (fixV A) ≤ Nat.card (fixV B) :=
          Subgroup.card_le_of_le (fixV_anti inf_le_left)
        calc Nat.card B * Nat.card (fixV A) * 2 ^ a ≤
            Nat.card B * Nat.card (fixV B) * 2 ^ a := by gcongr
          _ ≤ (2 ^ a) ^ 4 := hb1
    rw [hcard]
    refine ⟨by linarith, ?_, fun h => (hAL h).elim⟩
    by_cases ha2 : a = 2
    · exact Or.inr ⟨ha2, f, hfA, by rw [hft]; ring⟩
    · left
      have h8 : 8 ≤ 2 ^ a := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h1 : Nat.card B * Nat.card (fixV A) * 8 ≤ Nat.card B * Nat.card (fixV A) * 2 ^ a :=
        Nat.mul_le_mul_left _ h8
      linarith

theorem exists_conj_stdH [Fintype F] (ha : 1 ≤ a) (hF : Fintype.card F = 2 ^ (2 * a))
    {A : Subgroup (MulAut (VH a F))} (hA : IsElemAbelian2 A) :
    ∃ g ∈ LH hσ, conjSub g A ⊓ LH hσ ≤ UH hσ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFn : Nat.card F = 2 ^ (2 * a) := by rw [Nat.card_eq_fintype_card, hF]
  set B' : Subgroup (SL₂ F) := (A ⊓ LH hσ).comap (rhoH hσ) with hB'
  have hB'2 : IsPGroup 2 B' := by
    rintro ⟨x, hx⟩
    refine ⟨1, Subtype.ext (rhoH_injective hσ ?_)⟩
    have h := hA.2 _ hx.1
    simpa using h
  obtain ⟨g₁, hg₁⟩ := H11P.exists_conj_le_Uu (by omega) hFn hB'2
  refine ⟨rhoH hσ g₁, ⟨g₁, rfl⟩, ?_⟩
  rintro _ ⟨⟨x, hx, rfl⟩, hxL⟩
  have hxL' : x ∈ LH hσ := by
    have e : x = (rhoH hσ g₁)⁻¹ * (MulAut.conj (rhoH hσ g₁)).toMonoidHom x * rhoH hσ g₁ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact (LH hσ).mul_mem ((LH hσ).mul_mem ((LH hσ).inv_mem ⟨_, rfl⟩) hxL) ⟨_, rfl⟩
  obtain ⟨p, rfl⟩ := hxL'
  have hp : p ∈ B' := ⟨hx, ⟨p, rfl⟩⟩
  refine ⟨g₁ * p * g₁⁻¹, hg₁ ⟨p, hp, rfl⟩, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [map_mul, map_mul, map_inv]

theorem h11_cardH [Fintype F] (ha : 1 < a) (hF : Fintype.card F = 2 ^ (2 * a)) {θ₀ : F}
    (hθ₀ : sig a θ₀ ≠ θ₀) {A : Subgroup (MulAut (VH a F))} (hAN : A ≤ NH hσ) (hA1 : A ≠ ⊥)
    (hA : IsElemAbelian2 A) :
    Nat.card A * Nat.card (fixV A) * 2 ^ a ≤ 2 * (2 ^ a) ^ 4 ∧
    (Nat.card A * Nat.card (fixV A) * 4 ≤ (2 ^ a) ^ 4 ∨
      (a = 2 ∧ ∃ t ∈ A, Nat.card (fixV (Subgroup.zpowers t)) * 2 ^ a = (2 ^ a) ^ 4)) ∧
    (A ≤ LH hσ → Nat.card A * Nat.card (fixV A) * 2 ^ a ≤ (2 ^ a) ^ 4) := by
  obtain ⟨g, hgL, hstd⟩ := exists_conj_stdH hσ ha.le hF hA
  have hgN : g ∈ NH hσ := Subgroup.le_normalizer hgL
  have hA'N : conjSub g A ≤ NH hσ := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (NH hσ).mul_mem ((NH hσ).mul_mem hgN (hAN hx)) ((NH hσ).inv_mem hgN)
  have hA'1 : conjSub g A ≠ ⊥ := fun h =>
    hA1 ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective).mp h)
  have hA'e : IsElemAbelian2 (conjSub g A) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hA.1 x hx y hy]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hA.2 x hx, map_one]
  obtain ⟨c1, c2, c3⟩ := caseH hσ ha hF hθ₀ hA'N hA'1 hA'e hstd
  rw [card_conjSub, card_fixV_conjSub] at c1 c2 c3
  refine ⟨c1, ?_, fun hAL => c3 ?_⟩
  · rcases c2 with c2 | ⟨ha2, t, ht, htc⟩
    · exact Or.inl c2
    · obtain ⟨x, hx, rfl⟩ := ht
      refine Or.inr ⟨ha2, x, hx, ?_⟩
      rw [← card_fixV_conjSub g (Subgroup.zpowers x), conjSub, MonoidHom.map_zpowers]
      exact htc
  · rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (LH hσ).mul_mem ((LH hσ).mul_mem hgL (hAL hx)) ((LH hσ).inv_mem hgL)

theorem exists_sig_ne [Fintype F] (ha : 1 ≤ a) (hF : Fintype.card F = 2 ^ (2 * a)) :
    ∃ θ : F, sig a θ ≠ θ := by
  by_contra h
  push Not at h
  have h1 := card_KS (a := a) (F := F) ha hF
  have h2 : Nat.card (KS a F) = Nat.card F := Nat.card_congr (Equiv.subtypeUnivEquiv h)
  rw [h2, Nat.card_eq_fintype_card, hF] at h1
  have := Nat.pow_right_injective (le_refl 2) h1
  omega

theorem card_VH [Fintype F] (ha : 1 ≤ a) (hF : Fintype.card F = 2 ^ (2 * a)) :
    Nat.card (VH a F) = 2 ^ (4 * a) := by
  rw [← CFSG.Quasithin.B45L2.card_hermA ha hF]
  exact Nat.card_congr (Additive.ofMul.trans (JonesParshall.hermEquiv a F).toEquiv)

theorem h11_modelH [Fintype F] (ha : 1 < a) (hF : Fintype.card F = 2 ^ (2 * a))
    {A : Subgroup (MulAut (VH a F))} (hAN : A ≤ NH hσ) (hA1 : A ≠ ⊥) (hA : IsElemAbelian2 A) :
    rk A + a ≤ rkIdx (fixV A) + 1 ∧
      (rk A + 2 ≤ rkIdx (fixV A) ∨ (a = 2 ∧ ∃ t ∈ A, rkIdx (fixV (Subgroup.zpowers t)) = a)) ∧
      (A ≤ LH hσ → rk A + a ≤ rkIdx (fixV A)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨θ₀, hθ₀⟩ := exists_sig_ne (a := a) (F := F) ha.le hF
  obtain ⟨c1, c2, c3⟩ := h11_cardH hσ ha hF hθ₀ hAN hA1 hA
  have hV : Nat.card (VH a F) = 2 ^ (4 * a) := card_VH ha.le hF
  have hVp : IsPGroup 2 (VH a F) := IsPGroup.of_card hV
  have hAp : IsPGroup 2 A := by
    rintro ⟨x, hx⟩
    exact ⟨1, Subtype.ext (by simpa using hA.2 x hx)⟩
  obtain ⟨r, hr⟩ := hAp.exists_card_eq
  obtain ⟨k, hk⟩ := (hVp.to_subgroup (fixV A)).exists_card_eq
  rw [H11P.rk_eq_of_card hr, H11P.rkIdx_eq_of_card hk hV]
  rw [hr, hk] at c1 c2 c3
  have hkV : k ≤ 4 * a := by
    have h1 := Subgroup.card_le_card_group (fixV A)
    rw [hk, hV] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  have hpow : ∀ x y : ℕ, 2 ^ x ≤ 2 ^ y → x ≤ y := fun x y h =>
    (Nat.pow_le_pow_iff_right (by norm_num)).mp h
  refine ⟨?_, ?_, fun hAL => ?_⟩
  · have := hpow (r + k + a) (1 + 4 * a) (by
      calc 2 ^ (r + k + a) = 2 ^ r * 2 ^ k * 2 ^ a := by rw [pow_add, pow_add]
        _ ≤ 2 * (2 ^ a) ^ 4 := c1
        _ = 2 ^ (1 + 4 * a) := by rw [pow_add, pow_one, ← pow_mul, mul_comm a 4])
    omega
  · rcases c2 with c2 | ⟨ha2, t, ht, htc⟩
    · left
      have := hpow (r + k + 2) (4 * a) (by
        calc 2 ^ (r + k + 2) = 2 ^ r * 2 ^ k * 4 := by rw [pow_add, pow_add]; norm_num
          _ ≤ (2 ^ a) ^ 4 := c2
          _ = 2 ^ (4 * a) := by rw [← pow_mul, mul_comm a 4])
      omega
    · right
      refine ⟨ha2, t, ht, ?_⟩
      obtain ⟨j, hj⟩ := (hVp.to_subgroup (fixV (Subgroup.zpowers t))).exists_card_eq
      rw [H11P.rkIdx_eq_of_card hj hV]
      rw [hj] at htc
      have h1 : 2 ^ (j + a) = 2 ^ (4 * a) := by
        rw [pow_add, htc, ← pow_mul, mul_comm a 4]
      have h2 := Nat.pow_right_injective (le_refl 2) h1
      omega
  · have := hpow (r + k + a) (4 * a) (by
      calc 2 ^ (r + k + a) = 2 ^ r * 2 ^ k * 2 ^ a := by rw [pow_add, pow_add]
        _ ≤ (2 ^ a) ^ 4 := c3 hAL
        _ = 2 ^ (4 * a) := by rw [← pow_mul, mul_comm a 4])
    omega

end CFSG.Quasithin.H13.H11M

end
