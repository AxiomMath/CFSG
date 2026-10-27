module

public import CFSG.Quasithin.H13.L32A764f

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.RuType
open CFSG.Quasithin.CosetGeom
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

namespace Ctx764

variable (C : Ctx764 G T L V)
include C

theorem four_le_card_dS_inf_V (h4 : Nat.card ↥(u0 T V) = 4) {s : G}
    (hs : s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) (hsQ : s ∉ pCoreOf 2 (hz T V)) :
    4 ≤ Nat.card ↥(dS T V s ⊓ V) := by
  have h64 := C.card_sup_V hs hsQ
  have hle : dS T V s ⊔ V ≤ V ⊔ u0 T V := sup_le (C.dS_le hs) le_sup_left
  have hc := Subgroup.card_le_of_le hle
  rw [C.card_sup_u0, h4] at hc
  nlinarith

theorem card_dS_inf_V_of_four (h4 : Nat.card ↥(u0 T V) = 4) {s : G}
    (hs : s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) (hsQ : s ∉ pCoreOf 2 (hz T V)) :
    Nat.card ↥(dS T V s ⊓ V) = 4 := by
  have hge := C.four_le_card_dS_inf_V h4 hs hsQ
  obtain ⟨-, hV8, -, -, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
  have hdvd : Nat.card ↥(dS T V s ⊓ V) ∣ 2 ^ 3 := by
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← hV8]
    exact Subgroup.card_dvd_of_le inf_le_right
  rcases (Nat.dvd_prime_pow Nat.prime_two).mp hdvd with ⟨k, hk, e⟩
  rw [e] at hge ⊢
  interval_cases k
  · simp at hge
  · simp at hge
  · rfl
  ·
    exfalso
    have hDV : dS T V s ⊓ V = V :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [e, hV8]; norm_num)
    have hDV' : dS T V s ⊓ V = dS T V s :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [e, C.card_dS hs hsQ]; norm_num)
    have hD : dS T V s = V := hDV'.symm.trans hDV
    obtain ⟨x, hxL1, -, -, hxs⟩ := C.exists_fpf
    obtain ⟨hs', hs'Q⟩ := C.conj_mem_R1 hxL1 hs hsQ
    have hxH : x ∈ hz T V := C.hF.L₁T_le_H (Subgroup.mem_sup_left hxL1)
    have hxV : x ∈ Subgroup.normalizer (V : Set G) :=
      C.hF.L₁T_normalizes_Vp (Subgroup.mem_sup_left hxL1)
    have hD' : dS T V (x * s * x⁻¹) = V := by
      rw [← C.conj_dS_eq hxH hs hsQ hs' hs'Q, hD, conjSub_eq_self_iff.mpr hxV]
    have heq := C.dS_sup_eq hs hsQ hs' hs'Q (hxs s hs hsQ)
    rw [hD, hD', sup_idem] at heq
    have hc := C.card_sup_u0
    rw [← heq, hV8, h4] at hc
    omega

theorem exists_comm_of_four (h4 : Nat.card ↥(u0 T V) = 4) {s : G}
    (hs : s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) (hsQ : s ∉ pCoreOf 2 (hz T V)) :
    ∃ u ∈ fsuU T V, u * s * u⁻¹ * s⁻¹ ∈ V ∧ u * s * u⁻¹ * s⁻¹ ∉ fsuV1 T V := by
  have hge := C.four_le_card_dS_inf_V h4 hs hsQ
  obtain ⟨d, hd, hdV1⟩ : ∃ d ∈ dS T V s ⊓ V, d ∉ fsuV1 T V := by
    by_contra hno
    push Not at hno
    have := Subgroup.card_le_of_le (show dS T V s ⊓ V ≤ fsuV1 T V from hno)
    rw [C.hF.card_V₁] at this
    omega
  obtain ⟨hdD, hdV⟩ := Subgroup.mem_inf.mp hd
  obtain ⟨u, hu, c, hc, rfl⟩ := (mem_dS_iff C.hUc (C.R1_le_normalizer_U hs)).mp hdD
  have hcV : c ∈ V := (inf_le_left : fsuV1 T V ≤ V) hc
  refine ⟨u, hu, ?_, fun h => hdV1 (mul_mem h hc)⟩
  have := mul_mem hdV (inv_mem hcV)
  simpa using this

theorem comm_mem_of_four (h4 : Nat.card ↥(u0 T V) = 4) {s : G}
    (hs : s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) (hsQ : s ∉ pCoreOf 2 (hz T V)) {u₁ u₂ : G}
    (hu₁ : u₁ ∈ fsuU T V) (hu₂ : u₂ ∈ fsuU T V) (h₁ : u₁ * s * u₁⁻¹ * s⁻¹ ∈ V)
    (h₂ : u₂ * s * u₂⁻¹ * s⁻¹ ∈ V) :
    u₁ * s * u₁⁻¹ * s⁻¹ ∈ fsuV1 T V ∨ u₂ * s * u₂⁻¹ * s⁻¹ ∈ fsuV1 T V ∨
      (u₁ * s * u₁⁻¹ * s⁻¹) * (u₂ * s * u₂⁻¹ * s⁻¹)⁻¹ ∈ fsuV1 T V := by
  by_cases ha : u₁ * s * u₁⁻¹ * s⁻¹ ∈ fsuV1 T V
  · exact Or.inl ha
  by_cases hb : u₂ * s * u₂⁻¹ * s⁻¹ ∈ fsuV1 T V
  · exact Or.inr (Or.inl hb)
  right; right
  have hcard := C.card_dS_inf_V_of_four h4 hs hsQ
  have hmem : ∀ {u : G}, u ∈ fsuU T V → u * s * u⁻¹ * s⁻¹ ∈ V →
      u * s * u⁻¹ * s⁻¹ ∈ dS T V s ⊓ V := fun hu hV =>
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left (Subgroup.subset_closure ⟨_, hu, rfl⟩), hV⟩
  refine L32NSet14.mul_mem_of_card_eq_two_mul (W := fsuV1 T V) (X := dS T V s ⊓ V)
    (le_inf le_sup_right inf_le_left)
    (by rw [hcard, C.hF.card_V₁]) (by rw [C.hF.card_V₁]; norm_num) (hmem hu₁ h₁)
    (inv_mem (hmem hu₂ h₂)) ha fun h => hb (by simpa using inv_mem h)

theorem mem_union_of_four (h4 : Nat.card ↥(u0 T V) = 4) {f : G} (hf : f ∈ V ⊔ u0 T V) :
    f ∈ u0 T V ∨ ∃ s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T),
      s ∉ pCoreOf 2 (hz T V) ∧ ∃ u ∈ fsuU T V, f * (u * s * u⁻¹ * s⁻¹)⁻¹ ∈ fsuV1 T V := by
  have hVU : V ≤ fsuU T V := le_conjClosure V _
  have hU0U : u0 T V ≤ fsuU T V := centralizerMod_le_left _ _ _
  have hV1U0 := fsuV1_le_u0 C.hyp C.hMod
  have hV1V : fsuV1 T V ≤ V := inf_le_left
  obtain ⟨v, hv, u₀, hu₀, rfl⟩ := mem_sup_of_comm C.hUc hVU hU0U hf
  by_cases hvV1 : v ∈ fsuV1 T V
  · exact Or.inl (mul_mem (hV1U0 hvV1) hu₀)
  right
  obtain ⟨x, hxL1, hx3, hfpf, hxs⟩ := C.exists_fpf
  have hxK : x ∈ kz T V := l1_le_kz C.hyp C.hMod hxL1
  have hxH : x ∈ hz T V := C.hF.L₁T_le_H (Subgroup.mem_sup_left hxL1)
  have hxV : x ∈ Subgroup.normalizer (V : Set G) :=
    C.hF.L₁T_normalizes_Vp (Subgroup.mem_sup_left hxL1)
  have hxV1 : x ∈ Subgroup.normalizer (fsuV1 T V : Set G) := C.hF.H_normalizes_V₁ hxH
  have hxU0 : x ∈ Subgroup.normalizer (u0 T V : Set G) := hz_le_normalizer_u0 C.hyp C.hMod hxH
  obtain ⟨s₁, hs₁, hs₁Q, -⟩ := C.exists_two
  obtain ⟨hs₂, hs₂Q⟩ := C.conj_mem_R1 hxL1 hs₁ hs₁Q
  obtain ⟨hs₃, hs₃Q⟩ := C.conj_mem_R1 hxL1 hs₂ hs₂Q
  have hx31 : x * (x * (x * s₁ * x⁻¹) * x⁻¹) * x⁻¹ = s₁ := by
    calc x * (x * (x * s₁ * x⁻¹) * x⁻¹) * x⁻¹ = x ^ 3 * s₁ * (x ^ 3)⁻¹ := by
          rw [pow_three]; group
      _ = s₁ := by rw [hx3]; group
  have hD12 := C.conj_dS_eq hxH hs₁ hs₁Q hs₂ hs₂Q
  have hD23 := C.conj_dS_eq hxH hs₂ hs₂Q hs₃ hs₃Q
  obtain ⟨hs₄, hs₄Q⟩ := C.conj_mem_R1 hxL1 hs₃ hs₃Q
  have hD31 := C.conj_dS_eq hxH hs₃ hs₃Q hs₄ hs₄Q
  rw [hx31] at hD31
  have hconj : ∀ {a : G} {y : G}, y ∈ dS T V a → x * y * x⁻¹ ∈ conjSub x (dS T V a) :=
    fun hy => mul_mem_conjSub hy
  have hrep : ∀ {s w : G}, s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) → s ∉ pCoreOf 2 (hz T V) →
      w ∈ V → ∃ t ∈ u0 T V, w * t ∈ dS T V s := by
    intro s w hs hsQ hw
    have hw' : w ∈ dS T V s ⊔ u0 T V := by
      rw [C.dS_sup_u0 hs hsQ]
      exact Subgroup.mem_sup_left hw
    obtain ⟨d, hd, t, ht, hdt⟩ := mem_sup_of_comm C.hUc (C.dS_le_U hs) hU0U hw'
    exact ⟨t⁻¹, inv_mem ht, by rw [hdt]; group; exact hd⟩
  have hfin : ∀ {s : G}, s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) → s ∉ pCoreOf 2 (hz T V) →
      ∀ {t : G}, v * t ∈ dS T V s → t⁻¹ * u₀ ∈ fsuV1 T V →
      ∃ s' ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T), s' ∉ pCoreOf 2 (hz T V) ∧
        ∃ u ∈ fsuU T V, v * u₀ * (u * s' * u⁻¹ * s'⁻¹)⁻¹ ∈ fsuV1 T V := by
    intro s hs hsQ t hd htu
    have hf : v * u₀ ∈ dS T V s := by
      rw [show v * u₀ = (v * t) * (t⁻¹ * u₀) by group]
      exact mul_mem hd (Subgroup.mem_sup_right htu)
    obtain ⟨u, hu, c, hc, hfc⟩ := (mem_dS_iff C.hUc (C.R1_le_normalizer_U hs)).mp hf
    refine ⟨s, hs, hsQ, u, hu, ?_⟩
    have hcU : u * s * u⁻¹ * s⁻¹ ∈ fsuU T V := C.dS_le_U hs
      (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨u, hu, rfl⟩))
    rw [hfc, C.hUc _ hcU c (hV1U0.trans hU0U hc), mul_inv_cancel_right]
    exact hc
  obtain ⟨t₁, ht₁, hd₁⟩ := hrep hs₁ hs₁Q hv
  obtain ⟨t₂, ht₂, hd₂⟩ := hrep hs₂ hs₂Q hv
  obtain ⟨t₃, ht₃, hd₃⟩ := hrep hs₃ hs₃Q hv
  by_cases e₁ : t₁⁻¹ * u₀ ∈ fsuV1 T V
  · exact hfin hs₁ hs₁Q hd₁ e₁
  by_cases e₂ : t₂⁻¹ * u₀ ∈ fsuV1 T V
  · exact hfin hs₂ hs₂Q hd₂ e₂
  by_cases e₃ : t₃⁻¹ * u₀ ∈ fsuV1 T V
  · exact hfin hs₃ hs₃Q hd₃ e₃
  exfalso
  have hcardU0 : Nat.card ↥(u0 T V) = 2 * Nat.card ↥(fsuV1 T V) := by
    rw [h4, C.hF.card_V₁]
  have hsq : ∀ u ∈ fsuU T V, u * u = 1 := fun u hu => by rw [← sq]; exact C.hUe u hu
  have hagree : ∀ {t t' : G}, t ∈ u0 T V → t' ∈ u0 T V → t⁻¹ * u₀ ∉ fsuV1 T V →
      t'⁻¹ * u₀ ∉ fsuV1 T V → t⁻¹ * t' ∈ fsuV1 T V := by
    intro t t' ht ht' hn hn'
    have h1 := L32NSet14.mul_mem_of_card_eq_two_mul hV1U0 hcardU0
      (by rw [C.hF.card_V₁]; norm_num) (mul_mem (inv_mem ht) hu₀) (inv_mem (mul_mem (inv_mem ht')
        hu₀)) hn fun h => hn' (by simpa using inv_mem h)
    rwa [show t⁻¹ * u₀ * (t'⁻¹ * u₀)⁻¹ = t⁻¹ * t' * (t'⁻¹ * u₀ * u₀⁻¹ * t') by group,
      show t'⁻¹ * u₀ * u₀⁻¹ * t' = 1 by group, mul_one] at h1
  have h13 := hagree ht₁ ht₃ e₁ e₃
  have h12 := hagree ht₁ ht₂ e₁ e₂
  have hxt : ∀ {t : G}, t ∈ u0 T V → x * t * x⁻¹ ∈ u0 T V ∧ t⁻¹ * (x * t * x⁻¹) ∈ fsuV1 T V := by
    intro t ht
    have hxtU0 : x * t * x⁻¹ ∈ u0 T V := (Subgroup.mem_normalizer_iff.mp hxU0 t).mp ht
    refine ⟨hxtU0, ?_⟩
    have h1 := ((mem_u0_iff C.hyp C.hMod).mp ht).2 x hxK
    have h3 : t⁻¹ * (x * t * x⁻¹) = x * t * x⁻¹ * t⁻¹ :=
      C.hUc t⁻¹ (inv_mem (hU0U ht)) (x * t * x⁻¹) (hU0U hxtU0)
    rw [h3]
    exact h1
  obtain ⟨w₁, hw₁⟩ : ∃ w₁ : G, w₁ = x * v * x⁻¹ := ⟨_, rfl⟩
  obtain ⟨w₂, hw₂⟩ : ∃ w₂ : G, w₂ = x * w₁ * x⁻¹ := ⟨_, rfl⟩
  have hw₁V : w₁ ∈ V := hw₁ ▸ (Subgroup.mem_normalizer_iff.mp hxV v).mp hv
  have hA : w₁ * (x * t₂ * x⁻¹) ∈ dS T V (x * (x * s₁ * x⁻¹) * x⁻¹) := by
    rw [← hD23]
    have := hconj hd₂
    rwa [show x * (v * t₂) * x⁻¹ = w₁ * (x * t₂ * x⁻¹) by rw [hw₁]; group] at this
  have hB : w₁ * (x * t₃ * x⁻¹) ∈ dS T V s₁ := by
    rw [← hD31]
    have := hconj hd₃
    rwa [show x * (v * t₃) * x⁻¹ = w₁ * (x * t₃ * x⁻¹) by rw [hw₁]; group] at this
  have hC : w₂ * (x * (x * t₂ * x⁻¹) * x⁻¹) ∈ dS T V s₁ := by
    rw [← hD31]
    have := hconj hA
    rwa [show x * (w₁ * (x * t₂ * x⁻¹)) * x⁻¹ = w₂ * (x * (x * t₂ * x⁻¹) * x⁻¹) by
      rw [hw₂]; group] at this
  obtain ⟨ht₂', ht₂e⟩ := hxt ht₂
  obtain ⟨ht₂'', ht₂e'⟩ := hxt ht₂'
  obtain ⟨ht₃', ht₃e⟩ := hxt ht₃
  obtain ⟨t₂', ht₂'def⟩ : ∃ t : G, t = x * t₂ * x⁻¹ := ⟨_, rfl⟩
  obtain ⟨t₂'', ht₂''def⟩ : ∃ t : G, t = x * t₂' * x⁻¹ := ⟨_, rfl⟩
  obtain ⟨t₃', ht₃'def⟩ : ∃ t : G, t = x * t₃ * x⁻¹ := ⟨_, rfl⟩
  rw [← ht₂'def] at ht₂' ht₂e hA
  rw [← ht₂'def, ← ht₂''def] at ht₂'' ht₂e' hC
  rw [← ht₃'def] at ht₃' ht₃e hB
  have hV1D : fsuV1 T V ≤ dS T V s₁ := le_sup_right
  have hc13 : t₁⁻¹ * t₃' ∈ fsuV1 T V := by
    rw [show t₁⁻¹ * t₃' = (t₁⁻¹ * t₃) * (t₃⁻¹ * t₃') by group]
    exact mul_mem h13 ht₃e
  have hc12 : t₁⁻¹ * t₂'' ∈ fsuV1 T V := by
    rw [show t₁⁻¹ * t₂'' = (t₁⁻¹ * t₂) * (t₂⁻¹ * t₂') * (t₂'⁻¹ * t₂'') by group]
    exact mul_mem (mul_mem h12 ht₂e) ht₂e'
  have hvw : v * w₁ ∈ dS T V s₁ := by
    have h1 := mul_mem hd₁ hB
    have ht13 : t₁ * t₃' ∈ fsuV1 T V := by
      rw [show t₁ * t₃' = (t₁ * t₁) * (t₁⁻¹ * t₃') by group, hsq t₁ (hU0U ht₁), one_mul]
      exact hc13
    have e : v * t₁ * (w₁ * t₃') = v * w₁ * (t₁ * t₃') := by
      have hc := C.hUc t₁ (hU0U ht₁) w₁ (hVU hw₁V)
      calc v * t₁ * (w₁ * t₃') = v * (t₁ * w₁) * t₃' := by group
        _ = v * (w₁ * t₁) * t₃' := by rw [hc]
        _ = v * w₁ * (t₁ * t₃') := by group
    rw [e] at h1
    have := mul_mem h1 (hV1D (inv_mem ht13))
    simpa [mul_assoc] using this
  have hnorm := C.norm_mem hxL1 hx3 hfpf hv
  rw [← hw₁, ← hw₂] at hnorm
  have hw₂D : w₂ ∈ dS T V s₁ := by
    have := mul_mem (inv_mem hvw) (hV1D hnorm)
    simpa [mul_assoc] using this
  have ht₂''D : t₂'' ∈ dS T V s₁ := by
    have := mul_mem (inv_mem hw₂D) hC
    simpa using this
  have ht₂''V1 : t₂'' ∈ fsuV1 T V := by
    rw [← C.dS_inf_u0 hs₁ hs₁Q]
    exact Subgroup.mem_inf.mpr ⟨ht₂''D, ht₂''⟩
  have ht₁V1 : t₁ ∈ fsuV1 T V := by
    rw [show t₁ = t₂'' * (t₁⁻¹ * t₂'')⁻¹ by group]
    exact mul_mem ht₂''V1 (inv_mem hc12)
  have ht₃'V1 : t₃' ∈ fsuV1 T V := by
    rw [show t₃' = t₁ * (t₁⁻¹ * t₃') by group]
    exact mul_mem ht₁V1 hc13
  have hvD : v ∈ dS T V s₁ ⊓ V := by
    refine Subgroup.mem_inf.mpr ⟨?_, hv⟩
    rw [show v = (v * t₁) * t₁⁻¹ by group]
    exact mul_mem hd₁ (hV1D (inv_mem ht₁V1))
  have hw₁D : w₁ ∈ dS T V s₁ ⊓ V := by
    refine Subgroup.mem_inf.mpr ⟨?_, hw₁V⟩
    rw [show w₁ = (w₁ * t₃') * t₃'⁻¹ by group]
    exact mul_mem hB (hV1D (inv_mem ht₃'V1))
  have hw₁V1 : w₁ ∉ fsuV1 T V := by
    intro h
    apply hvV1
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hxV1) w₁).mp h
    rw [hw₁] at this
    simpa [mul_assoc] using this
  have hcard := C.card_dS_inf_V_of_four h4 hs₁ hs₁Q
  have hvw₁ := L32NSet14.mul_mem_of_card_eq_two_mul (le_inf hV1D hV1V)
    (by rw [hcard, C.hF.card_V₁]) (by rw [C.hF.card_V₁]; norm_num) hvD hw₁D hvV1 hw₁V1
  apply hvV1
  refine hfpf v hv ?_
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right (hsq v (hVU hv))
  rw [hvi, ← hw₁, ← C.hUc v (hVU hv) w₁ (hVU hw₁V)]
  exact hvw₁

end Ctx764

end CFSG.Quasithin.H13.L32A
