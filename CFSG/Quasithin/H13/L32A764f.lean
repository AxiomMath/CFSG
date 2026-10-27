module

public import CFSG.Quasithin.H13.L32A764e

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.RuType
open CFSG.Quasithin.CosetGeom
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

namespace Ctx764

variable (C : Ctx764 G T L V)
include C

theorem conj_le_of_le {x : G} (hxK : x ∈ kz T V) (hxV : x ∈ Subgroup.normalizer (V : Set G))
    {X : Subgroup G} (hVX : V ≤ X) (hXVU : X ≤ V ⊔ u0 T V) {y : G} (hy : y ∈ X) :
    x * y * x⁻¹ ∈ X := by
  have hVU : V ≤ fsuU T V := le_conjClosure V _
  have hU0U : u0 T V ≤ fsuU T V := centralizerMod_le_left _ _ _
  obtain ⟨v, hv, u, hu, rfl⟩ := mem_sup_of_comm C.hUc hVU hU0U (hXVU hy)
  have huX : u ∈ X := by
    have := mul_mem (inv_mem (hVX hv)) hy
    simpa using this
  have hxv : x * v * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hxV v).mp hv
  have hxu : x * u * x⁻¹ * u⁻¹ ∈ fsuV1 T V := ((mem_u0_iff C.hyp C.hMod).mp hu).2 x hxK
  rw [show x * (v * u) * x⁻¹ = (x * v * x⁻¹) * (x * u * x⁻¹ * u⁻¹) * u by group]
  exact mul_mem (mul_mem (hVX hxv) (hVX ((inf_le_left : fsuV1 T V ≤ V) hxu))) huX

theorem conj_mem_R1 {x : G} (hxL1 : x ∈ L₁Of L (fsuV1 T V)) {s : G}
    (hs : s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) (hsQ : s ∉ pCoreOf 2 (hz T V)) :
    x * s * x⁻¹ ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ∧ x * s * x⁻¹ ∉ pCoreOf 2 (hz T V) := by
  have hxN := le_normalizer_pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) (Subgroup.mem_sup_left hxL1)
  have hxH : x ∈ hz T V := C.hF.L₁T_le_H (Subgroup.mem_sup_left hxL1)
  refine ⟨(Subgroup.mem_normalizer_iff.mp hxN s).mp hs, fun h => hsQ ?_⟩
  have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ (inv_mem hxH)) _).mp h
  simpa [mul_assoc] using this

theorem card_inf_dS {s s' : G} (hs : s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
    (hsQ : s ∉ pCoreOf 2 (hz T V)) (hs' : s' ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
    (hs'Q : s' ∉ pCoreOf 2 (hz T V)) (h12 : s⁻¹ * s' ∉ pCoreOf 2 (hz T V)) :
    Nat.card ↥(dS T V s ⊓ dS T V s') * Nat.card ↥(V ⊔ u0 T V) = 64 := by
  have hN : dS T V s ≤ Subgroup.normalizer (dS T V s' : Set G) := by
    intro d hd
    refine mem_normalizer_of_forall_conj_mem fun e he => ?_
    rw [C.hUc d (C.dS_le_U hs hd) e (C.dS_le_U hs' he), mul_inv_cancel_right]
    exact he
  have h1 := L32NSet14.card_sup_mul_card_inf hN
  rw [C.dS_sup_eq hs hsQ hs' hs'Q h12, C.card_dS hs hsQ, C.card_dS hs' hs'Q] at h1
  rw [mul_comm, h1]

theorem card_sup_V {s : G} (hs : s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
    (hsQ : s ∉ pCoreOf 2 (hz T V)) :
    Nat.card ↥(dS T V s ⊔ V) * Nat.card ↥(dS T V s ⊓ V) = 64 := by
  obtain ⟨-, hV8, -, -, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
  have hN : dS T V s ≤ Subgroup.normalizer (V : Set G) := by
    intro d hd
    refine mem_normalizer_of_forall_conj_mem fun e he => ?_
    rw [C.hUc d (C.dS_le_U hs hd) e (le_conjClosure V _ he), mul_inv_cancel_right]
    exact he
  rw [L32NSet14.card_sup_mul_card_inf hN, C.card_dS hs hsQ, hV8]

theorem dS_inf_V_of_eight (h8 : Nat.card ↥(u0 T V) = 8) {s : G}
    (hs : s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) (hsQ : s ∉ pCoreOf 2 (hz T V)) :
    dS T V s ⊓ V = fsuV1 T V := by
  obtain ⟨x, hxL1, -, -, hxs⟩ := C.exists_fpf
  obtain ⟨hs', hs'Q⟩ := C.conj_mem_R1 hxL1 hs hsQ
  have hxK : x ∈ kz T V := l1_le_kz C.hyp C.hMod hxL1
  have hxH : x ∈ hz T V := C.hF.L₁T_le_H (Subgroup.mem_sup_left hxL1)
  have hxV : x ∈ Subgroup.normalizer (V : Set G) :=
    C.hF.L₁T_normalizes_Vp (Subgroup.mem_sup_left hxL1)
  have hle : fsuV1 T V ≤ dS T V s ⊓ V := le_inf le_sup_right inf_le_left
  refine le_antisymm ?_ hle
  by_contra hnle
  have hlt : fsuV1 T V < dS T V s ⊓ V := lt_of_le_of_ne hle fun e => hnle e.symm.le
  have h2 := Subgroup.card_lt_of_lt hlt
  rw [C.hF.card_V₁] at h2
  obtain ⟨-, hV8, -, -, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
  have hdvd : Nat.card ↥(dS T V s ⊓ V) ∣ 8 := hV8 ▸ Subgroup.card_dvd_of_le inf_le_right
  have h4 : 4 ≤ Nat.card ↥(dS T V s ⊓ V) := by
    have hdvd' : Nat.card ↥(dS T V s ⊓ V) ∣ 2 ^ 3 := by
      rw [show (2 : ℕ) ^ 3 = 8 by norm_num]
      exact hdvd
    rcases (Nat.dvd_prime_pow Nat.prime_two).mp hdvd' with ⟨k, hk, e⟩
    rw [e] at h2 ⊢
    interval_cases k <;> simp_all
  have h64 := C.card_sup_V hs hsQ
  have hX : dS T V s ⊔ V ≤ V ⊔ u0 T V := sup_le (C.dS_le hs) le_sup_left
  have hD' : dS T V (x * s * x⁻¹) ≤ dS T V s ⊔ V := by
    rw [← C.conj_dS_eq hxH hs hsQ hs' hs'Q]
    intro y hy
    rw [mem_conjSub] at hy
    have := C.conj_le_of_le hxK hxV le_sup_right hX (Subgroup.mem_sup_left hy)
    rwa [show x * (x⁻¹ * y * x) * x⁻¹ = y by group] at this
  have hVU : V ⊔ u0 T V ≤ dS T V s ⊔ V := by
    rw [← C.dS_sup_eq hs hsQ hs' hs'Q (hxs s hs hsQ)]
    exact sup_le le_sup_left hD'
  have hc := Subgroup.card_le_of_le hVU
  rw [C.card_sup_u0, h8] at hc
  nlinarith

theorem norm_mem {x : G} (hxL1 : x ∈ L₁Of L (fsuV1 T V)) (hx3 : x ^ 3 = 1)
    (hfpf : ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ fsuV1 T V → v ∈ fsuV1 T V) {v : G} (hv : v ∈ V) :
    v * (x * v * x⁻¹) * (x * (x * v * x⁻¹) * x⁻¹) ∈ fsuV1 T V := by
  have hxV : x ∈ Subgroup.normalizer (V : Set G) :=
    C.hF.L₁T_normalizes_Vp (Subgroup.mem_sup_left hxL1)
  have hVU : V ≤ fsuU T V := le_conjClosure V _
  have h1 : x * v * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hxV v).mp hv
  have h2 : x * (x * v * x⁻¹) * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hxV _).mp h1
  have hx3' : x * (x * (x * v * x⁻¹) * x⁻¹) * x⁻¹ = v := by
    calc x * (x * (x * v * x⁻¹) * x⁻¹) * x⁻¹ = x ^ 3 * v * (x ^ 3)⁻¹ := by
          rw [pow_three]; group
      _ = v := by rw [hx3]; group
  have hn : v * (x * v * x⁻¹) * (x * (x * v * x⁻¹) * x⁻¹) ∈ V := mul_mem (mul_mem hv h1) h2
  refine hfpf _ hn ?_
  have e : x * (v * (x * v * x⁻¹) * (x * (x * v * x⁻¹) * x⁻¹)) * x⁻¹ =
      (x * v * x⁻¹) * (x * (x * v * x⁻¹) * x⁻¹) * v := by
    rw [show x * (v * (x * v * x⁻¹) * (x * (x * v * x⁻¹) * x⁻¹)) * x⁻¹ =
      (x * v * x⁻¹) * (x * (x * v * x⁻¹) * x⁻¹) * (x * (x * (x * v * x⁻¹) * x⁻¹) * x⁻¹) by
      group, hx3']
  rw [e, show (x * v * x⁻¹) * (x * (x * v * x⁻¹) * x⁻¹) * v *
    (v * (x * v * x⁻¹) * (x * (x * v * x⁻¹) * x⁻¹))⁻¹ =
      ((x * v * x⁻¹) * (x * (x * v * x⁻¹) * x⁻¹) * v) * ((x * (x * v * x⁻¹) * x⁻¹)⁻¹ *
        (x * v * x⁻¹)⁻¹ * v⁻¹) by group]
  have hc1 := C.hUc v (hVU hv) _ (hVU (mul_mem h1 h2))
  rw [show (x * v * x⁻¹) * (x * (x * v * x⁻¹) * x⁻¹) * v =
    v * ((x * v * x⁻¹) * (x * (x * v * x⁻¹) * x⁻¹)) by rw [hc1]]
  rw [show v * ((x * v * x⁻¹) * (x * (x * v * x⁻¹) * x⁻¹)) * ((x * (x * v * x⁻¹) * x⁻¹)⁻¹ *
    (x * v * x⁻¹)⁻¹ * v⁻¹) = 1 by group]
  exact one_mem _

theorem mem_union_of_eight (h8 : Nat.card ↥(u0 T V) = 8) {f : G} (hf : f ∈ V ⊔ u0 T V) :
    f ∈ V ∨ f ∈ u0 T V ∨ ∃ s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T),
      s ∉ pCoreOf 2 (hz T V) ∧ ∃ u ∈ fsuU T V, f * (u * s * u⁻¹ * s⁻¹)⁻¹ ∈ fsuV1 T V := by
  classical
  have hVU : V ≤ fsuU T V := le_conjClosure V _
  have hU0U : u0 T V ≤ fsuU T V := centralizerMod_le_left _ _ _
  have hV1U0 := fsuV1_le_u0 C.hyp C.hMod
  have hV1V : fsuV1 T V ≤ V := inf_le_left
  obtain ⟨v, hv, u₀, hu₀, rfl⟩ := mem_sup_of_comm C.hUc hVU hU0U hf
  by_cases hvV1 : v ∈ fsuV1 T V
  · exact Or.inr (Or.inl (mul_mem (hV1U0 hvV1) hu₀))
  by_cases hu₀V1 : u₀ ∈ fsuV1 T V
  · exact Or.inl (mul_mem hv (hV1V hu₀V1))
  right; right
  obtain ⟨x, hxL1, hx3, -, hxs⟩ := C.exists_fpf
  obtain ⟨s₁, hs₁, hs₁Q, -⟩ := C.exists_two
  obtain ⟨hs₂, hs₂Q⟩ := C.conj_mem_R1 hxL1 hs₁ hs₁Q
  obtain ⟨hs₃, hs₃Q⟩ := C.conj_mem_R1 hxL1 hs₂ hs₂Q
  have h12 := hxs _ hs₁ hs₁Q
  have h23 := hxs _ hs₂ hs₂Q
  have h31 := hxs _ hs₃ hs₃Q
  have hx31 : x * (x * (x * s₁ * x⁻¹) * x⁻¹) * x⁻¹ = s₁ := by
    calc x * (x * (x * s₁ * x⁻¹) * x⁻¹) * x⁻¹ = x ^ 3 * s₁ * (x ^ 3)⁻¹ := by
          rw [pow_three]; group
      _ = s₁ := by rw [hx3]; group
  rw [hx31] at h31
  have h13 : s₁⁻¹ * (x * (x * s₁ * x⁻¹) * x⁻¹) ∉ pCoreOf 2 (hz T V) := fun h =>
    h31 (by rw [show (x * (x * s₁ * x⁻¹) * x⁻¹)⁻¹ * s₁ =
      (s₁⁻¹ * (x * (x * s₁ * x⁻¹) * x⁻¹))⁻¹ by group]; exact inv_mem h)
  set s₂ := x * s₁ * x⁻¹ with hs₂def
  set s₃ := x * s₂ * x⁻¹ with hs₃def
  have hcap : ∀ {a b : G}, a ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) → a ∉ pCoreOf 2 (hz T V) →
      b ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) → b ∉ pCoreOf 2 (hz T V) →
      a⁻¹ * b ∉ pCoreOf 2 (hz T V) → ∀ y ∈ dS T V a, y ∈ dS T V b → y ∈ fsuV1 T V := by
    intro a b ha haQ hb hbQ hab y hya hyb
    have h1 := C.card_inf_dS ha haQ hb hbQ hab
    rw [C.card_sup_u0, h8] at h1
    have hle : fsuV1 T V ≤ dS T V a ⊓ dS T V b := le_inf le_sup_right le_sup_right
    have heq : dS T V a ⊓ dS T V b = fsuV1 T V := by
      refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
      rw [C.hF.card_V₁]
      omega
    rw [← heq]
    exact Subgroup.mem_inf.mpr ⟨hya, hyb⟩
  have hrep : ∀ {s : G}, s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) → s ∉ pCoreOf 2 (hz T V) →
      ∃ t ∈ u0 T V, v * t ∈ dS T V s := by
    intro s hs hsQ
    have hv' : v ∈ dS T V s ⊔ u0 T V := by
      rw [C.dS_sup_u0 hs hsQ]
      exact Subgroup.mem_sup_left hv
    obtain ⟨d, hd, t, ht, hdt⟩ := mem_sup_of_comm C.hUc (C.dS_le_U hs) hU0U hv'
    exact ⟨t⁻¹, inv_mem ht, by rw [hdt]; group; exact hd⟩
  obtain ⟨t₁, ht₁, hd₁⟩ := hrep hs₁ hs₁Q
  obtain ⟨t₂, ht₂, hd₂⟩ := hrep hs₂ hs₂Q
  obtain ⟨t₃, ht₃, hd₃⟩ := hrep hs₃ hs₃Q
  have hVinf : ∀ {s : G}, s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) →
      s ∉ pCoreOf 2 (hz T V) → ∀ y ∈ dS T V s, y ∈ V → y ∈ fsuV1 T V := by
    intro s hs hsQ y hy hyV
    rw [← C.dS_inf_V_of_eight h8 hs hsQ]
    exact Subgroup.mem_inf.mpr ⟨hy, hyV⟩
  have hnot : ∀ {s : G} (hs : s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
      (hsQ : s ∉ pCoreOf 2 (hz T V)) {t : G}, v * t ∈ dS T V s → t ∉ fsuV1 T V := by
    intro s hs hsQ t hd ht
    apply hvV1
    refine hVinf hs hsQ v ?_ hv
    rw [show v = (v * t) * t⁻¹ by group]
    exact mul_mem hd (Subgroup.mem_sup_right (inv_mem ht))
  have hdist : ∀ {a b : G} (ha : a ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
      (haQ : a ∉ pCoreOf 2 (hz T V)) (hb : b ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
      (hbQ : b ∉ pCoreOf 2 (hz T V)), a⁻¹ * b ∉ pCoreOf 2 (hz T V) → ∀ {t t' : G},
      t ∈ u0 T V → t' ∈ u0 T V → v * t ∈ dS T V a → v * t' ∈ dS T V b →
      t⁻¹ * t' ∉ fsuV1 T V := by
    intro a b ha haQ hb hbQ hab t t' ht ht' hda hdb htt
    apply hvV1
    have hmem : v * t' ∈ dS T V a := by
      rw [show v * t' = (v * t) * (t⁻¹ * t') by group]
      exact mul_mem hda (Subgroup.mem_sup_right htt)
    have h1 := hcap ha haQ hb hbQ hab _ hmem hdb
    have hvU0 : v ∈ u0 T V := by
      rw [show v = (v * t') * t'⁻¹ by group]
      exact mul_mem (hV1U0 h1) (inv_mem ht')
    rw [← inf_u0_eq C.hyp C.hMod C.h63 C.hF]
    exact Subgroup.mem_inf.mpr ⟨hv, hvU0⟩
  have hd12 := hdist hs₁ hs₁Q hs₂ hs₂Q h12 ht₁ ht₂ hd₁ hd₂
  have hd23 := hdist hs₂ hs₂Q hs₃ hs₃Q h23 ht₂ ht₃ hd₂ hd₃
  have hd13 := hdist hs₁ hs₁Q hs₃ hs₃Q h13 ht₁ ht₃ hd₁ hd₃
  set N := (fsuV1 T V).subgroupOf (u0 T V) with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := C.hUc g (hU0U g.2) n (hU0U n.2)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [this, mul_inv_cancel_right]
    exact hn
  have : Fintype (↥(u0 T V) ⧸ N) := Fintype.ofFinite _
  have hcardN : Nat.card (↥(u0 T V) ⧸ N) = 4 := by
    rw [← Subgroup.index_eq_card]
    have := Subgroup.relIndex_mul_card (fsuV1 T V) (u0 T V)
    rw [inf_eq_left.mpr hV1U0, C.hF.card_V₁, h8] at this
    show (fsuV1 T V).relIndex (u0 T V) = 4
    omega
  set π := QuotientGroup.mk' N with hπ
  have hπeq : ∀ a b : ↥(u0 T V), π a = π b ↔ (a : G)⁻¹ * b ∈ fsuV1 T V := fun a b => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simp
  have hπ1 : ∀ a : ↥(u0 T V), π a = 1 ↔ (a : G) ∈ fsuV1 T V := fun a => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hne1 : ∀ {t : G} (ht : t ∈ u0 T V), t ∉ fsuV1 T V → π ⟨t, ht⟩ ≠ 1 :=
    fun ht hn h => hn ((hπ1 _).mp h)
  have hne : ∀ {t t' : G} (ht : t ∈ u0 T V) (ht' : t' ∈ u0 T V), t⁻¹ * t' ∉ fsuV1 T V →
      π ⟨t, ht⟩ ≠ π ⟨t', ht'⟩ := fun ht ht' hn h => hn ((hπeq _ _).mp h)
  have huniv : ({1, π ⟨t₁, ht₁⟩, π ⟨t₂, ht₂⟩, π ⟨t₃, ht₃⟩} : Finset (↥(u0 T V) ⧸ N)) =
      Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_pair (hne ht₂ ht₃ hd23), ← Nat.card_eq_fintype_card, hcardN]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hne ht₁ ht₂ hd12, hne ht₁ ht₃ hd13⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun e => hne1 ht₁ (hnot hs₁ hs₁Q hd₁) e.symm,
        fun e => hne1 ht₂ (hnot hs₂ hs₂Q hd₂) e.symm, fun e => hne1 ht₃ (hnot hs₃ hs₃Q hd₃) e.symm⟩
  have hmem : π ⟨u₀, hu₀⟩ ∈ ({1, π ⟨t₁, ht₁⟩, π ⟨t₂, ht₂⟩, π ⟨t₃, ht₃⟩} :
      Finset (↥(u0 T V) ⧸ N)) := by
    rw [huniv]
    exact Finset.mem_univ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
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
  rcases hmem with h | h | h | h
  · exact absurd h (hne1 hu₀ hu₀V1)
  · exact hfin hs₁ hs₁Q hd₁ ((hπeq _ _).mp h.symm)
  · exact hfin hs₂ hs₂Q hd₂ ((hπeq _ _).mp h.symm)
  · exact hfin hs₃ hs₃Q hd₃ ((hπeq _ _).mp h.symm)

end Ctx764

end CFSG.Quasithin.H13.L32A
