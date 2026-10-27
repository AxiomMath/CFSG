module

public import CFSG.Quasithin.EmptyFaithful.S153G93DSplit
public import CFSG.Quasithin.EmptyFaithful.S153E58In

public section

namespace CFSG.Quasithin

namespace S153G93D

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native
open scoped commutatorElement

section General

theorem nonab_of_quasisimple {Q : Type*} [Group Q] (h : CFSG.IsQuasisimple Q) :
    ∃ x y : Q, x * y ≠ y * x := by
  obtain ⟨-, -, a, b, hab⟩ := h
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨a, b, fun h => hab ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]

theorem isSimpleGroup_of_quasisimple_center {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q)
    (hZ : Subgroup.center Q = ⊥) : IsSimpleGroup Q := by
  have := hQ.2.1
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup

theorem center_eq_bot_of_simple {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (h : ∃ x y : Q, x * y ≠ y * x) : Subgroup.center Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h0 | h0
  · exact h0
  · exfalso
    obtain ⟨x, y, hxy⟩ := h
    have hx : x ∈ Subgroup.center Q := by rw [h0]; exact Subgroup.mem_top x
    exact hxy ((Subgroup.mem_center_iff.mp hx y).symm)

theorem mem_sup_iff_mul {G : Type*} [Group G] {K T : Subgroup G}
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) {x : G} :
    x ∈ K ⊔ T ↔ ∃ k ∈ K, ∃ t ∈ T, x = k * t := by
  constructor
  · intro hx
    let Q : Subgroup G :=
      { carrier := {x | ∃ k ∈ K, ∃ t ∈ T, x = k * t}
        one_mem' := ⟨1, K.one_mem, 1, T.one_mem, by simp⟩
        mul_mem' := by
          rintro _ _ ⟨k₁, hk₁, t₁, ht₁, rfl⟩ ⟨k₂, hk₂, t₂, ht₂, rfl⟩
          have h1 : t₁ * k₂ * t₁⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hTK ht₁) k₂).mp hk₂
          exact ⟨k₁ * (t₁ * k₂ * t₁⁻¹), K.mul_mem hk₁ h1, t₁ * t₂, T.mul_mem ht₁ ht₂, by group⟩
        inv_mem' := by
          rintro _ ⟨k, hk, t, ht, rfl⟩
          have h1 : t⁻¹ * k⁻¹ * t⁻¹⁻¹ ∈ K :=
            (Subgroup.mem_normalizer_iff.mp (hTK (T.inv_mem ht)) k⁻¹).mp (K.inv_mem hk)
          exact ⟨t⁻¹ * k⁻¹ * t⁻¹⁻¹, h1, t⁻¹, T.inv_mem ht, by group⟩ }
    have hle : K ⊔ T ≤ Q := sup_le (fun k hk => ⟨k, hk, 1, T.one_mem, by simp⟩)
      (fun t ht => ⟨1, K.one_mem, t, ht, by simp⟩)
    exact hle hx
  · rintro ⟨k, hk, t, ht, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right ht)

theorem exists_pow_mem_of_sup {G : Type*} [Group G] {K T : Subgroup G} (hT : IsPGroup 2 T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) :
    ∀ x ∈ K ⊔ T, ∃ e : ℕ, x ^ 2 ^ e ∈ K := by
  intro x hx
  obtain ⟨k, hk, t, ht, rfl⟩ := (mem_sup_iff_mul hTK).mp hx
  have hYn : K ⊔ T ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hTK
  have hnormK : (K.subgroupOf (K ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hYn
  obtain ⟨e, he⟩ := hT ⟨t, ht⟩
  refine ⟨e, ?_⟩
  let φ : ↥(K ⊔ T) →* ↥(K ⊔ T) ⧸ K.subgroupOf (K ⊔ T) := QuotientGroup.mk' _
  let xk : ↥(K ⊔ T) := ⟨k, Subgroup.mem_sup_left hk⟩
  let xt : ↥(K ⊔ T) := ⟨t, Subgroup.mem_sup_right ht⟩
  have hxk : φ xk = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (by rw [Subgroup.mem_subgroupOf]; exact hk)
  have hxt : xt ^ 2 ^ e = 1 := Subtype.ext (by simpa using congrArg Subtype.val he)
  have h1 : φ ((xk * xt) ^ 2 ^ e) = 1 := by
    rw [map_pow, map_mul, hxk, one_mul, ← map_pow, hxt, map_one]
  have h2 := (QuotientGroup.eq_one_iff _).mp h1
  rw [Subgroup.mem_subgroupOf] at h2
  simpa using h2

end General

section QLevel

variable {G : Type} [Group G] {Γ K : Subgroup G}

theorem minNormal_subgroupOf (hK : IsMinNormalIn Γ K)
    (hnc : ¬ ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) :
    (K.subgroupOf Γ).Normal ∧ K.subgroupOf Γ ≠ ⊥ ∧
      (∀ M : Subgroup ↥Γ, M.Normal → M ≤ K.subgroupOf Γ → M = ⊥ ∨ M = K.subgroupOf Γ) ∧
      ∃ x ∈ K.subgroupOf Γ, ∃ y ∈ K.subgroupOf Γ, x * y ≠ y * x := by
  obtain ⟨hKΓ, hKnorm, hK1, hKmin⟩ := hK
  have hKqmap : (K.subgroupOf Γ).map Γ.subtype = K := Subgroup.map_subgroupOf_eq_of_le hKΓ
  have hKqn : (K.subgroupOf Γ).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hKnorm g g.2 n hn
  refine ⟨hKqn, ?_, ?_, ?_⟩
  · intro h
    apply hK1
    rw [← hKqmap, h, Subgroup.map_bot]
  · intro M hM hMK
    have hMK' : M.map Γ.subtype ≤ K := hKqmap ▸ Subgroup.map_mono hMK
    have hnorm : ∀ h ∈ Γ, ∀ k ∈ M.map Γ.subtype, h * k * h⁻¹ ∈ M.map Γ.subtype := by
      rintro h hh _ ⟨m, hm, rfl⟩
      exact ⟨⟨h, hh⟩ * m * ⟨h, hh⟩⁻¹, hM.conj_mem m hm ⟨h, hh⟩, rfl⟩
    rcases hKmin _ hMK' hnorm with h | h
    · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective M Γ.subtype_injective).mp h)
    · refine Or.inr (Subgroup.map_injective Γ.subtype_injective ?_)
      rw [h, hKqmap]
  · by_contra hall
    push Not at hall
    apply hnc
    intro x hx y hy
    exact congrArg Subtype.val (hall ⟨x, hKΓ hx⟩ (Subgroup.mem_subgroupOf.mpr hx)
      ⟨y, hKΓ hy⟩ (Subgroup.mem_subgroupOf.mpr hy))

theorem pCore_eq_bot_of_pCoreOf (hO2 : pCoreOf 2 Γ = ⊥) : CFSG.pCore 2 ↥Γ = ⊥ := by
  have h := hO2
  unfold pCoreOf at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ Γ.subtype_injective).mp h

theorem exists_twoStruct_of_minNormal [Finite G] (h38 : A38ForSQTKCat) (hS : A38TypesSimple)
    (hq : G64.IsQuotientOfSQTKCat ↥Γ) (hO2 : pCoreOf 2 Γ = ⊥) (hK : IsMinNormalIn Γ K)
    (hnc : ¬ ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) :
    CFSG.IsComponent (K.subgroupOf Γ) ∨
      ∃ (N N' : Subgroup ↥Γ) (g : ↥Γ), TwoStruct (K.subgroupOf Γ) N N' g := by
  obtain ⟨hKqn, hKq1, hKqmin, hncq⟩ := minNormal_subgroupOf hK hnc
  exact exists_twoStruct h38 hS (S153G93.isQuotientOfSQTKTC_of_cat hq) (pCore_eq_bot_of_pCoreOf hO2)
    hKqn hKq1 hKqmin hncq

theorem simple_of_component (hK : IsMinNormalIn Γ K) (hnc : ¬ ∀ x ∈ K, ∀ y ∈ K, x * y = y * x)
    (hc : CFSG.IsComponent (K.subgroupOf Γ)) : IsSimpleGroup ↥K ∧ CFSG.IsQuasisimple ↥K := by
  obtain ⟨hKqn, -, hKqmin, hncq⟩ := minNormal_subgroupOf hK hnc
  have hZ := inf_centralizer_eq_bot hKqn hKqmin hncq
  have hcenter : Subgroup.center ↥(K.subgroupOf Γ) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have h1 : (z : ↥Γ) ∈ K.subgroupOf Γ ⊓ Subgroup.centralizer (K.subgroupOf Γ : Set ↥Γ) := by
      refine ⟨z.2, ?_⟩
      show (z : ↥Γ) ∈ Subgroup.centralizer (K.subgroupOf Γ : Set ↥Γ)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have := Subgroup.mem_center_iff.mp hz ⟨y, hy⟩
      exact congrArg Subtype.val this
    rw [hZ, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  have e : ↥(K.subgroupOf Γ) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hK.1
  have hquasi : CFSG.IsQuasisimple ↥K := CFSG.LocalCores.isQuasisimple_of_mulEquiv e hc.1
  have hsimple : IsSimpleGroup ↥(K.subgroupOf Γ) := isSimpleGroup_of_quasisimple_center hc.1 hcenter
  exact ⟨e.symm.isSimpleGroup, hquasi⟩

end QLevel

end S153G93D

end CFSG.Quasithin
