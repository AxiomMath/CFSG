module

public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.Quasithin.F112Crit

open Subgroup
open scoped commutatorElement

variable {Γ : Type*} [Group Γ]

@[expose] noncomputable def conjGen (K : Subgroup Γ) (t : Γ) : Subgroup Γ :=
  closure {x | ∃ k ∈ K, x = k * t * k⁻¹}

@[expose] noncomputable def comGen (K : Subgroup Γ) (t : Γ) : Subgroup Γ :=
  closure {c | ∃ k ∈ K, c = k * t * k⁻¹ * t⁻¹}

variable {K : Subgroup Γ} {t : Γ}

theorem conj_mem_conjGen {k : Γ} (hk : k ∈ K) : k * t * k⁻¹ ∈ conjGen K t :=
  subset_closure ⟨k, hk, rfl⟩

theorem self_mem_conjGen : t ∈ conjGen K t := by
  have := conj_mem_conjGen (K := K) (t := t) K.one_mem
  simpa using this

theorem com_mem_comGen {k : Γ} (hk : k ∈ K) : k * t * k⁻¹ * t⁻¹ ∈ comGen K t :=
  subset_closure ⟨k, hk, rfl⟩

theorem comGen_le_conjGen : comGen K t ≤ conjGen K t := by
  refine (closure_le _).2 ?_
  rintro _ ⟨k, hk, rfl⟩
  exact mul_mem (conj_mem_conjGen hk) (inv_mem self_mem_conjGen)

theorem com_mem {k : Γ} (hk : k ∈ K) (hnorm : ∀ k ∈ K, t * k * t⁻¹ ∈ K) :
    k * t * k⁻¹ * t⁻¹ ∈ K := by
  have := mul_mem hk (hnorm k⁻¹ (inv_mem hk))
  simpa [mul_assoc] using this

theorem comGen_le (hnorm : ∀ k ∈ K, t * k * t⁻¹ ∈ K) : comGen K t ≤ K := by
  refine (closure_le _).2 ?_
  rintro _ ⟨k, hk, rfl⟩
  exact com_mem hk hnorm

theorem conj_mem_comGen {k' : Γ} (hk' : k' ∈ K) {y : Γ} (hy : y ∈ comGen K t) :
    k' * y * k'⁻¹ ∈ comGen K t := by
  induction hy using closure_induction with
  | mem c hc =>
    obtain ⟨k, hk, rfl⟩ := hc
    have h1 := com_mem_comGen (t := t) (K.mul_mem hk' hk)
    have h2 := com_mem_comGen (t := t) hk'
    have := mul_mem h1 (inv_mem h2)
    convert this using 1
    group
  | one => simp [one_mem]
  | mul x y _ _ hx hy =>
    have := mul_mem hx hy
    convert this using 1
    group
  | inv x _ hx =>
    have := inv_mem hx
    convert this using 1
    group

theorem normal_comGen : ((comGen K t).subgroupOf K).Normal := by
  constructor
  intro n hn g
  rw [mem_subgroupOf] at hn ⊢
  have := conj_mem_comGen (K := K) (t := t) g.2 hn
  simpa using this

theorem commute_of_comGen_le_center (hq : CFSG.IsQuasisimple ↥K) (ht2 : t * t = 1)
    (hnorm : ∀ k ∈ K, t * k * t⁻¹ ∈ K) (hc : (comGen K t).subgroupOf K ≤ center ↥K) :
    ∀ k ∈ K, k * t = t * k := by
  have hP : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hq.1
  have hYK := comGen_le hnorm
  have hcentral : ∀ y ∈ comGen K t, ∀ k ∈ K, y * k = k * y := by
    intro y hy k hk
    have hy' : (⟨y, hYK hy⟩ : ↥K) ∈ center ↥K := hc (mem_subgroupOf.mpr hy)
    have h := Subgroup.mem_center_iff.mp hy' ⟨k, hk⟩
    exact (congrArg Subtype.val h).symm
  have hzp : ∀ x ∈ zpowers t, x = 1 ∨ x = t := by
    intro x hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
    rcases Int.even_or_odd' n with ⟨m, rfl | rfl⟩
    · left
      rw [zpow_mul, zpow_two, ht2, one_zpow]
    · right
      rw [zpow_add_one, zpow_mul, zpow_two, ht2, one_zpow, one_mul]
  have hX : ⁅K, zpowers t⁆ ≤ comGen K t := by
    rw [commutator_le]
    intro k hk x hx
    rcases hzp x hx with rfl | rfl
    · simp [commutatorElement_def, one_mem]
    · rw [commutatorElement_def]
      exact com_mem_comGen hk
  have hdouble : ⁅⁅K, zpowers t⁆, K⁆ = ⊥ := by
    rw [eq_bot_iff, commutator_le]
    intro y hy k hk
    have hy' := hX hy
    rw [mem_bot, commutatorElement_def, hcentral y hy' k hk]
    group
  have hzero := CFSG.LocalAnalysis.ComponentInitial.perfect_double_commutator hP hdouble
  intro k hk
  have h1 : ⁅k, t⁆ ∈ (⊥ : Subgroup Γ) := hzero ▸ commutator_mem_commutator hk (mem_zpowers t)
  rw [mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

theorem le_comGen (hq : CFSG.IsQuasisimple ↥K) (ht2 : t * t = 1)
    (hnorm : ∀ k ∈ K, t * k * t⁻¹ ∈ K) (hnc : ∃ k ∈ K, k * t ≠ t * k) : K ≤ comGen K t := by
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hq
      (normal_comGen (K := K) (t := t)) with htop | hcen
  · intro k hk
    have : (⟨k, hk⟩ : ↥K) ∈ (comGen K t).subgroupOf K := by rw [htop]; exact mem_top _
    exact mem_subgroupOf.mp this
  · exfalso
    obtain ⟨k, hk, hne⟩ := hnc
    exact hne (commute_of_comGen_le_center hq ht2 hnorm hcen k hk)

theorem le_conjGen (hq : CFSG.IsQuasisimple ↥K) (ht2 : t * t = 1)
    (hnorm : ∀ k ∈ K, t * k * t⁻¹ ∈ K) (hnc : ∃ k ∈ K, k * t ≠ t * k) : K ≤ conjGen K t :=
  (le_comGen hq ht2 hnorm hnc).trans comGen_le_conjGen

theorem exists_not_commute (hq : CFSG.IsQuasisimple ↥K) (ht2 : t * t = 1)
    (hnorm : ∀ k ∈ K, t * k * t⁻¹ ∈ K) (hnc : ∃ k ∈ K, k * t ≠ t * k) :
    ∃ k ∈ K, ∃ k' ∈ K,
      (k * t * k⁻¹ * t⁻¹) * (k' * t * k'⁻¹ * t⁻¹) ≠ (k' * t * k'⁻¹ * t⁻¹) * (k * t * k⁻¹ * t⁻¹) := by
  by_contra hall
  push Not at hall
  have hK := le_comGen hq ht2 hnorm hnc
  have hcomm : ∀ x ∈ comGen K t, ∀ y ∈ comGen K t, x * y = y * x := by
    have hS : ∀ c ∈ {c | ∃ k ∈ K, c = k * t * k⁻¹ * t⁻¹}, ∀ c' ∈ {c | ∃ k ∈ K, c = k * t * k⁻¹ * t⁻¹},
        c * c' = c' * c := by
      rintro _ ⟨k, hk, rfl⟩ _ ⟨k', hk', rfl⟩
      exact hall k hk k' hk'
    have h1 : comGen K t ≤ centralizer (comGen K t : Set Γ) := by
      refine (closure_le _).2 fun c hc => ?_
      rw [SetLike.mem_coe, mem_centralizer_iff]
      intro y hy
      have hle : comGen K t ≤ centralizer ({c} : Set Γ) := by
        refine (closure_le _).2 fun c' hc' => ?_
        rw [SetLike.mem_coe, mem_centralizer_iff]
        intro s hs
        rw [Set.mem_singleton_iff] at hs
        rw [hs]
        exact hS c hc c' hc'
      have := hle hy
      rw [mem_centralizer_iff] at this
      exact (this c rfl).symm
    intro x hx y hy
    have := h1 hx
    rw [mem_centralizer_iff] at this
    exact (this y hy).symm
  obtain ⟨a, b, hab⟩ := hq.2.2
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  have := hcomm x.1 (hK x.2) y.1 (hK y.2)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext this

theorem conjGen_subset (ht2 : t * t = 1) (hnorm : ∀ k ∈ K, t * k * t⁻¹ ∈ K) :
    ∀ x ∈ conjGen K t, x ∈ K ∨ ∃ k ∈ K, x = k * t := by
  intro x hx
  induction hx using closure_induction with
  | mem y hy =>
    obtain ⟨k, hk, rfl⟩ := hy
    right
    refine ⟨k * t * k⁻¹ * t⁻¹, com_mem hk hnorm, ?_⟩
    group
  | one => left; exact K.one_mem
  | mul x y _ _ hx hy =>
    rcases hx with hx | ⟨k₁, hk₁, rfl⟩ <;> rcases hy with hy | ⟨k₂, hk₂, rfl⟩
    · left; exact K.mul_mem hx hy
    · right; exact ⟨x * k₂, K.mul_mem hx hk₂, by group⟩
    · right
      exact ⟨k₁ * (t * y * t⁻¹), K.mul_mem hk₁ (hnorm y hy), by group⟩
    · left
      have : k₁ * t * (k₂ * t) = k₁ * (t * k₂ * t⁻¹) * (t * t) := by group
      rw [this, ht2, mul_one]
      exact K.mul_mem hk₁ (hnorm k₂ hk₂)
  | inv x _ hx =>
    rcases hx with hx | ⟨k, hk, rfl⟩
    · left; exact K.inv_mem hx
    · right
      refine ⟨t * k⁻¹ * t⁻¹, hnorm k⁻¹ (K.inv_mem hk), ?_⟩
      have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
      calc (k * t)⁻¹ = t⁻¹ * k⁻¹ := mul_inv_rev _ _
        _ = t * k⁻¹ := by rw [hti]
        _ = t * k⁻¹ * t⁻¹ * t := by group

theorem index_subgroupOf_conjGen_le_two (ht2 : t * t = 1)
    (hnorm : ∀ k ∈ K, t * k * t⁻¹ ∈ K) :
    (K.subgroupOf (conjGen K t)).index ≤ 2 := by
  set X₀ := conjGen K t with hX₀
  let t' : ↥X₀ := ⟨t, self_mem_conjGen⟩
  have hsurj : Function.Surjective
      (fun b : Bool => (QuotientGroup.mk (if b then 1 else t') : ↥X₀ ⧸ K.subgroupOf X₀)) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      rcases conjGen_subset ht2 hnorm x.1 x.2 with hx | ⟨k, hk, hx⟩
      · refine ⟨true, ?_⟩
        simp only [if_true]
        rw [QuotientGroup.eq]
        simpa [mem_subgroupOf] using hx
      · refine ⟨false, ?_⟩
        simp only [Bool.false_eq_true, if_false]
        rw [QuotientGroup.eq, mem_subgroupOf]
        have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
        have e1 : ((t' ⁻¹ * x : ↥X₀) : Γ) = t⁻¹ * (k * t) := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv, hx]
        have e2 : ((t' ⁻¹ * x : ↥X₀) : Γ) = t * k * t⁻¹ := by
          rw [e1, hti]; group
        rw [e2]
        exact hnorm k hk
  calc (K.subgroupOf X₀).index = Nat.card (↥X₀ ⧸ K.subgroupOf X₀) := rfl
    _ ≤ Nat.card Bool := Nat.card_le_card_of_surjective _ hsurj
    _ = 2 := by simp

end CFSG.Quasithin.F112Crit
