module

public import CFSG.Quasithin.Background.F1Cartan

public section

namespace CFSG.Quasithin.SzN19

open scoped commutatorElement

section Basic

variable {Ω : Type*} [Group Ω]

@[expose] def cj (τ : Ω) (A : Subgroup Ω) : Subgroup Ω := A.map (MulAut.conj τ).toMonoidHom

theorem mem_cj {τ : Ω} {A : Subgroup Ω} {x : Ω} : x ∈ cj τ A ↔ τ⁻¹ * x * τ ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using ha
  · intro h
    exact ⟨τ⁻¹ * x * τ, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem cj_sup (τ : Ω) (A B : Subgroup Ω) : cj τ (A ⊔ B) = cj τ A ⊔ cj τ B := Subgroup.map_sup _ _ _

theorem cj_inf (τ : Ω) (A B : Subgroup Ω) : cj τ (A ⊓ B) = cj τ A ⊓ cj τ B :=
  Subgroup.map_inf _ _ _ (MulAut.conj τ).injective

theorem cj_eq_self {τ : Ω} {A : Subgroup Ω} (h : τ ∈ Subgroup.normalizer (A : Set Ω)) :
    cj τ A = A := by
  ext x
  rw [mem_cj]
  have := Subgroup.mem_normalizer_iff.1 (inv_mem h) x
  simpa using this.symm

theorem conj_mem_cj {τ : Ω} {A : Subgroup Ω} {a : Ω} (ha : a ∈ A) : τ * a * τ⁻¹ ∈ cj τ A :=
  ⟨a, ha, by simp [MulAut.conj_apply]⟩

theorem exists_mul_of_normalizes {A E : Subgroup Ω} (hE : E ≤ Subgroup.normalizer (A : Set Ω)) {g : Ω}
    (hg : g ∈ A ⊔ E) : ∃ a ∈ A, ∃ e ∈ E, g = a * e := by
  let S : Subgroup Ω :=
    { carrier := {g | ∃ a ∈ A, ∃ e ∈ E, g = a * e}
      one_mem' := ⟨1, A.one_mem, 1, E.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, e, he, rfl⟩ ⟨a', ha', e', he', rfl⟩
        have h1 : e * a' * e⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 (hE he) a').1 ha'
        refine ⟨a * (e * a' * e⁻¹), A.mul_mem ha h1, e * e', E.mul_mem he he', ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨a, ha, e, he, rfl⟩
        have h1 : e⁻¹ * a⁻¹ * e ∈ A := by
          have := (Subgroup.mem_normalizer_iff.1 (hE (E.inv_mem he)) a⁻¹).1 (A.inv_mem ha)
          simpa using this
        refine ⟨e⁻¹ * a⁻¹ * e, h1, e⁻¹, E.inv_mem he, ?_⟩
        group }
  have hle : A ⊔ E ≤ S := sup_le (fun a ha => ⟨a, ha, 1, E.one_mem, by simp⟩)
    (fun e he => ⟨1, A.one_mem, e, he, by simp⟩)
  exact hle hg

end Basic

section Swap

variable {Ω : Type*} [Group Ω] [Finite Ω]

omit [Finite Ω] in
theorem mem_normalizer_of_cj_eq {τ : Ω} {A : Subgroup Ω} (h : cj τ A = A) :
    τ ∈ Subgroup.normalizer (A : Set Ω) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : τ * x * τ⁻¹ ∈ cj τ A := ⟨x, hx, by simp [MulAut.conj_apply]⟩
    rwa [h] at this
  · intro hx
    rw [← h, mem_cj] at hx
    simpa [mul_assoc] using hx

theorem false_of_commuting_order_three {Y : Subgroup Ω} {a b : Ω} (ha : a ∈ Y) (hb : b ∈ Y)
    (ha3 : orderOf a = 3) (hb3 : orderOf b = 3) (hab : a * b = b * a)
    (hnot : b ∉ Subgroup.zpowers a)
    (hY3 : ∀ E : Subgroup Ω, E ≤ Y → IsPGroup 3 E → Nat.card E ≤ 3) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : IsPGroup 3 (Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha3]; norm_num)
  have hB : IsPGroup 3 (Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb3]; norm_num)
  have hcomm : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers b, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := hy
    exact (Commute.zpow_zpow (show Commute a b from hab) i j).eq
  have hAB : Subgroup.zpowers a ≤ Subgroup.normalizer (Subgroup.zpowers b : Set Ω) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hcomm x hx y hy, mul_inv_cancel_right]
      exact hy
    · intro hy
      have h3 := hcomm x⁻¹ (inv_mem hx) _ hy
      have h4 : x * y * x⁻¹ = y := by
        calc x * y * x⁻¹ = (x * y * x⁻¹) * x⁻¹ * x := by group
          _ = x⁻¹ * (x * y * x⁻¹) * x := by rw [h3]
          _ = y := by group
      rwa [h4] at hy
  have hE : IsPGroup 3 (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup Ω) :=
    IsPGroup.to_sup_of_normal_right' hA hB hAB
  have hEY : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ Y :=
    sup_le ((Subgroup.zpowers_le).2 ha) ((Subgroup.zpowers_le).2 hb)
  have hlt : Subgroup.zpowers a < Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
    refine lt_of_le_of_ne le_sup_left fun h => hnot ?_
    rw [h]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  have h1 := Subgroup.card_lt_of_lt hlt
  have h2 := hY3 _ hEY hE
  rw [Nat.card_zpowers, ha3] at h1
  omega

end Swap

section NotSwap

variable {Ω : Type*} [Group Ω]

theorem le_normalizer_of_commute {A B : Subgroup Ω} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    B ≤ Subgroup.normalizer (A : Set Ω) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ y ∈ B, ∀ a ∈ A, y * a * y⁻¹ = a := fun y hy a ha => by
    rw [← hc a ha y hy, mul_inv_cancel_right]
  intro h
  constructor
  · intro ha
    rw [key x hx h ha]
    exact ha
  · intro ha
    have h1 := key x⁻¹ (B.inv_mem hx) _ ha
    have h2 : h = x * h * x⁻¹ := by
      calc h = x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ := by group
        _ = x * h * x⁻¹ := h1
    rw [h2]
    exact ha

theorem isSolvable_proj {N₁ N₂ R₀ : Subgroup Ω} (hinf : N₁ ⊓ N₂ = ⊥)
    (hR₀ : R₀ ≤ Subgroup.normalizer (N₂ : Set Ω)) (hs : Group.IsSolvable ↥R₀) :
    Group.IsSolvable ↥((N₂ ⊔ R₀) ⊓ N₁) := by
  have hnorm : (N₂.subgroupOf (N₂ ⊔ R₀)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hR₀)
  have hq : Group.IsSolvable (↥(N₂ ⊔ R₀) ⧸ N₂.subgroupOf (N₂ ⊔ R₀)) := by
    refine Group.isSolvable_of_surjective
      (f := (QuotientGroup.mk' (N₂.subgroupOf (N₂ ⊔ R₀))).comp
        (Subgroup.inclusion (le_sup_right : R₀ ≤ N₂ ⊔ R₀))) ?_
    intro z
    induction z using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨a, ha, b, hb, hx⟩ := exists_mul_of_normalizes hR₀ x.2
      refine ⟨⟨b, hb⟩, ?_⟩
      show (QuotientGroup.mk (⟨b, Subgroup.mem_sup_right hb⟩ : ↥(N₂ ⊔ R₀)) :
          ↥(N₂ ⊔ R₀) ⧸ N₂.subgroupOf (N₂ ⊔ R₀)) = QuotientGroup.mk x
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have : (((⟨b, Subgroup.mem_sup_right hb⟩ : ↥(N₂ ⊔ R₀))⁻¹ * x : ↥(N₂ ⊔ R₀)) : Ω) =
          b⁻¹ * (a * b) := by
        simp [hx]
      rw [this]
      have := (Subgroup.mem_normalizer_iff.mp (hR₀ (R₀.inv_mem hb)) a).mp ha
      simpa [mul_assoc] using this
  refine Group.isSolvable_of_isSolvable_injective
    (f := (QuotientGroup.mk' (N₂.subgroupOf (N₂ ⊔ R₀))).comp
      (Subgroup.inclusion (inf_le_left : (N₂ ⊔ R₀) ⊓ N₁ ≤ N₂ ⊔ R₀))) ?_
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : ((Subgroup.inclusion (inf_le_left : (N₂ ⊔ R₀) ⊓ N₁ ≤ N₂ ⊔ R₀) x : ↥(N₂ ⊔ R₀)) : Ω) ∈ N₂ :=
    Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hx)
  have h2 : (x : Ω) ∈ N₁ ⊓ N₂ := ⟨x.2.2, h1⟩
  rw [hinf, Subgroup.mem_bot] at h2
  exact Subtype.ext h2

end NotSwap

section Main

variable {Ω : Type*} [Group Ω] [Finite Ω]

theorem not_swap {N₁ N₂ Y M T H : Subgroup Ω}
    (hc : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) (hinf : N₁ ⊓ N₂ = ⊥)
    (hns : ¬ Group.IsSolvable ↥N₁)
    (hN₁H : N₁ ≤ H) (hN₂H : N₂ ≤ H) (hTH : T ≤ H)
    (hperm : ∀ t ∈ T, (cj t N₁ = N₁ ∧ cj t N₂ = N₂) ∨ (cj t N₁ = N₂ ∧ cj t N₂ = N₁))
    (hT : IsPGroup 2 T) (hTY : T ≤ Subgroup.normalizer (Y : Set Ω))
    (hY : Group.IsSolvable ↥Y) (hYX : Y ≤ N₁ ⊔ N₂)
    (hmin : ∀ K : Subgroup Ω, Y ⊔ T ≤ K → K ≤ H → ¬ N₁ ≤ K → K ≤ M)
    (hθ : ∀ x ∈ M, orderOf x = 3 → x ∈ Y)
    (hY3 : ∀ E : Subgroup Ω, E ≤ Y → IsPGroup 3 E → Nat.card E ≤ 3)
    (hex : ∃ y ∈ Y, orderOf y = 3) :
    ∀ t ∈ T, cj t N₁ = N₁ := by
  classical
  intro t₀ ht₀
  by_contra hswap
  obtain ⟨hs1, hs2⟩ := (hperm t₀ ht₀).resolve_left fun h => hswap h.1
  have hc' : ∀ a ∈ N₂, ∀ b ∈ N₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have hbot : ∀ x, x ∈ N₁ → x ∈ N₂ → x = 1 := fun x h1 h2 => by
    have : x ∈ N₁ ⊓ N₂ := ⟨h1, h2⟩
    rw [hinf, Subgroup.mem_bot] at this
    exact this
  have hN₁n : N₁ ≤ Subgroup.normalizer (N₂ : Set Ω) := le_normalizer_of_commute hc'
  have hXn₂ : N₁ ⊔ N₂ ≤ Subgroup.normalizer (N₂ : Set Ω) := sup_le hN₁n Subgroup.le_normalizer
  have hRs : Group.IsSolvable ↥(Y ⊔ T) :=
    F1.isSolvable_sup_of_le_normalizer hY (F1.isSolvable_of_isPGroup_two hT) hTY
  have hR₀s : Group.IsSolvable ↥((Y ⊔ T) ⊓ (N₁ ⊔ N₂)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (inf_le_left : (Y ⊔ T) ⊓ (N₁ ⊔ N₂) ≤ Y ⊔ T))
      (Subgroup.inclusion_injective _)
  have hR₀n : (Y ⊔ T) ⊓ (N₁ ⊔ N₂) ≤ Subgroup.normalizer (N₂ : Set Ω) := inf_le_right.trans hXn₂
  have hP₁s : Group.IsSolvable ↥((N₂ ⊔ (Y ⊔ T) ⊓ (N₁ ⊔ N₂)) ⊓ N₁) := isSolvable_proj hinf hR₀n hR₀s
  have hXcj : ∀ t ∈ T, cj t (N₁ ⊔ N₂) = N₁ ⊔ N₂ := by
    intro t ht
    rcases hperm t ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [cj_sup, h1, h2]
    · rw [cj_sup, h1, h2, sup_comm]
  have hRcj : ∀ t ∈ T, cj t (Y ⊔ T) = Y ⊔ T := fun t ht =>
    cj_eq_self (Subgroup.le_normalizer (Subgroup.mem_sup_right ht))
  have hR₀cj : ∀ t ∈ T, cj t ((Y ⊔ T) ⊓ (N₁ ⊔ N₂)) = (Y ⊔ T) ⊓ (N₁ ⊔ N₂) := by
    intro t ht
    rw [cj_inf, hRcj t ht, hXcj t ht]
  set R₀ : Subgroup Ω := (Y ⊔ T) ⊓ (N₁ ⊔ N₂) with hR₀
  set P₁ : Subgroup Ω := (N₂ ⊔ R₀) ⊓ N₁ with hP₁
  set P₂ : Subgroup Ω := (N₁ ⊔ R₀) ⊓ N₂ with hP₂
  have hP : ∀ t ∈ T, cj t (P₁ ⊔ P₂) = P₁ ⊔ P₂ := by
    intro t ht
    rcases hperm t ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 : cj t P₁ = P₁ := by rw [hP₁, cj_inf, cj_sup, h1, h2, hR₀cj t ht]
      have e2 : cj t P₂ = P₂ := by rw [hP₂, cj_inf, cj_sup, h1, h2, hR₀cj t ht]
      rw [cj_sup, e1, e2]
    · have e1 : cj t P₁ = P₂ := by rw [hP₁, hP₂, cj_inf, cj_sup, h1, h2, hR₀cj t ht]
      have e2 : cj t P₂ = P₁ := by rw [hP₂, hP₁, cj_inf, cj_sup, h1, h2, hR₀cj t ht]
      rw [cj_sup, e1, e2, sup_comm]
  have hTn : T ≤ Subgroup.normalizer ((P₁ ⊔ P₂ : Subgroup Ω) : Set Ω) := fun t ht =>
    mem_normalizer_of_cj_eq (hP t ht)
  have hdec : ∀ r ∈ R₀, ∃ a ∈ P₁, ∃ b ∈ P₂, r = a * b := by
    intro r hr
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_normalizes (le_normalizer_of_commute hc) hr.2
    refine ⟨a, ⟨?_, ha⟩, b, ⟨?_, hb⟩, rfl⟩
    · have := (N₂ ⊔ R₀).mul_mem (Subgroup.mem_sup_right hr) ((N₂ ⊔ R₀).inv_mem (Subgroup.mem_sup_left hb))
      simpa using this
    · have := (N₁ ⊔ R₀).mul_mem ((N₁ ⊔ R₀).inv_mem (Subgroup.mem_sup_left ha)) (Subgroup.mem_sup_right hr)
      simpa using this
  have hcP : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a := fun a ha b hb => hc a ha.2 b hb.2
  have hP₂n : P₂ ≤ Subgroup.normalizer (P₁ : Set Ω) := le_normalizer_of_commute hcP
  have hYR₀ : Y ≤ R₀ := le_inf le_sup_left hYX
  have hR₀le : R₀ ≤ P₁ ⊔ P₂ := fun r hr => by
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec r hr
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)
  set K : Subgroup Ω := (P₁ ⊔ P₂) ⊔ T with hK
  have hYK : Y ⊔ T ≤ K := sup_le (hYR₀.trans (hR₀le.trans le_sup_left)) le_sup_right
  have hKH : K ≤ H :=
    sup_le (sup_le (inf_le_right.trans hN₁H) (inf_le_right.trans hN₂H)) hTH
  have hnot : ¬ N₁ ≤ K := by
    intro hle
    have hP₁N : N₁ ≤ P₁ := by
      intro a ha
      obtain ⟨p, hp, t, ht, hpt⟩ := exists_mul_of_normalizes hTn (hle ha)
      have htX : t ∈ N₁ ⊔ N₂ := by
        have h1 : p ∈ N₁ ⊔ N₂ :=
          (sup_le_sup (inf_le_right : P₁ ≤ N₁) (inf_le_right : P₂ ≤ N₂)) hp
        have h2 : a ∈ N₁ ⊔ N₂ := Subgroup.mem_sup_left ha
        have : t = p⁻¹ * a := by rw [hpt]; group
        rw [this]
        exact (N₁ ⊔ N₂).mul_mem ((N₁ ⊔ N₂).inv_mem h1) h2
      have htR₀ : t ∈ R₀ := ⟨Subgroup.mem_sup_right ht, htX⟩
      have hap : a ∈ P₁ ⊔ P₂ := by
        rw [hpt]
        exact Subgroup.mul_mem _ hp (hR₀le htR₀)
      obtain ⟨p₁, hp₁, p₂, hp₂, hpp⟩ := exists_mul_of_normalizes hP₂n hap
      have h3 : p₂ ∈ N₁ := by
        have : p₂ = p₁⁻¹ * a := by rw [hpp]; group
        rw [this]
        exact N₁.mul_mem (N₁.inv_mem hp₁.2) ha
      have h4 : p₂ = 1 := hbot p₂ h3 hp₂.2
      rw [hpp, h4, mul_one]
      exact hp₁
    exact hns (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hP₁N)
      (Subgroup.inclusion_injective _))
  have hKM : K ≤ M := hmin K hYK hKH hnot
  obtain ⟨y, hyY, hy3⟩ := hex
  obtain ⟨a, haP, b, hbP, hyab⟩ := hdec y (hYR₀ hyY)
  have haM : a ∈ M := hKM (Subgroup.mem_sup_left (Subgroup.mem_sup_left haP))
  have hbM : b ∈ M := hKM (Subgroup.mem_sup_left (Subgroup.mem_sup_right hbP))
  have haN : a ∈ N₁ := haP.2
  have hbN : b ∈ N₂ := hbP.2
  have hab : a * b = b * a := hc a haN b hbN
  have hy1 : (a * b) ^ 3 = 1 := by
    rw [← hyab, ← hy3]
    exact pow_orderOf_eq_one y
  have hpow : a ^ 3 * b ^ 3 = 1 := by
    rw [← Commute.mul_pow (show Commute a b from hab)]
    exact hy1
  have ha3 : a ^ 3 = 1 := hbot _ (N₁.pow_mem haN 3) (by
    have : a ^ 3 = (b ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left hpow
    rw [this]
    exact N₂.inv_mem (N₂.pow_mem hbN 3))
  have hb3 : b ^ 3 = 1 := by
    rw [ha3, one_mul] at hpow
    exact hpow
  have hF3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hordconj : ∀ z : Ω, orderOf (t₀ * z * t₀⁻¹) = orderOf z := fun z => by
    have := orderOf_injective (MulAut.conj t₀).toMonoidHom (MulAut.conj t₀).injective z
    simpa [MulAut.conj_apply] using this
  by_cases ha1 : a = 1
  ·
    have hbeq : y = b := by rw [hyab, ha1, one_mul]
    have hbo : orderOf b = 3 := hbeq ▸ hy3
    have hbY : b ∈ Y := hbeq ▸ hyY
    have hb'N₁ : t₀ * b * t₀⁻¹ ∈ N₁ := by
      have := conj_mem_cj (τ := t₀) hbN
      rwa [hs2] at this
    have hb'Y : t₀ * b * t₀⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hTY ht₀) b).mp hbY
    refine false_of_commuting_order_three hb'Y hbY ((hordconj b).trans hbo) hbo
      (hc _ hb'N₁ b hbN) (fun hmem => ?_) hY3
    have h1 : b ∈ N₁ := (Subgroup.zpowers_le.2 hb'N₁) hmem
    have := hbot b h1 hbN
    rw [this, orderOf_one] at hbo
    omega
  · by_cases hb1 : b = 1
    ·
      have haeq : y = a := by rw [hyab, hb1, mul_one]
      have hao : orderOf a = 3 := haeq ▸ hy3
      have haY : a ∈ Y := haeq ▸ hyY
      have ha'N₂ : t₀ * a * t₀⁻¹ ∈ N₂ := by
        have := conj_mem_cj (τ := t₀) haN
        rwa [hs1] at this
      have ha'Y : t₀ * a * t₀⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hTY ht₀) a).mp haY
      refine false_of_commuting_order_three haY ha'Y hao ((hordconj a).trans hao)
        (hc a haN _ ha'N₂) (fun hmem => ?_) hY3
      have h1 : t₀ * a * t₀⁻¹ ∈ N₁ := (Subgroup.zpowers_le.2 haN) hmem
      have := hbot _ h1 ha'N₂
      have ho : orderOf (t₀ * a * t₀⁻¹) = 3 := (hordconj a).trans hao
      rw [this, orderOf_one] at ho
      omega
    · have hao : orderOf a = 3 := orderOf_eq_prime ha3 ha1
      have hbo : orderOf b = 3 := orderOf_eq_prime hb3 hb1
      refine false_of_commuting_order_three (hθ a haM hao) (hθ b hbM hbo) hao hbo hab
        (fun hmem => ?_) hY3
      have h1 : b ∈ N₁ := (Subgroup.zpowers_le.2 haN) hmem
      exact hb1 (hbot b h1 hbN)

end Main

end CFSG.Quasithin.SzN19
