module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31WD
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WA

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.P31X

variable {Y : Type*} [Group Y]

@[expose, instance_reducible] def conjAct (P A : Subgroup Y) (h : P ≤ Subgroup.normalizer (A : Set Y)) :
    MulAction ↥P ↥A where
  smul p a := ⟨p * a * p⁻¹, (Subgroup.mem_normalizer_iff.1 (h p.2) a).1 a.2⟩
  one_smul a := Subtype.ext (by
    show ((1 : ↥P) : Y) * a * ((1 : ↥P) : Y)⁻¹ = a
    simp)
  mul_smul p q a := Subtype.ext (by
    show ((p * q : ↥P) : Y) * a * ((p * q : ↥P) : Y)⁻¹ = p * (q * a * (q : Y)⁻¹) * (p : Y)⁻¹
    simp [mul_assoc])

theorem exists_centralizes_order_three [Finite Y] {P A : Subgroup Y} (hP : IsPGroup 3 P)
    (h : P ≤ Subgroup.normalizer (A : Set Y)) (h3 : 3 ∣ Nat.card A) :
    ∃ y ∈ A, orderOf y = 3 ∧ ∀ x ∈ P, x * y * x⁻¹ = y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI := conjAct P A h
  have hmod := hP.card_modEq_card_fixedPoints ↥A
  have hfix : Nat.card (MulAction.fixedPoints ↥P ↥A) =
      Nat.card ↥(A ⊓ Subgroup.centralizer (P : Set Y)) := by
    refine Nat.card_congr
      { toFun := fun a => ⟨a.1.1, a.1.2, ?_⟩
        invFun := fun c => ⟨⟨c.1, c.2.1⟩, ?_⟩
        left_inv := fun a => rfl
        right_inv := fun c => rfl }
    · show (a.1.1 : Y) ∈ Subgroup.centralizer (P : Set Y)
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have h1 := MulAction.mem_fixedPoints.1 a.2 ⟨g, hg⟩
      have h2 : (g * a.1.1 * g⁻¹ : Y) = a.1.1 := congrArg (fun z : ↥A => (z : Y)) h1
      calc g * a.1.1 = (g * a.1.1 * g⁻¹) * g := by group
        _ = a.1.1 * g := by rw [h2]
    · rw [MulAction.mem_fixedPoints]
      intro p
      apply Subtype.ext
      have h1 := Subgroup.mem_centralizer_iff.1 c.2.2 p p.2
      show (p : Y) * c.1 * (p : Y)⁻¹ = c.1
      calc (p : Y) * c.1 * (p : Y)⁻¹ = c.1 * (p : Y) * (p : Y)⁻¹ := by rw [h1]
        _ = c.1 := by group
  rw [hfix] at hmod
  have h3' : 3 ∣ Nat.card ↥(A ⊓ Subgroup.centralizer (P : Set Y)) := by
    have := hmod.symm.trans (Nat.modEq_zero_iff_dvd.2 h3)
    exact Nat.modEq_zero_iff_dvd.1 this
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(A ⊓ Subgroup.centralizer (P : Set Y))) 3 h3'
  refine ⟨(y : Y), (Subgroup.mem_inf.1 y.2).1, by rw [Subgroup.orderOf_coe, hy], fun x hx => ?_⟩
  have h1 := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 y.2).2 x hx
  calc x * (y : Y) * x⁻¹ = (y : Y) * x * x⁻¹ := by rw [h1]
    _ = (y : Y) := by group


theorem mem_sup_of_threeRank [Finite Y] (hR : P31D.ThreeRankLE2 Y) {X₁ X₂ : Subgroup Y}
    (hcomm : ∀ a ∈ X₁, ∀ b ∈ X₂, a * b = b * a) (hX : X₁ ⊓ X₂ = ⊥)
    (h₁ : 3 ∣ Nat.card X₁) (h₂ : 3 ∣ Nat.card X₂) {x : Y} (hx3 : x ^ 3 = 1)
    (hx₁ : x ∈ Subgroup.normalizer (X₁ : Set Y)) (hx₂ : x ∈ Subgroup.normalizer (X₂ : Set Y)) :
    x ∈ X₁ ⊔ X₂ := by
  by_contra hxs
  have hx1 : x ≠ 1 := fun h => hxs (h ▸ Subgroup.one_mem _)
  have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hP : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxord]; norm_num)
  obtain ⟨y₁, hy₁, hy₁o, hy₁c⟩ :=
    exists_centralizes_order_three hP (Subgroup.zpowers_le.2 hx₁) h₁
  obtain ⟨y₂, hy₂, hy₂o, hy₂c⟩ :=
    exists_centralizes_order_three hP (Subgroup.zpowers_le.2 hx₂) h₂
  have hc1 : x * y₁ = y₁ * x := by
    have h := hy₁c x (Subgroup.mem_zpowers x)
    calc x * y₁ = (x * y₁ * x⁻¹) * x := by group
      _ = y₁ * x := by rw [h]
  have hc2 : x * y₂ = y₂ * x := by
    have h := hy₂c x (Subgroup.mem_zpowers x)
    calc x * y₂ = (x * y₂ * x⁻¹) * x := by group
      _ = y₂ * x := by rw [h]
  have hc12 : y₁ * y₂ = y₂ * y₁ := hcomm y₁ hy₁ y₂ hy₂
  have hy₁3 : y₁ ^ 3 = 1 := by rw [← hy₁o]; exact pow_orderOf_eq_one y₁
  have hy₂3 : y₂ ^ 3 = 1 := by rw [← hy₂o]; exact pow_orderOf_eq_one y₂
  refine hR x y₁ y₂ hx3 hy₁3 hy₂3 hc1 hc2 hc12 ?_
  intro a b c habc
  have hmem : x ^ a ∈ X₁ ⊔ X₂ := by
    have e : x ^ a = (y₁ ^ b * y₂ ^ c)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← mul_assoc]; exact habc)
    rw [e]
    exact Subgroup.inv_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left (X₁.pow_mem hy₁ b))
      (Subgroup.mem_sup_right (X₂.pow_mem hy₂ c)))
  have ha : 3 ∣ a := by
    by_contra h3a
    apply hxs
    have hx3' : ∀ t : ℕ, (x ^ 3) ^ t = 1 := fun t => by rw [hx3, one_pow]
    have hmod : a % 3 = 1 ∨ a % 3 = 2 := by omega
    have hxa : x ^ a = x ^ (a % 3) := by
      conv_lhs => rw [← Nat.div_add_mod a 3, pow_add, pow_mul, hx3' (a / 3), one_mul]
    rcases hmod with h | h
    · rw [hxa, h, pow_one] at hmem
      exact hmem
    · rw [hxa, h] at hmem
      have : x = (x ^ 2)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one]; calc x * x ^ 2 = x ^ 3 := by group
          _ = 1 := hx3
      rw [this]
      exact Subgroup.inv_mem _ hmem
  have hxa1 : x ^ a = 1 := by
    obtain ⟨t, rfl⟩ := ha
    rw [pow_mul, hx3, one_pow]
  have hyy : y₁ ^ b * y₂ ^ c = 1 := by rw [hxa1, one_mul] at habc; exact habc
  have hy1b : y₁ ^ b = 1 := by
    have hmem' : y₁ ^ b ∈ X₁ ⊓ X₂ :=
      Subgroup.mem_inf.2 ⟨X₁.pow_mem hy₁ b, by
        rw [eq_inv_of_mul_eq_one_left hyy]; exact X₂.inv_mem (X₂.pow_mem hy₂ c)⟩
    rw [hX, Subgroup.mem_bot] at hmem'
    exact hmem'
  have hy2c : y₂ ^ c = 1 := by rw [hy1b, one_mul] at hyy; exact hyy
  refine ⟨ha, ?_, ?_⟩
  · have := orderOf_dvd_of_pow_eq_one hy1b
    rwa [hy₁o] at this
  · have := orderOf_dvd_of_pow_eq_one hy2c
    rwa [hy₂o] at this


theorem sup_le_normalizer_left {X₁ X₂ : Subgroup Y} (hcomm : ∀ a ∈ X₁, ∀ b ∈ X₂, a * b = b * a) :
    X₁ ⊔ X₂ ≤ Subgroup.normalizer (X₁ : Set Y) :=
  sup_le Subgroup.le_normalizer (P31A.le_normalizer_of_comm le_rfl hcomm)

theorem eq_or_commute_of_simple {K₀ W X : Subgroup Y} (hW : IsSimpleGroup ↥W)
    (hX : IsSimpleGroup ↥X) (hWK : W ≤ K₀) (hXK : X ≤ K₀)
    (hWn : K₀ ≤ Subgroup.normalizer (W : Set Y)) (hXn : K₀ ≤ Subgroup.normalizer (X : Set Y)) :
    W = X ∨ ∀ w ∈ W, ∀ x ∈ X, w * x = x * w := by
  haveI : (X.subgroupOf W).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hgX : (g : Y) ∈ Subgroup.normalizer (X : Set Y) := hXn (hWK g.2)
    have := (Subgroup.mem_normalizer_iff.1 hgX (n : Y)).1 hn
    simpa using this⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (X.subgroupOf W) with hbot | htop
  · right
    intro w hw x hx
    have h1 : w * x * w⁻¹ * x⁻¹ ∈ X ⊓ W := by
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · have hwX : w ∈ Subgroup.normalizer (X : Set Y) := hXn (hWK hw)
        have := (Subgroup.mem_normalizer_iff.1 hwX x).1 hx
        exact X.mul_mem (by simpa [mul_assoc] using this) (X.inv_mem hx)
      · have hxW : x ∈ Subgroup.normalizer (W : Set Y) := hWn (hXK hx)
        have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hxW) w).1 hw
        have h2 : w * (x * w⁻¹ * x⁻¹) = w * x * w⁻¹ * x⁻¹ := by group
        rw [← h2]
        refine W.mul_mem hw ?_
        have h3 := (Subgroup.mem_normalizer_iff.1 hxW w⁻¹).1 (W.inv_mem hw)
        simpa [mul_assoc] using h3
    have h2 : w * x * w⁻¹ * x⁻¹ ∈ X ⊓ W := h1
    have h3 : (⟨w * x * w⁻¹ * x⁻¹, (Subgroup.mem_inf.1 h2).2⟩ : ↥W) ∈ X.subgroupOf W :=
      Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.1 h2).1
    rw [hbot, Subgroup.mem_bot] at h3
    have h4 : w * x * w⁻¹ * x⁻¹ = 1 := congrArg Subtype.val h3
    calc w * x = (w * x * w⁻¹ * x⁻¹) * (x * w) := by group
      _ = x * w := by rw [h4, one_mul]
  · left
    have hWX : W ≤ X := fun w hw => by
      have : (⟨w, hw⟩ : ↥W) ∈ X.subgroupOf W := by rw [htop]; exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.1 this
    haveI : (W.subgroupOf X).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have hgW : (g : Y) ∈ Subgroup.normalizer (W : Set Y) := hWn (hXK g.2)
      have := (Subgroup.mem_normalizer_iff.1 hgW (n : Y)).1 hn
      simpa using this⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (W.subgroupOf X) with hb | ht
    · exfalso
      obtain ⟨a, b, hab⟩ := hW.exists_pair_ne
      apply hab
      have ha : (a : Y) ∈ X := hWX a.2
      have hmem : (⟨a, hWX a.2⟩ : ↥X) ∈ W.subgroupOf X := Subgroup.mem_subgroupOf.2 a.2
      have hmem' : (⟨b, hWX b.2⟩ : ↥X) ∈ W.subgroupOf X := Subgroup.mem_subgroupOf.2 b.2
      rw [hb, Subgroup.mem_bot] at hmem hmem'
      exact Subtype.ext (congrArg (fun z : ↥X => (z : Y)) (hmem.trans hmem'.symm))
    · refine le_antisymm hWX fun x hx => ?_
      have : (⟨x, hx⟩ : ↥X) ∈ W.subgroupOf X := by rw [ht]; exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.1 this


theorem eq_or_eq_of_simple_normal {X₁ X₂ W : Subgroup Y} (hX₁ : IsSimpleGroup ↥X₁)
    (hX₂ : IsSimpleGroup ↥X₂) (hW : IsSimpleGroup ↥W) (hnc : ¬ ∀ a b : ↥W, a * b = b * a)
    (hcomm : ∀ a ∈ X₁, ∀ b ∈ X₂, a * b = b * a) (hWK : W ≤ X₁ ⊔ X₂)
    (hWn : X₁ ⊔ X₂ ≤ Subgroup.normalizer (W : Set Y)) : W = X₁ ∨ W = X₂ := by
  have hN₁ : X₁ ⊔ X₂ ≤ Subgroup.normalizer (X₁ : Set Y) := sup_le_normalizer_left hcomm
  have hN₂ : X₁ ⊔ X₂ ≤ Subgroup.normalizer (X₂ : Set Y) := by
    rw [sup_comm]
    exact sup_le_normalizer_left (fun b hb a ha => (hcomm a ha b hb).symm)
  rcases eq_or_commute_of_simple hW hX₁ hWK le_sup_left hWn hN₁ with h1 | h1
  · exact Or.inl h1
  rcases eq_or_commute_of_simple hW hX₂ hWK le_sup_right hWn hN₂ with h2 | h2
  · exact Or.inr h2
  exfalso
  apply hnc
  intro a b
  have hsup : X₁ ⊔ X₂ ≤ Subgroup.centralizer (W : Set Y) := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact h1 w hw x hx
    · rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact h2 w hw x hx
  have hb : (b : Y) ∈ Subgroup.centralizer (W : Set Y) := hsup (hWK b.2)
  exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hb a a.2)

theorem isSimpleGroup_map_conj {W : Subgroup Y} (hW : IsSimpleGroup ↥W) (x : Y) :
    IsSimpleGroup ↥(W.map (MulAut.conj x).toMonoidHom) :=
  (W.equivMapOfInjective _ (MulAut.conj x).injective).symm.isSimpleGroup

theorem map_conj_pair {X₁ X₂ X : Subgroup Y} (hX₁ : IsSimpleGroup ↥X₁) (hX₂ : IsSimpleGroup ↥X₂)
    (hXs : IsSimpleGroup ↥X) (hXnc : ¬ ∀ a b : ↥X, a * b = b * a)
    (hcomm : ∀ a ∈ X₁, ∀ b ∈ X₂, a * b = b * a) {x : Y}
    (hx : x ∈ Subgroup.normalizer ((X₁ ⊔ X₂ : Subgroup Y) : Set Y)) (hXK : X ≤ X₁ ⊔ X₂)
    (hXn : X₁ ⊔ X₂ ≤ Subgroup.normalizer (X : Set Y)) :
    X.map (MulAut.conj x).toMonoidHom = X₁ ∨ X.map (MulAut.conj x).toMonoidHom = X₂ := by
  have h1 : X₁ ⊔ X₂ ≤ Subgroup.normalizer ((X.map (MulAut.conj x).toMonoidHom : Subgroup Y) : Set Y) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hk' : x⁻¹ * k * x ∈ X₁ ⊔ X₂ := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hx) k).1 hk
      simpa [mul_assoc] using this
    have h1 := Subgroup.mem_normalizer_iff_map_conj_eq.1 (hXn hk')
    calc (X.map (MulAut.conj x).toMonoidHom).map (MulAut.conj k).toMonoidHom
        = X.map ((MulAut.conj k).toMonoidHom.comp (MulAut.conj x).toMonoidHom) := by
          simp only [Subgroup.map_map]
      _ = X.map ((MulAut.conj x).toMonoidHom.comp (MulAut.conj (x⁻¹ * k * x)).toMonoidHom) := by
          congr 1
          ext y
          simp [MulAut.conj_apply, mul_assoc]
      _ = (X.map (MulAut.conj (x⁻¹ * k * x)).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
          rw [Subgroup.map_map]
      _ = X.map (MulAut.conj x).toMonoidHom :=
          congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) h1
  have h2 : X.map (MulAut.conj x).toMonoidHom ≤ X₁ ⊔ X₂ := by
    rintro _ ⟨s, hs, rfl⟩
    have := (Subgroup.mem_normalizer_iff.1 hx s).1 (hXK hs)
    simpa using this
  refine eq_or_eq_of_simple_normal hX₁ hX₂ (isSimpleGroup_map_conj hXs x) ?_ hcomm h2 h1
  intro hcomm'
  apply hXnc
  intro a b
  have h4 := congrArg Subtype.val (hcomm' ⟨x * (a : Y) * x⁻¹, a, a.2, rfl⟩ ⟨x * (b : Y) * x⁻¹, b, b.2, rfl⟩)
  apply Subtype.ext
  have e1 : x * ((a : Y) * b) * x⁻¹ = (x * (a : Y) * x⁻¹) * (x * (b : Y) * x⁻¹) := by group
  have e2 : x * ((b : Y) * a) * x⁻¹ = (x * (b : Y) * x⁻¹) * (x * (a : Y) * x⁻¹) := by group
  have h3 : x * ((a : Y) * b) * x⁻¹ = x * ((b : Y) * a) * x⁻¹ := by
    rw [e1, e2]
    exact h4
  have h5 := mul_left_cancel (mul_right_cancel h3)
  exact h5

theorem normalizer_left_of_odd {X₁ X₂ : Subgroup Y} (hX₁ : IsSimpleGroup ↥X₁)
    (hX₂ : IsSimpleGroup ↥X₂) (hnc₁ : ¬ ∀ a b : ↥X₁, a * b = b * a)
    (hnc₂ : ¬ ∀ a b : ↥X₂, a * b = b * a)
    (hcomm : ∀ a ∈ X₁, ∀ b ∈ X₂, a * b = b * a) (hX : X₁ ⊓ X₂ = ⊥)
    {x : Y} (hx : x ∈ Subgroup.normalizer ((X₁ ⊔ X₂ : Subgroup Y) : Set Y)) {n : ℕ}
    (hn : Odd n) (hxn : x ^ n = 1) : x ∈ Subgroup.normalizer (X₁ : Set Y) := by
  have hne : X₁ ≠ X₂ := by
    intro h
    obtain ⟨a, b, hab⟩ := hX₁.exists_pair_ne
    apply hab
    have ha : (a : Y) ∈ X₁ ⊓ X₂ := ⟨a.2, h ▸ a.2⟩
    have hb : (b : Y) ∈ X₁ ⊓ X₂ := ⟨b.2, h ▸ b.2⟩
    rw [hX] at ha hb
    exact Subtype.ext ((Subgroup.mem_bot.1 ha).trans (Subgroup.mem_bot.1 hb).symm)
  set c : Subgroup Y → Subgroup Y := fun S => S.map (MulAut.conj x).toMonoidHom with hc
  have hcinj : ∀ {S R : Subgroup Y}, c S = c R → S = R := fun h =>
    Subgroup.map_injective (f := (MulAut.conj x).toMonoidHom) (MulAut.conj x).injective h
  have hnorm : ∀ S : Subgroup Y, x ∈ Subgroup.normalizer (S : Set Y) ↔ c S = S := fun S =>
    Subgroup.mem_normalizer_iff_map_conj_eq
  have hpair : ∀ X : Subgroup Y, IsSimpleGroup ↥X → (¬ ∀ a b : ↥X, a * b = b * a) →
      X ≤ X₁ ⊔ X₂ → X₁ ⊔ X₂ ≤ Subgroup.normalizer (X : Set Y) → c X = X₁ ∨ c X = X₂ :=
    fun X hXs hXnc hXK hXn => map_conj_pair hX₁ hX₂ hXs hXnc hcomm hx hXK hXn
  have hN₁ : X₁ ⊔ X₂ ≤ Subgroup.normalizer (X₁ : Set Y) := sup_le_normalizer_left hcomm
  have hN₂ : X₁ ⊔ X₂ ≤ Subgroup.normalizer (X₂ : Set Y) := by
    rw [sup_comm]
    exact sup_le_normalizer_left (fun b hb a ha => (hcomm a ha b hb).symm)
  by_contra hxN
  have h1 : c X₁ = X₂ := by
    rcases hpair X₁ hX₁ hnc₁ le_sup_left hN₁ with h | h
    · exact absurd ((hnorm X₁).2 h) hxN
    · exact h
  have h2 : c X₂ = X₁ := by
    rcases hpair X₂ hX₂ hnc₂ le_sup_right hN₂ with h | h
    · exact h
    · exact absurd (hcinj (h.trans h1.symm)).symm hne
  have hcc : c (c X₁) = X₁ := by rw [h1, h2]
  have hx2 : x * x ∈ Subgroup.normalizer (X₁ : Set Y) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    calc X₁.map (MulAut.conj (x * x)).toMonoidHom = c (c X₁) := by
          simp only [hc, Subgroup.map_map]
          congr 1
          ext y
          simp [MulAut.conj_apply, mul_assoc]
      _ = X₁ := hcc
  obtain ⟨m, rfl⟩ := hn
  apply hxN
  have hxm : x = (x * x) ^ (m + 1) := by
    have h3 : x ^ (2 * m + 1) = 1 := hxn
    calc x = x ^ (2 * m + 1) * x := by rw [h3, one_mul]
      _ = x ^ (2 * m + 1 + 1) := (pow_succ x _).symm
      _ = (x * x) ^ (m + 1) := by
        rw [← pow_two, ← pow_mul]
        congr 1
  rw [hxm]
  exact Subgroup.pow_mem _ hx2 _


theorem mem_sup_of_order_three [Finite Y] (hR : P31D.ThreeRankLE2 Y) {X₁ X₂ : Subgroup Y}
    (hX₁ : IsSimpleGroup ↥X₁) (hX₂ : IsSimpleGroup ↥X₂) (hnc₁ : ¬ ∀ a b : ↥X₁, a * b = b * a)
    (hnc₂ : ¬ ∀ a b : ↥X₂, a * b = b * a) (hcomm : ∀ a ∈ X₁, ∀ b ∈ X₂, a * b = b * a)
    (hX : X₁ ⊓ X₂ = ⊥) (h₁ : 3 ∣ Nat.card X₁) (h₂ : 3 ∣ Nat.card X₂) {x : Y}
    (hx : x ∈ Subgroup.normalizer ((X₁ ⊔ X₂ : Subgroup Y) : Set Y)) (hx3 : x ^ 3 = 1) :
    x ∈ X₁ ⊔ X₂ := by
  have hcomm' : ∀ a ∈ X₂, ∀ b ∈ X₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  refine mem_sup_of_threeRank hR hcomm hX h₁ h₂ hx3
    (normalizer_left_of_odd hX₁ hX₂ hnc₁ hnc₂ hcomm hX hx (n := 3) ⟨1, rfl⟩ hx3)
    (normalizer_left_of_odd hX₂ hX₁ hnc₂ hnc₁ hcomm' (by rwa [inf_comm]) ?_ (n := 3) ⟨1, rfl⟩ hx3)
  rwa [sup_comm]

end CFSG.Quasithin.H13.P31X
