module

public import CFSG.Quasithin.Background.E6Eighteen
public import CFSG.Quasithin.Background.GoldschmidtTDE68Seven

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique

section Nine

theorem mul_pow_three_of_commute_comm {Y : Type*} [Group Y] {x y : Y}
    (hx : Commute (x * y * x⁻¹ * y⁻¹) x)
    (hy : Commute (x * y * x⁻¹ * y⁻¹) y) (ht : (x * y * x⁻¹ * y⁻¹) ^ 3 = 1) :
    (x * y) ^ 3 = x ^ 3 * y ^ 3 := by
  set t := x * y * x⁻¹ * y⁻¹ with htdef
  have e1 : y * x = t⁻¹ * (x * y) := by rw [htdef]; group
  have hx' : ∀ w : Y, x * (t⁻¹ * w) = t⁻¹ * (x * w) := fun w => by
    rw [← mul_assoc, ← mul_assoc, (hx.inv_left).eq]
  have hy' : ∀ w : Y, y * (t⁻¹ * w) = t⁻¹ * (y * w) := fun w => by
    rw [← mul_assoc, ← mul_assoc, (hy.inv_left).eq]
  have e1' : ∀ w : Y, y * (x * w) = t⁻¹ * (x * (y * w)) := fun w => by
    rw [← mul_assoc, e1, mul_assoc, mul_assoc]
  have h3 : (x * y) ^ 3 = x * (y * (x * (y * (x * y)))) := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have h4 : x ^ 3 * y ^ 3 = x * (x * (x * (y * (y * y)))) := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have ht3 : t⁻¹ * (t⁻¹ * t⁻¹) = 1 := by
    rw [← mul_assoc, ← pow_two, ← pow_succ, inv_pow, ht, inv_one]
  rw [h3, h4]
  calc x * (y * (x * (y * (x * y)))) = x * (t⁻¹ * (x * (y * (y * (x * y))))) := by
        rw [e1']
    _ = t⁻¹ * (x * (x * (y * (y * (x * y))))) := by rw [hx']
    _ = t⁻¹ * (x * (x * (y * (t⁻¹ * (x * (y * y)))))) := by rw [e1' y]
    _ = t⁻¹ * (x * (x * (t⁻¹ * (y * (x * (y * y)))))) := by rw [hy']
    _ = t⁻¹ * (x * (t⁻¹ * (x * (y * (x * (y * y)))))) := by rw [hx']
    _ = t⁻¹ * (t⁻¹ * (x * (x * (y * (x * (y * y)))))) := by rw [hx']
    _ = t⁻¹ * (t⁻¹ * (x * (x * (t⁻¹ * (x * (y * (y * y))))))) := by rw [e1' (y * y)]
    _ = t⁻¹ * (t⁻¹ * (x * (t⁻¹ * (x * (x * (y * (y * y))))))) := by rw [hx']
    _ = t⁻¹ * (t⁻¹ * (t⁻¹ * (x * (x * (x * (y * (y * y))))))) := by rw [hx']
    _ = x * (x * (x * (y * (y * y)))) := by rw [← mul_assoc, ← mul_assoc, mul_assoc t⁻¹ t⁻¹,
          ht3, one_mul]

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_elemAbelian_nine {L : Subgroup Y} {u₁ u₂ : Y} (h₁L : u₁ ∈ L) (h₂L : u₂ ∈ L)
    (hc : Commute u₁ u₂) (h₁ : u₁ ^ 3 = 1) (h₂ : u₂ ^ 3 = 1) (h₁1 : u₁ ≠ 1)
    (h₂z : u₂ ∉ Subgroup.zpowers u₁) :
    ∃ E : Subgroup Y, E ≤ L ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let F₀ : PUnit.{1} →* Y := 1
  have hF₀ : Function.Injective F₀ := fun a b _ => Subsingleton.elim a b
  have hcard₀ : Nat.card PUnit.{1} = 3 ^ 0 := by simp
  have hu₁r : u₁ ∉ F₀.range := by
    rintro ⟨a, ha⟩
    exact h₁1 ha.symm
  obtain ⟨F₁, hF₁, hcomm₁, hpow₁, hcard₁, hrep₁⟩ := CFSG.SectionRank.exists_extend
    (fun _ _ => rfl) (fun _ => rfl) hcard₀ F₀ hF₀ h₁ hu₁r (fun _ => Commute.one_left u₁)
  have hr₁ : ∀ a, F₁ a ∈ Subgroup.zpowers u₁ := by
    intro a
    obtain ⟨b, n, hb⟩ := hrep₁ a
    rw [hb]
    exact Subgroup.mul_mem _ (by simp [F₀]) (Subgroup.pow_mem _ (Subgroup.mem_zpowers u₁) n)
  have hu₂r : u₂ ∉ F₁.range := by
    rintro ⟨a, ha⟩
    exact h₂z (ha ▸ hr₁ a)
  have hc12 : ∀ a, Commute (F₁ a) u₂ := by
    intro a
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hr₁ a)
    rw [← hk]
    exact hc.zpow_left k
  obtain ⟨F₂, hF₂, hcomm₂, hpow₂, hcard₂, hrep₂⟩ :=
    CFSG.SectionRank.exists_extend hcomm₁ hpow₁ hcard₁ F₁ hF₁ h₂ hu₂r hc12
  refine ⟨F₂.range, ?_, ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩, ?_⟩
  · rintro _ ⟨a, rfl⟩
    obtain ⟨b, n, hb⟩ := hrep₂ a
    rw [hb]
    exact L.mul_mem ((Subgroup.zpowers_le.2 h₁L) (hr₁ b)) (L.pow_mem h₂L n)
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 b.2
    apply Subtype.ext
    change (a : Y) * b = b * a
    rw [← hx, ← hz, ← map_mul, ← map_mul, hcomm₂]
  · obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
    rw [← map_pow, hpow₂, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hF₂).toEquiv, hcard₂]
    norm_num

end Nine

section A7

variable {Y : Type} [Group Y] [Finite Y]

@[expose] def a7c₁ : alternatingGroup (Fin 7) :=
  ⟨Equiv.swap (0 : Fin 7) 1 * Equiv.swap 1 2,
    Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

@[expose] def a7c₂ : alternatingGroup (Fin 7) :=
  ⟨Equiv.swap (3 : Fin 7) 4 * Equiv.swap 4 5,
    Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

theorem a7c_facts : a7c₁ ^ 3 = 1 ∧ a7c₂ ^ 3 = 1 ∧ a7c₁ * a7c₂ = a7c₂ * a7c₁ ∧ a7c₁ ≠ 1 ∧
    a7c₂ ≠ 1 ∧ a7c₁ * a7c₂ ≠ 1 ∧ a7c₁ * a7c₂⁻¹ ≠ 1 ∧ a7c₂ ≠ a7c₁ ∧ a7c₂ ≠ a7c₁ * a7c₁ := by
  decide +kernel

theorem not_mem_zpowers_of_pow_three {G : Type*} [Group G] {x y : G} (hx : x ^ 3 = 1)
    (h0 : y ≠ 1) (h1 : y ≠ x) (h2 : y ≠ x * x) : y ∉ Subgroup.zpowers x := by
  intro hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have hk : x ^ k = x ^ (k % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 3]
    rw [zpow_add, zpow_mul, show ((3 : ℤ)) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hx,
      one_zpow, mul_one]
  rw [hk] at h0 h1 h2
  have : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases this with h | h | h <;> rw [h] at h0 h1 h2
  · exact h0 (zpow_zero x)
  · exact h1 (zpow_one x)
  · exact h2 (by rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two])

theorem exists_pow_three_eq_one_of_center {P : Type*} [Group P] [Finite P]
    (hZ3 : Nat.card (Subgroup.center P) = 3) {a b : P} (ha : a ^ 3 ∈ Subgroup.center P)
    (hb : b ^ 3 ∈ Subgroup.center P) (hab : a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center P)
    (hab' : a * b⁻¹ * a⁻¹ * b⁻¹⁻¹ ∈ Subgroup.center P) :
    a ^ 3 = 1 ∨ b ^ 3 = 1 ∨ (a * b) ^ 3 = 1 ∨ (a * b⁻¹) ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc3 : ∀ c ∈ Subgroup.center P, c ^ 3 = 1 := by
    intro c hc
    have h1 := pow_card_eq_one' (G := Subgroup.center P) (x := ⟨c, hc⟩)
    rw [hZ3] at h1
    exact congrArg Subtype.val h1
  have hcomm : ∀ c ∈ Subgroup.center P, ∀ w : P, Commute c w := fun c hc w =>
    (Subgroup.mem_center_iff.1 hc w).symm
  have e1 : (a * b) ^ 3 = a ^ 3 * b ^ 3 :=
    mul_pow_three_of_commute_comm (hcomm _ hab a) (hcomm _ hab b) (hc3 _ hab)
  have e2 : (a * b⁻¹) ^ 3 = a ^ 3 * b⁻¹ ^ 3 :=
    mul_pow_three_of_commute_comm (hcomm _ hab' a) (hcomm _ hab' b⁻¹) (hc3 _ hab')
  by_cases hα : a ^ 3 = 1
  · exact Or.inl hα
  by_cases hβ : b ^ 3 = 1
  · exact Or.inr (Or.inl hβ)
  right; right
  set α : Subgroup.center P := ⟨a ^ 3, ha⟩ with hαdef
  have hα1 : α ≠ 1 := fun h => hα (congrArg Subtype.val h)
  have htop : Subgroup.zpowers α = ⊤ := by
    have hd := Subgroup.card_subgroup_dvd_card (Subgroup.zpowers α)
    rw [hZ3, Nat.dvd_prime Nat.prime_three] at hd
    rcases hd with h1 | h3
    · exact absurd (Subgroup.zpowers_eq_bot.1 (Subgroup.eq_bot_of_card_eq _ h1)) hα1
    · exact Subgroup.eq_top_of_card_eq _ (h3.trans hZ3.symm)
  have hβmem : (⟨b ^ 3, hb⟩ : Subgroup.center P) ∈ Subgroup.zpowers α := by
    rw [htop]; exact Subgroup.mem_top _
  have hα3 : α ^ 3 = 1 := Subtype.ext (hc3 _ ha)
  by_cases hβα : (⟨b ^ 3, hb⟩ : Subgroup.center P) = α
  · right
    rw [e2, inv_pow, show b ^ 3 = a ^ 3 from congrArg Subtype.val hβα, mul_inv_cancel]
  · left
    have hβ2 : (⟨b ^ 3, hb⟩ : Subgroup.center P) = α * α := by
      by_contra hne
      exact not_mem_zpowers_of_pow_three hα3 (fun h => hβ (congrArg Subtype.val h)) hβα hne
        hβmem
    have h1 : b ^ 3 = a ^ 3 * a ^ 3 := congrArg Subtype.val hβ2
    rw [e1, h1, ← pow_add, ← pow_add, show 3 + (3 + 3) = 3 * 3 by norm_num, pow_mul,
      hc3 _ ha]

theorem exists_elemAbelian_nine_of_alt7 {L : Subgroup Y}
    (φ : (↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin 7))
    (hZ : Nat.card (Subgroup.center ↥L) = 1 ∨ Nat.card (Subgroup.center ↥L) = 3) :
    ∃ E : Subgroup Y, E ≤ L ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨h13, h23, hc12, h11, h21, h121, h12i1, h2ne1, h2ne11⟩ := a7c_facts
  set π : ↥L →* alternatingGroup (Fin 7) :=
    φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L)) with hπ
  have hπs : Function.Surjective π := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ∀ x : ↥L, π x = 1 ↔ x ∈ Subgroup.center ↥L := by
    intro x
    simp only [hπ, MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  obtain ⟨a, ha⟩ := hπs a7c₁
  obtain ⟨b, hb⟩ := hπs a7c₂
  have hcoe : ∀ (x : ↥L) (n : ℕ), ((x ^ n : ↥L) : Y) = (x : Y) ^ n := fun x n => by simp
  rcases hZ with h1 | h3
  ·
    have hZbot : Subgroup.center ↥L = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    have hinj : Function.Injective π := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have h := (hker x).1 hx
      rwa [hZbot, Subgroup.mem_bot] at h
    have hab : a * b = b * a := hinj (by rw [map_mul, map_mul, ha, hb, hc12])
    have ha3 : a ^ 3 = 1 := hinj (by rw [map_pow, ha, h13, map_one])
    have hb3 : b ^ 3 = 1 := hinj (by rw [map_pow, hb, h23, map_one])
    refine exists_elemAbelian_nine a.2 b.2 (congrArg Subtype.val hab)
      (by rw [← hcoe, ha3]; rfl) (by rw [← hcoe, hb3]; rfl) ?_ ?_
    · intro h0
      apply h11
      rw [← ha, show a = 1 from Subtype.ext h0, map_one]
    · intro hmem
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
      have hk' : a ^ k = b := Subtype.ext (by rw [← hk]; simp)
      have hab' : a7c₁ ^ k = a7c₂ := by rw [← ha, ← hb, ← map_zpow, hk']
      exact not_mem_zpowers_of_pow_three h13 h21 h2ne1 h2ne11
        (Subgroup.mem_zpowers_iff.2 ⟨k, hab'⟩)
  ·
    have hmem : ∀ x : ↥L, π x = 1 → x ∈ Subgroup.center ↥L := fun x hx => (hker x).1 hx
    have ha3 : a ^ 3 ∈ Subgroup.center ↥L := hmem _ (by rw [map_pow, ha, h13])
    have hb3 : b ^ 3 ∈ Subgroup.center ↥L := hmem _ (by rw [map_pow, hb, h23])
    have hc : a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center ↥L := hmem _ (by
      simp only [map_mul, map_inv, ha, hb]
      decide +kernel)
    have hc' : a * b⁻¹ * a⁻¹ * b⁻¹⁻¹ ∈ Subgroup.center ↥L := hmem _ (by
      simp only [map_mul, map_inv, inv_inv, ha, hb]
      decide +kernel)
    obtain ⟨x, hx3, hx1⟩ : ∃ x : ↥L, x ^ 3 = 1 ∧ π x ≠ 1 := by
      rcases exists_pow_three_eq_one_of_center h3 ha3 hb3 hc hc' with h | h | h | h
      · exact ⟨a, h, by rw [ha]; exact h11⟩
      · exact ⟨b, h, by rw [hb]; exact h21⟩
      · exact ⟨a * b, h, by rw [map_mul, ha, hb]; exact h121⟩
      · exact ⟨a * b⁻¹, h, by rw [map_mul, map_inv, ha, hb]; exact h12i1⟩
    have hcyc : IsCyclic (Subgroup.center ↥L) := isCyclic_of_prime_card (p := 3) h3
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Subgroup.center ↥L)
    have hgo : orderOf g = 3 := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, h3]
    set z : ↥L := (g : ↥L) with hz
    have hzo : orderOf z = 3 := by rw [hz, Subgroup.orderOf_coe, hgo]
    have hzc : ∀ w : ↥L, z * w = w * z := fun w => (Subgroup.mem_center_iff.1 g.2 w).symm
    refine exists_elemAbelian_nine z.2 x.2 (congrArg Subtype.val (hzc x))
      (by rw [← hcoe, ← hzo, pow_orderOf_eq_one]; rfl) (by rw [← hcoe, hx3]; rfl) ?_ ?_
    · intro h0
      have : z = 1 := Subtype.ext h0
      rw [this, orderOf_one] at hzo
      omega
    · intro hxz
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hxz
      have hk' : z ^ k = x := Subtype.ext (by rw [← hk]; simp)
      apply hx1
      rw [← hk', map_zpow]
      have hz1 : π z = 1 := (hker z).2 g.2
      rw [hz1, one_zpow]

end A7

theorem e618A7Facts_holds : E618A7Facts := by
  intro Y _ _ L A R hL h
  obtain ⟨⟨φ⟩, hZ⟩ := hL
  exact ⟨exists_elemAbelian_nine_of_alt7 φ hZ,
    Alt.altRank_of_iso Alt.A7.altModel_seven Alt.A7.card_D7q (by decide) Alt.card_G7 φ hZ h⟩

end E6

end CFSG.Quasithin
