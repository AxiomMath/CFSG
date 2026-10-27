module

public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.Quasithin.H13.KG1297

open CFSG.Open

@[expose] def NoE9 {M : Type*} [Group M] (Y : Subgroup M) : Prop :=
  ∀ a ∈ Y, ∀ b ∈ Y, a ^ 3 = 1 → b ^ 3 = 1 → a * b = b * a → a ≠ 1 → b ∈ Subgroup.zpowers a

variable {M : Type*} [Group M]

theorem orderOf_eq_three {a : M} (ha : a ^ 3 = 1) (ha1 : a ≠ 1) : orderOf a = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime ha ha1

theorem exists_elemAbelian_nine [Finite M] {a b : M} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hab : a * b = b * a) (ha1 : a ≠ 1) (hba : b ∉ Subgroup.zpowers a) :
    ∃ E : Subgroup M, E ≤ Subgroup.closure {a, b} ∧ (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧
      (∀ x ∈ E, x ^ 3 = 1) ∧ Nat.card E = 9 := by
  have hb1 : b ≠ 1 := fun h => hba (h ▸ Subgroup.one_mem _)
  have hoa := orderOf_eq_three ha ha1
  have hob := orderOf_eq_three hb hb1
  have hc : Commute a b := hab
  have hcomm : ∀ (x : ↥(Subgroup.zpowers a)) (y : ↥(Subgroup.zpowers b)),
      Commute ((Subgroup.zpowers a).subtype x) ((Subgroup.zpowers b).subtype y) := by
    intro x y
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.2
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp y.2
    change Commute (x : M) (y : M)
    rw [← hk, ← hl]
    exact hc.zpow_zpow k l
  set f : ↥(Subgroup.zpowers a) × ↥(Subgroup.zpowers b) →* M :=
    MonoidHom.noncommCoprod (Subgroup.zpowers a).subtype (Subgroup.zpowers b).subtype hcomm
    with hf
  have hfapp : ∀ p, f p = (p.1 : M) * p.2 := fun p => rfl
  have hdisj : ∀ y ∈ Subgroup.zpowers b, y ∈ Subgroup.zpowers a → y = 1 := by
    intro y hyb hya
    by_contra hy1
    have hyo : orderOf y = 3 := by
      have h1 := orderOf_dvd_of_mem_zpowers hyb
      rw [hob] at h1
      rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) hy1
      · exact h
    have hle : Subgroup.zpowers y ≤ Subgroup.zpowers b := Subgroup.zpowers_le.2 hyb
    have heq : Subgroup.zpowers y = Subgroup.zpowers b :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hyo, hob])
    apply hba
    have : b ∈ Subgroup.zpowers y := heq ▸ Subgroup.mem_zpowers b
    exact (Subgroup.zpowers_le.2 hya) this
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, y⟩ hxy
    have hxy' : (x : M) * y = 1 := hxy
    have hy : (y : M) = (x : M)⁻¹ := eq_inv_of_mul_eq_one_right hxy'
    have hy1 : (y : M) = 1 := hdisj _ y.2 (by rw [hy]; exact Subgroup.inv_mem _ x.2)
    have hx1 : (x : M) = 1 := by rw [hy1, mul_one] at hxy'; exact hxy'
    rw [Subgroup.mem_bot]
    exact Prod.ext (Subtype.ext hx1) (Subtype.ext hy1)
  refine ⟨f.range, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨⟨x, y⟩, rfl⟩
    rw [hfapp]
    refine Subgroup.mul_mem _ ?_ ?_
    · exact (Subgroup.zpowers_le.2 (Subgroup.subset_closure (Set.mem_insert a _))) x.2
    · exact (Subgroup.zpowers_le.2
        (Subgroup.subset_closure (Set.mem_insert_of_mem a (Set.mem_singleton b)))) y.2
  · rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Prod.ext (mul_comm' p.1 q.1) (mul_comm' p.2 q.2)
  · rintro _ ⟨⟨x, y⟩, rfl⟩
    rw [hfapp]
    have hxy : Commute (x : M) (y : M) := hcomm x y
    rw [hxy.mul_pow]
    have hx3 : (x : M) ^ 3 = 1 := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.2
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha, one_zpow]
    have hy3 : (y : M) ^ 3 = 1 := by
      obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp y.2
      rw [← hl, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb, one_zpow]
    rw [hx3, hy3, mul_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod, Nat.card_zpowers,
      Nat.card_zpowers, hoa, hob]

variable {G : Type*} [Group G] [Finite G]

theorem two_le_pRank_of_lift [Finite M] {Y : Subgroup G} (ρ : ↥Y →* M) (hker : IsPGroup 2 ρ.ker)
    {E' : Subgroup M} (hE'ρ : E' ≤ ρ.range) (hcomm : ∀ x ∈ E', ∀ y ∈ E', x * y = y * x)
    (hexp : ∀ x ∈ E', x ^ 3 = 1) (hcard : Nat.card E' = 9) : 2 ≤ pRank 3 Y := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Ehat : Subgroup ↥Y := E'.comap ρ with hEhat
  set f : ↥Ehat →* ↥E' := (ρ.comp Ehat.subtype).codRestrict E' (fun x => x.2) with hfdef
  have hfs : Function.Surjective f := by
    intro e
    obtain ⟨y, hy⟩ := hE'ρ e.2
    exact ⟨⟨y, show ρ y ∈ E' by rw [hy]; exact e.2⟩, Subtype.ext hy⟩
  have h9 : 3 ^ 2 ∣ Nat.card Ehat := by
    rw [show (3 : ℕ) ^ 2 = 9 from rfl, ← hcard]
    exact Subgroup.card_dvd_of_surjective hfs
  obtain ⟨P₀, hP₀⟩ := Sylow.exists_subgroup_card_pow_prime 3 h9
  set P : Subgroup ↥Y := P₀.map Ehat.subtype with hPdef
  have hPcard : Nat.card P = 9 := by
    rw [hPdef, Subgroup.card_map_of_injective Ehat.subtype_injective, hP₀]
    rfl
  have hPE : ∀ y ∈ P, ρ y ∈ E' := by
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  have htriv : ∀ y ∈ P, ρ y = 1 → y = 1 := by
    intro y hyP hy
    obtain ⟨k, hk⟩ := hker ⟨y, hy⟩
    have h1 : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hk)
    have h2 : orderOf y ∣ 9 := by
      have := orderOf_dvd_natCard (⟨y, hyP⟩ : ↥P)
      rw [hPcard, Subgroup.orderOf_mk] at this
      exact this
    have hcop : Nat.Coprime (2 ^ k) 9 :=
      Nat.Coprime.pow_left k (by norm_num)
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  set E : Subgroup G := P.map Y.subtype with hEdef
  refine SectionRank.le_pRank (by norm_num) (E := E) (Subgroup.map_subtype_le _) ⟨⟨⟨?_⟩⟩, ?_⟩ ?_
  · rintro ⟨_, ⟨y₁, hy₁, rfl⟩⟩ ⟨_, ⟨y₂, hy₂, rfl⟩⟩
    apply Subtype.ext
    show (y₁ : G) * y₂ = y₂ * y₁
    have h := htriv (y₁ * y₂ * y₁⁻¹ * y₂⁻¹)
      (P.mul_mem (P.mul_mem (P.mul_mem hy₁ hy₂) (P.inv_mem hy₁)) (P.inv_mem hy₂)) (by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm _ (hPE y₁ hy₁) _ (hPE y₂ hy₂)]
        group)
    have h' : y₁ * y₂ = y₂ * y₁ := by
      calc y₁ * y₂ = (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) * (y₂ * y₁) := by group
        _ = y₂ * y₁ := by rw [h, one_mul]
    exact congrArg Subtype.val h'
  · rintro _ ⟨y, hy, rfl⟩
    have h := htriv (y ^ 3) (P.pow_mem hy 3) (by rw [map_pow, hexp _ (hPE y hy)])
    show (y : G) ^ 3 = 1
    rw [← Subgroup.coe_pow, h, Subgroup.coe_one]
  · rw [hEdef, Subgroup.card_map_of_injective Y.subtype_injective, hPcard]
    rfl

theorem noE9_of_pRank [Finite M] {Y : Subgroup G} (ρ : ↥Y →* M) (hker : IsPGroup 2 ρ.ker)
    (hY : pRank 3 Y ≤ 1) : NoE9 ρ.range := by
  intro a ha b hb ha3 hb3 hab ha1
  by_contra hba
  obtain ⟨E', hE'cl, hcomm, hexp, hcard⟩ := exists_elemAbelian_nine ha3 hb3 hab ha1 hba
  have hcl : Subgroup.closure {a, b} ≤ ρ.range := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  have := two_le_pRank_of_lift ρ hker (hE'cl.trans hcl) hcomm hexp hcard
  omega

end CFSG.Quasithin.H13.KG1297
