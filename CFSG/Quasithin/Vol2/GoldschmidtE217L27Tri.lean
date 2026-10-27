module

public import CFSG.Quasithin.Background.E2SeventeenSolv

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6 E2

namespace E217L27

theorem prod_eq_one {Γ : Type*} [Group Γ] {m₁ m₂ u : Γ} (h12 : Commute m₁ m₂)
    (h1u : Commute m₁ u) (h2u : Commute m₂ u) (hm₁ : m₁ * m₁ = 1) (hm₂ : m₂ * m₂ = 1)
    (hu : u * u = 1) : m₁ * m₂ * (u * m₂) * (u * m₁) = 1 := by
  have hc : Commute m₁ (m₂ * u * m₂ * u) := ((h12.mul_right h1u).mul_right h12).mul_right h1u
  calc m₁ * m₂ * (u * m₂) * (u * m₁) = m₁ * ((m₂ * u * m₂ * u) * m₁) := by group
    _ = m₁ * (m₁ * (m₂ * u * m₂ * u)) := by rw [← hc.eq]
    _ = (m₁ * m₁) * (m₂ * u * m₂ * u) := by group
    _ = 1 := by
      have e : m₂ * u * m₂ * u = (m₂ * m₂) * (u * u) := by
        calc m₂ * u * m₂ * u = m₂ * (u * m₂) * u := by group
          _ = m₂ * (m₂ * u) * u := by rw [← h2u.eq]
          _ = (m₂ * m₂) * (u * u) := by group
      rw [e, hm₁, hm₂, hu]
      group

theorem triple_core {Γ : Type*} [Group Γ] {𝔅 𝔄 𝔓 : Subgroup Γ} (hBA : 𝔅 ⊓ 𝔄 = ⊥)
    (hBP : 𝔅 ≤ 𝔓) (hAP : 𝔄 ≤ 𝔓) (hdec : ∀ p ∈ 𝔓, ∃ u ∈ 𝔅, ∃ a ∈ 𝔄, u * a = p)
    (hcomm : ∀ p ∈ 𝔓, ∀ q ∈ 𝔓, p * q = q * p) (hsq : ∀ p ∈ 𝔓, p * p = 1)
    {x z : Γ} (hz3 : z ^ 3 = 1) (hx2 : x * x = 1) (hxz : x * z * x⁻¹ = z⁻¹)
    (hxB : ∀ p ∈ 𝔅, x * p * x⁻¹ = p) (hzP : ∀ p ∈ 𝔓, z * p * z⁻¹ ∈ 𝔓)
    (hwB : ∀ p ∈ 𝔅, (z * x) * p * (z * x)⁻¹ ∈ 𝔄) (hwA : ∀ p ∈ 𝔄, (z * x) * p * (z * x)⁻¹ ∈ 𝔅)
    {b : Γ} (hb : b ∈ 𝔅) : b * (z * b * z⁻¹) * (z⁻¹ * b * z) = 1 := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hz3' : z * z * z = 1 := by
    calc z * z * z = z ^ 3 := by rw [pow_succ, pow_two]
      _ = 1 := hz3
  have hzz : z * z = z⁻¹ := eq_inv_of_mul_eq_one_left hz3'
  have hxzi : x * z⁻¹ * x⁻¹ = z := by
    have := congrArg (fun t => t⁻¹) hxz
    simpa [mul_assoc] using this
  have hzP' : ∀ p ∈ 𝔓, z⁻¹ * p * z ∈ 𝔓 := by
    intro p hp
    have h1 := hzP _ (hzP p hp)
    have e : z * (z * p * z⁻¹) * z⁻¹ = z⁻¹ * p * z := by
      calc z * (z * p * z⁻¹) * z⁻¹ = (z * z) * p * (z * z)⁻¹ := by group
        _ = z⁻¹ * p * z := by rw [hzz]; group
    rwa [e] at h1
  have hbP : b ∈ 𝔓 := hBP hb
  have hcP : z⁻¹ * b * z ∈ 𝔓 := hzP' b hbP
  obtain ⟨u, hu, a, ha, hua⟩ := hdec _ hcP
  have hwc : (z * x) * (z⁻¹ * b * z) * (z * x)⁻¹ = z⁻¹ * b * z := by
    have e1 : x * (z⁻¹ * b * z) * x⁻¹ = z * b * z⁻¹ := by
      calc x * (z⁻¹ * b * z) * x⁻¹ = (x * z⁻¹ * x⁻¹) * (x * b * x⁻¹) * (x * z * x⁻¹) := by group
        _ = z * b * z⁻¹ := by rw [hxzi, hxB b hb, hxz]
    calc (z * x) * (z⁻¹ * b * z) * (z * x)⁻¹ = z * (x * (z⁻¹ * b * z) * x⁻¹) * z⁻¹ := by group
      _ = z * (z * b * z⁻¹) * z⁻¹ := by rw [e1]
      _ = (z * z) * b * (z * z)⁻¹ := by group
      _ = z⁻¹ * b * z := by rw [hzz]; group
  have hu' : (z * x) * u * (z * x)⁻¹ ∈ 𝔄 := hwB u hu
  have ha' : (z * x) * a * (z * x)⁻¹ ∈ 𝔅 := hwA a ha
  have hc2 : (z * x) * u * (z * x)⁻¹ * ((z * x) * a * (z * x)⁻¹) = z⁻¹ * b * z := by
    rw [← hwc, ← hua]
    group
  have hu'P : (z * x) * u * (z * x)⁻¹ ∈ 𝔓 := hAP hu'
  have ha'P : (z * x) * a * (z * x)⁻¹ ∈ 𝔓 := hBP ha'
  have huP : u ∈ 𝔓 := hBP hu
  have haP : a ∈ 𝔓 := hAP ha
  set u' := (z * x) * u * (z * x)⁻¹ with hu'def
  set a' := (z * x) * a * (z * x)⁻¹ with ha'def
  have h1 : u * a = a' * u' := by
    rw [hua, ← hc2, hcomm u' hu'P a' ha'P]
  have h2 : a'⁻¹ * u = u' * a⁻¹ := by
    calc a'⁻¹ * u = a'⁻¹ * (u * a) * a⁻¹ := by group
      _ = a'⁻¹ * (a' * u') * a⁻¹ := by rw [h1]
      _ = u' * a⁻¹ := by group
  have hmemB : a'⁻¹ * u ∈ 𝔅 := 𝔅.mul_mem (𝔅.inv_mem ha') hu
  have hmemA : a'⁻¹ * u ∈ 𝔄 := h2 ▸ 𝔄.mul_mem hu' (𝔄.inv_mem ha)
  have h3 : a'⁻¹ * u = 1 := by
    have : a'⁻¹ * u ∈ 𝔅 ⊓ 𝔄 := ⟨hmemB, hmemA⟩
    rwa [hBA, Subgroup.mem_bot] at this
  have h4 : u' * a⁻¹ = 1 := h2 ▸ h3
  have hu'a : u' = a := mul_inv_eq_one.1 h4
  have haz : a = z * u * z⁻¹ := by
    rw [← hu'a, hu'def]
    calc (z * x) * u * (z * x)⁻¹ = z * (x * u * x⁻¹) * z⁻¹ := by group
      _ = z * u * z⁻¹ := by rw [hxB u hu]
  have hc : z⁻¹ * b * z = u * (z * u * z⁻¹) := by rw [← haz, hua]
  have hb' : b = (z * u * z⁻¹) * (z * (z * u * z⁻¹) * z⁻¹) := by
    have : z * (z⁻¹ * b * z) * z⁻¹ = b := by group
    rw [← this, hc]
    group
  have hbz : z * b * z⁻¹ = u * (z⁻¹ * u * z) := by
    have e1 : x * (z⁻¹ * b * z) * x⁻¹ = z * b * z⁻¹ := by
      calc x * (z⁻¹ * b * z) * x⁻¹ = (x * z⁻¹ * x⁻¹) * (x * b * x⁻¹) * (x * z * x⁻¹) := by group
        _ = z * b * z⁻¹ := by rw [hxzi, hxB b hb, hxz]
    have e2 : x * (u * (z * u * z⁻¹)) * x⁻¹ = u * (z⁻¹ * u * z) := by
      calc x * (u * (z * u * z⁻¹)) * x⁻¹
          = (x * u * x⁻¹) * (x * z * x⁻¹) * (x * u * x⁻¹) * (x * z⁻¹ * x⁻¹) := by group
        _ = u * (z⁻¹ * u * z) := by rw [hxB u hu, hxz, hxzi]; group
    rw [← e1, hc, e2]
  have hz2 : z⁻¹ * u * z = z * (z * u * z⁻¹) * z⁻¹ := by
    calc z⁻¹ * u * z = (z * z) * u * (z * z)⁻¹ := by rw [hzz]; group
      _ = z * (z * u * z⁻¹) * z⁻¹ := by group
  set m₁ := z * u * z⁻¹ with hm₁
  set m₂ := z * m₁ * z⁻¹ with hm₂
  have hm₁P : m₁ ∈ 𝔓 := hzP u huP
  have hm₂P : m₂ ∈ 𝔓 := hzP m₁ hm₁P
  have hprod := prod_eq_one (m₁ := m₁) (m₂ := m₂) (u := u)
    (hcomm m₁ hm₁P m₂ hm₂P) (hcomm m₁ hm₁P u huP) (hcomm m₂ hm₂P u huP) (hsq m₁ hm₁P)
    (hsq m₂ hm₂P) (hsq u huP)
  have e_bz : z * b * z⁻¹ = u * m₂ := by rw [hbz, hz2]
  rw [e_bz, hc, hb']
  exact hprod

variable {G : Type} [Group G] [Finite G] {H T V U : Subgroup G} {x z : G}

theorem triple_rel (d : DihedralPair H T V U x z) (hz3 : z ^ 3 = 1) {b : G} (hb : b ∈ U) :
    b * (z * b * z⁻¹) * (z⁻¹ * b * z) ∈ dpZ V z := by
  set I := dpI V z with hI
  set Z := dpZ V z with hZ
  have hZc : ∀ ζ ∈ Z.subgroupOf I, ∀ g : ↥I, g * ζ = ζ * g := fun ζ hζ g =>
    Subtype.ext (d.ZC ζ (Subgroup.mem_subgroupOf.1 hζ) g g.2)
  have hN : (Z.subgroupOf I).Normal :=
    ⟨fun n hn g => by
      have := hZc n hn g
      rw [this, mul_assoc, mul_inv_cancel, mul_one]
      exact hn⟩
  set π : ↥I →* ↥I ⧸ Z.subgroupOf I := QuotientGroup.mk' (Z.subgroupOf I) with hπ
  have hker : ∀ g : ↥I, π g = 1 ↔ (g : G) ∈ Z := fun g => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hzI : z ∈ I := d.zI
  have hxI : x ∈ I := Subgroup.mem_sup_left d.xV
  have hUI : ∀ g ∈ U, g ∈ I := fun g hg => Subgroup.mem_sup_left (d.UV hg)
  have hAI : ∀ g ∈ dpA H V U z, g ∈ I := fun g hg => (d.AR.trans inf_le_left) hg
  set zI : ↥I := ⟨z, hzI⟩ with hzIdef
  set xI : ↥I := ⟨x, hxI⟩ with hxIdef
  set 𝔅 := (U.subgroupOf I).map π with h𝔅
  set 𝔄 := ((dpA H V U z).subgroupOf I).map π with h𝔄
  set 𝔓 := ((dpP H V U z).subgroupOf I).map π with h𝔓
  have hBA : 𝔅 ⊓ 𝔄 = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨⟨β, hβ, rfl⟩, ⟨α, hα, hαβ⟩⟩
    rw [Subgroup.mem_bot]
    have h1 := (QuotientGroup.eq (s := Z.subgroupOf I)).1 hαβ
    have h1' : (((α⁻¹ * β : ↥I)) : G) ∈ Z := Subgroup.mem_subgroupOf.1 h1
    have hβ' : (β : G) ∈ U := Subgroup.mem_subgroupOf.1 hβ
    have hα' : (α : G) ∈ dpA H V U z := Subgroup.mem_subgroupOf.1 hα
    have hβA : (β : G) ∈ dpA H V U z := by
      have e : (β : G) = (α : G) * (((α⁻¹ * β : ↥I)) : G) := by simp
      rw [e]
      exact (dpA H V U z).mul_mem hα' (d.ZA h1')
    have hβZ : (β : G) ∈ Z := by
      have : (β : G) ∈ U ⊓ dpA H V U z := ⟨hβ', hβA⟩
      rwa [d.U_inf_A] at this
    exact (hker β).2 hβZ
  have hBP : 𝔅 ≤ 𝔓 := by
    rintro _ ⟨β, hβ, rfl⟩
    exact ⟨β, Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.1 hβ)),
      rfl⟩
  have hAP : 𝔄 ≤ 𝔓 := by
    rintro _ ⟨α, hα, rfl⟩
    exact ⟨α, Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.1 hα)),
      rfl⟩
  have hdec : ∀ p ∈ 𝔓, ∃ u ∈ 𝔅, ∃ a ∈ 𝔄, u * a = p := by
    rintro _ ⟨p₀, hp₀, rfl⟩
    obtain ⟨u, hu, a, ha, hua⟩ := d.mem_P (Subgroup.mem_subgroupOf.1 hp₀)
    refine ⟨π ⟨u, hUI u hu⟩, ⟨⟨u, hUI u hu⟩, Subgroup.mem_subgroupOf.2 hu, rfl⟩,
      π ⟨a, hAI a ha⟩, ⟨⟨a, hAI a ha⟩, Subgroup.mem_subgroupOf.2 ha, rfl⟩, ?_⟩
    rw [← map_mul]
    congr 1
    exact Subtype.ext hua
  have hcomm : ∀ p ∈ 𝔓, ∀ q ∈ 𝔓, p * q = q * p := by
    rintro _ ⟨p₀, hp₀, rfl⟩ _ ⟨q₀, hq₀, rfl⟩
    have hp := Subgroup.mem_subgroupOf.1 hp₀
    have hq := Subgroup.mem_subgroupOf.1 hq₀
    rw [← map_mul, ← map_mul]
    apply (QuotientGroup.eq (s := Z.subgroupOf I)).2
    refine Subgroup.mem_subgroupOf.2 ?_
    have := d.comm_mem_Z ((dpP H V U z).inv_mem hq) ((dpP H V U z).inv_mem hp)
    have e : (((p₀ * q₀)⁻¹ * (q₀ * p₀) : ↥I) : G) =
        (q₀ : G)⁻¹ * (p₀ : G)⁻¹ * (q₀ : G)⁻¹⁻¹ * (p₀ : G)⁻¹⁻¹ := by simp [mul_assoc]
    rw [e]
    exact this
  have hsq : ∀ p ∈ 𝔓, p * p = 1 := by
    rintro _ ⟨p₀, hp₀, rfl⟩
    rw [← map_mul, hker]
    exact d.sq_mem_Z (Subgroup.mem_subgroupOf.1 hp₀)
  have hz3' : (π zI) ^ 3 = 1 := by
    have : zI ^ 3 = 1 := Subtype.ext (by simpa using hz3)
    rw [← map_pow, this, map_one]
  have hx2' : π xI * π xI = 1 := by
    have : xI * xI = 1 := Subtype.ext d.x2
    rw [← map_mul, this, map_one]
  have hxz' : π xI * π zI * (π xI)⁻¹ = (π zI)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    exact Subtype.ext (by simpa using d.xz)
  have hxB : ∀ p ∈ 𝔅, π xI * p * (π xI)⁻¹ = p := by
    rintro _ ⟨β, hβ, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hc := B2F.isElemAbelian_comm d.elem d.xV (d.UV (Subgroup.mem_subgroupOf.1 hβ))
    show x * (β : G) * x⁻¹ = β
    rw [hc]
    group
  have hzP : ∀ p ∈ 𝔓, π zI * p * (π zI)⁻¹ ∈ 𝔓 := by
    rintro _ ⟨p₀, hp₀, rfl⟩
    refine ⟨zI * p₀ * zI⁻¹, Subgroup.mem_subgroupOf.2 ?_, by simp [map_mul]⟩
    exact (Subgroup.mem_normalizer_iff.mp (d.IP hzI) p₀).mp (Subgroup.mem_subgroupOf.1 hp₀)
  have hzxI : z * x ∈ I := d.zxI
  have hwB : ∀ p ∈ 𝔅, (π zI * π xI) * p * (π zI * π xI)⁻¹ ∈ 𝔄 := by
    rintro _ ⟨β, hβ, rfl⟩
    refine ⟨zI * xI * β * (zI * xI)⁻¹, Subgroup.mem_subgroupOf.2 ?_, by simp [map_mul]⟩
    have hβ' : (β : G) ∈ U := Subgroup.mem_subgroupOf.1 hβ
    have hm : z * x * (β : G) * (z * x)⁻¹ ∈ cjSub (z * x) U := by
      rw [mem_cjSub]
      have e : (z * x)⁻¹ * (z * x * (β : G) * (z * x)⁻¹) * (z * x) = β := by group
      rw [e]
      exact hβ'
    rw [d.swap_U] at hm
    simpa [mul_assoc] using hm
  have hwA : ∀ p ∈ 𝔄, (π zI * π xI) * p * (π zI * π xI)⁻¹ ∈ 𝔅 := by
    rintro _ ⟨α, hα, rfl⟩
    refine ⟨zI * xI * α * (zI * xI)⁻¹, Subgroup.mem_subgroupOf.2 ?_, by simp [map_mul]⟩
    have hα' : (α : G) ∈ dpA H V U z := Subgroup.mem_subgroupOf.1 hα
    have hm : z * x * (α : G) * (z * x)⁻¹ ∈ cjSub (z * x) (dpA H V U z) := by
      rw [mem_cjSub]
      have e : (z * x)⁻¹ * (z * x * (α : G) * (z * x)⁻¹) * (z * x) = α := by group
      rw [e]
      exact hα'
    rw [d.swap_A] at hm
    simpa [mul_assoc] using hm
  have hbI : b ∈ I := hUI b hb
  have hb𝔅 : π ⟨b, hbI⟩ ∈ 𝔅 := ⟨⟨b, hbI⟩, Subgroup.mem_subgroupOf.2 hb, rfl⟩
  have h := triple_core hBA hBP hAP hdec hcomm hsq hz3' hx2' hxz' hxB hzP hwB hwA hb𝔅
  have h' : π (⟨b, hbI⟩ * (zI * ⟨b, hbI⟩ * zI⁻¹) * (zI⁻¹ * ⟨b, hbI⟩ * zI)) = 1 := by
    simpa [map_mul, map_inv] using h
  have := (hker _).1 h'
  simpa [mul_assoc] using this

end E217L27

end CFSG.Quasithin
