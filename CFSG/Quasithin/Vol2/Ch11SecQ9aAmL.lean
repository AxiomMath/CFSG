module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aAmK
public import CFSG.Quasithin.Vol2.Ch11SecQ9aAmF

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

variable {G : Type} [Group G] [Finite G]

theorem exists_lift_order_three {K J : Subgroup G} {y : ↥K ⧸ CFSG.pCore 2 ↥K}
    (hy : y ∈ modO2Image K J) (hy3 : orderOf y = 3) :
    ∃ x : ↥K, (x : G) ∈ J ∧ orderOf x = 3 ∧
      (QuotientGroup.mk' (CFSG.pCore 2 ↥K) x = y ∨
        QuotientGroup.mk' (CFSG.pCore 2 ↥K) x = y⁻¹) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk, rfl⟩ := hy
  have hy3' : QuotientGroup.mk' (CFSG.pCore 2 ↥K) k ^ 3 = 1 := hy3 ▸ pow_orderOf_eq_one _
  have hk3 : k ^ 3 ∈ CFSG.pCore 2 ↥K := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow]
    exact hy3'
  have h2 : IsPGroup 2 ↥(CFSG.pCore 2 ↥K) := by
    exact CFSG.LieType.BorelTits.pCore_isPGroup 2
  obtain ⟨n, hn⟩ := h2 ⟨k ^ 3, hk3⟩
  have hn' : (k ^ 3) ^ 2 ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have h3n : ¬ 3 ∣ 2 ^ n := fun hd =>
    absurd (Nat.prime_three.dvd_of_dvd_pow hd) (by norm_num)
  have hπy : QuotientGroup.mk' (CFSG.pCore 2 ↥K) (k ^ 2 ^ n) ≠ 1 := by
    rw [map_pow]
    intro h1
    exact h3n (hy3 ▸ orderOf_dvd_of_pow_eq_one h1)
  refine ⟨k ^ 2 ^ n, (J.subgroupOf K).pow_mem hk _, ?_, ?_⟩
  · refine orderOf_eq_prime ?_ (fun h1 => hπy (by rw [h1, map_one]))
    rw [← pow_mul, mul_comm, pow_mul, hn']
  · have e : QuotientGroup.mk' (CFSG.pCore 2 ↥K) k ^ 2 ^ n =
        QuotientGroup.mk' (CFSG.pCore 2 ↥K) k ^ (2 ^ n % 3) := by
      rw [← hy3, pow_mod_orderOf]
    rw [map_pow, e]
    have hmod : 2 ^ n % 3 = 1 ∨ 2 ^ n % 3 = 2 := by omega
    rcases hmod with h | h
    · left
      rw [h, pow_one]
    · right
      rw [h]
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← pow_succ]
      exact hy3'

variable {T L I V₁ V₂ X K : Subgroup G} {P₁ P₂ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)}

theorem pCoreOf_modO2Image_le {K J : Subgroup G} (hJK : J ≤ K) :
    pCoreOf 2 (modO2Image K J) ≤ modO2Image K (pCoreOf 2 J) := by
  intro y hy
  obtain ⟨w, hw, rfl⟩ := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hy
  exact ⟨w, mem_pCoreOf_of_mk_mem hJK hw hy, rfl⟩

theorem natural_section (h : StarHyp G T L I V₁ V₂ X K) (hP : ParData T K (LOf L V₁) P₁ P₂) :
    pCoreOf 2 (k0Of K P₂) ⊓ pCoreOf 2 K ≠ pCoreOf 2 (k0Of K P₂) ∧
      ∃ y ∈ k0Of K P₂, orderOf y = 3 ∧ ∀ b ∈ pCoreOf 2 (k0Of K P₂),
        y * b * y⁻¹ * b⁻¹ ∈ pCoreOf 2 (k0Of K P₂) ⊓ pCoreOf 2 K →
          b ∈ pCoreOf 2 (k0Of K P₂) ⊓ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hO2, yb, hyb, hyb3, hfree⟩ :=
    exists_fpf_of_isPSL h.psl h.isSylowTwoOf_bar hP.c₂.1 hP.ne_top₂ hP.c₂.2.1 hP.n₂
  have hmod : modO2Image K (k0Of K P₂) = P₂ := modO2Image_k0Of K hP.c₂.2.1
  have hO : pCoreOf 2 P₂ ≤ modO2Image K (pCoreOf 2 (k0Of K P₂)) := by
    have h0 := pCoreOf_modO2Image_le (k0Of_le K P₂)
    rwa [hmod] at h0
  obtain ⟨x, hxK₀, hx3, hxy⟩ := exists_lift_order_three (hmod.symm ▸ hyb) hyb3
  have hfx : ∀ b ∈ pCoreOf 2 P₂, QuotientGroup.mk' (CFSG.pCore 2 ↥K) x * b *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥K) x)⁻¹ = b → b = 1 := by
    rcases hxy with hxy | hxy
    · rw [hxy]
      exact hfree
    · rw [hxy]
      intro b hb hc
      refine hfree b hb ?_
      calc yb * b * yb⁻¹ = yb * (yb⁻¹ * b * yb⁻¹⁻¹) * yb⁻¹ := by rw [hc]
        _ = b := by group
  refine ⟨fun heq => hO2 ?_, x, hxK₀, (Subgroup.orderOf_coe x).trans hx3,
    fun b hb hc => ⟨hb, ?_⟩⟩
  · exact eq_bot_iff.mpr (hO.trans (modO2Image_eq_bot_of_le (inf_eq_left.mp heq)).le)
  · have hbK : b ∈ K := k0Of_le K P₂ (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hb)
    have hb' : QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨b, hbK⟩ ∈ pCoreOf 2 P₂ := by
      have h0 := modO2Image_pCoreOf_le (k0Of_le K P₂) ⟨⟨b, hbK⟩, hb, rfl⟩
      rwa [hmod] at h0
    have hcK : x * ⟨b, hbK⟩ * x⁻¹ * (⟨b, hbK⟩ : ↥K)⁻¹ ∈ CFSG.pCore 2 ↥K := by
      obtain ⟨c, hc1, hc2⟩ := hc.2
      have hce : c = x * ⟨b, hbK⟩ * x⁻¹ * (⟨b, hbK⟩ : ↥K)⁻¹ := Subtype.ext (by simpa using hc2)
      rw [← hce]
      exact hc1
    have hc' : QuotientGroup.mk' (CFSG.pCore 2 ↥K) x *
        QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨b, hbK⟩ *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥K) x)⁻¹ =
        QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨b, hbK⟩ := by
      have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥K)
          (x * ⟨b, hbK⟩ * x⁻¹ * (⟨b, hbK⟩ : ↥K)⁻¹) = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hcK
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      exact mul_inv_eq_one.mp h1
    have h1 := hfx _ hb' hc'
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact ⟨⟨b, hbK⟩, h1, rfl⟩

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS
