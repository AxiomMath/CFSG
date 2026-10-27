module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5bVG
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5bBurn
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5bInv

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431

@[expose] noncomputable def t0B : Bh :=
  ⟨t0A, That_le_Bh t0A_mem_That⟩

@[expose] def xB : Bh := ⟨xA, That_le_Bh xA_mem_That⟩

theorem t0A_mem_VA : t0A ∈ VA :=
  (mem_VA_iff t0A).2 ⟨Tl.getD 20 [], Vl_special.2.2, repL_t0A⟩

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

omit [Finite G] in
theorem AutIso.imgG_VA_le
    (iso : AutIso M₁ M₂) : iso.imgG VA ≤ iso.imgG That := by
  intro g hg
  obtain ⟨b, hb, rfl⟩ := iso.mem_imgG.1 hg
  exact iso.mem_imgG.2 ⟨b, VA_le_That hb, rfl⟩

omit [Finite G] in
theorem AutIso.toG_xB
    (iso : AutIso M₁ M₂) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) (hzc : z ∈ centerOf (M₁ ⊓ M₂)) :
    iso.toG xB = z := iso.toG_xA hz2 hz1 hzc

theorem caseA
    (c : AutCtx G M₁ M₂ z) (hTG : IsSylowTwoOf (c.iso.imgG That) ⊤)
    (hnx : ¬ IsConj t0A xA) (hconj0 : IsConj (c.iso.toG t0B) z)
    (hweak : ∀ y : G, (∀ a ∈ c.iso.imgG VA, y * a * y⁻¹ ∈ c.iso.imgG That) →
      ∀ a ∈ c.iso.imgG VA, y * a * y⁻¹ ∈ c.iso.imgG VA) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ¬ 2 ∣ (c.iso.imgG That).index := by
    have e : ((c.iso.imgG That).subgroupOf ⊤).index = (c.iso.imgG That).index :=
      Subgroup.relIndex_top_right _
    have := hTG.2.2
    rwa [e] at this
  let S : Sylow 2 G := hTG.2.1.toSylow hidx
  have hxz : c.iso.toG xB = z := c.iso.toG_xB c.z2 c.z1 c.zc
  have hzV : z ∈ c.iso.imgG VA := by
    have : c.iso.toG xB ∈ c.iso.imgG VA := c.iso.mem_imgG.2 ⟨xB, xA_mem_VA, rfl⟩
    rwa [hxz] at this
  have htV : c.iso.toG t0B ∈ c.iso.imgG VA := c.iso.mem_imgG.2 ⟨t0B, t0A_mem_VA, rfl⟩
  obtain ⟨y₀, hy₀⟩ := isConj_iff.1 hconj0
  have hzW : y₀ * c.iso.toG t0B * y₀⁻¹ ∈ c.iso.imgG VA := by
    rw [hy₀]
    exact hzV
  obtain ⟨n, hn, hnt⟩ := burnside_fusion S (W := c.iso.imgG VA) (c.iso.imgG_VA_le)
    (fun a ha b hb => c.iso.Vg_comm ha hb) hweak htV hzW
  rw [c.normalizer_Vg] at hn
  set p : ↥P2h := c.iso.phi2.symm ⟨n, hn⟩ with hp
  have hpn : c.iso.toG2 p = n := by
    show ((c.iso.phi2 (c.iso.phi2.symm ⟨n, hn⟩) : ↥M₂) : G) = n
    rw [MulEquiv.apply_symm_apply]
  have e1 : c.iso.toG2 (p * Subgroup.inclusion Bh_le_P2h t0B * p⁻¹) = z := by
    rw [map_mul, map_mul, map_inv, hpn, AutIso.toG2_inclusion, hnt, hy₀]
  have e2 : c.iso.toG2 (Subgroup.inclusion Bh_le_P2h xB) = z := by
    rw [AutIso.toG2_inclusion]
    exact c.iso.toG_xB c.z2 c.z1 c.zc
  have e3 : p * Subgroup.inclusion Bh_le_P2h t0B * p⁻¹ = Subgroup.inclusion Bh_le_P2h xB :=
    c.iso.toG2_injective (e1.trans e2.symm)
  refine hnx (isConj_iff.2 ⟨(p : Ah), ?_⟩)
  exact congrArg Subtype.val e3

end CFSG.Quasithin.H13.F431.U42Aut
