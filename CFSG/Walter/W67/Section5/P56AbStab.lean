module

public import CFSG.Walter.W67.Section5.P56AbCore
import CFSG.Walter.Bender1970.S1.QdNotInvolved
import all CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.PStability

public section

namespace CFSG.Walter.W67

open P56Ab
open scoped commutatorElement

namespace P56AbData

variable {G : Type} [Group G] [Finite G] (d : P56AbData G)

theorem pStableLocal_NV :
    Glauberman.pStableLocal 3 d.NV := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hab : HasAbelianSylowTwo d.NV := BenderSuzuki.HasAbelianSylow.subgroup d.abelian_sylow d.NV
  have hstabQ : Glauberman.pStable 3 ((⊤ : Subgroup d.NV) ⧸ (⊥ : Subgroup (⊤ : Subgroup d.NV))) :=
    (Glauberman.lemma6_3 (by norm_num)).mp (qd_not_involved_of_hasAbelianSylowTwo hab
      (by norm_num)) ⊤ ⊥
  have hstab : Glauberman.pStable 3 d.NV :=
    (Glauberman.pStable_iso (QuotientGroup.quotientBot.trans Subgroup.topEquiv)).mp hstabQ
  refine Glauberman.pStableLocal_of_core_ne_bot 3 hstab ?_
  intro hbot
  have hVn : (d.V.subgroupOf d.NV).Normal := Subgroup.normal_in_normalizer
  have hVp : IsPGroup 3 (d.V.subgroupOf d.NV) :=
    d.V_isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe d.V_le_NV).symm
  have hle : d.V.subgroupOf d.NV ≤ pCore 3 d.NV := le_sSup ⟨hVn, hVp⟩
  rw [hbot] at hle
  apply d.V_ne_bot
  rw [eq_bot_iff]
  intro m hm
  have := hle (show (⟨m, d.V_le_NV hm⟩ : d.NV) ∈ d.V.subgroupOf d.NV from hm)
  rw [Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val this

theorem pCore_quotient_eq_bot :
    pCore 3 (Subgroup.normalizer ((d.V.subgroupOf d.NV : Subgroup d.NV) : Set d.NV) ⧸
      (Subgroup.centralizer ((d.V.subgroupOf d.NV : Subgroup d.NV) : Set d.NV)).subgroupOf
        (Subgroup.normalizer ((d.V.subgroupOf d.NV : Subgroup d.NV) : Set d.NV))) = ⊥ := by
  set P : Subgroup d.NV := d.V.subgroupOf d.NV with hP
  set N' := Subgroup.normalizer (P : Set d.NV) with hN'
  set C' := Subgroup.centralizer (P : Set d.NV) with hC'
  let f : N' →* d.Nbar := d.φ.rangeRestrict.comp N'.subtype
  have hf : Function.Surjective f := by
    rintro ⟨_, ⟨y, rfl⟩⟩
    have hPn : P.Normal := Subgroup.normal_in_normalizer
    have hy : y ∈ N' := by
      rw [hN', Subgroup.normalizer_eq_top_iff.mpr hPn]
      exact Subgroup.mem_top _
    exact ⟨⟨y, hy⟩, rfl⟩
  have hker : C'.subgroupOf N' = f.ker := by
    ext y
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    change (y : d.NV) ∈ C' ↔ d.φ.rangeRestrict y = 1
    rw [← Subtype.coe_inj, MonoidHom.coe_rangeRestrict, OneMemClass.coe_one, φ_eq_one_iff,
      Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro h m hm
      exact congrArg Subtype.val (h ⟨m, d.V_le_NV hm⟩ hm)
    · intro h m hm
      exact Subtype.ext (h m hm)
  let e : (N' ⧸ C'.subgroupOf N') ≃* d.Nbar :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have hmap := pCore_map_iso 3 e
  rw [d.pCore_Nbar_eq_bot] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hmap

theorem mem_CV_of_quadratic
    {x : G} (hx : x ∈ d.NV)
    (hq : ∀ m ∈ d.V, x * (m⁻¹ * (x * m * x⁻¹)) * x⁻¹ = m⁻¹ * (x * m * x⁻¹)) : x ∈ d.CV := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := d.pStableLocal_NV
  set P : Subgroup d.NV := d.V.subgroupOf d.NV with hP
  have hPn : P.Normal := Subgroup.normal_in_normalizer
  have hPp : IsPGroup 3 P := d.V_isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe d.V_le_NV).symm
  have hcorePn : (pPrimeCore 3 d.NV ⊔ P).Normal := by
    have : (pPrimeCore 3 d.NV).Normal := Subgroup.sSup_normal _ fun _ hK => hK.1
    exact Subgroup.sup_normal _ _
  set x' : d.NV := ⟨x, hx⟩ with hx'
  have hxN : x' ∈ Subgroup.normalizer (P : Set d.NV) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hPn]
    exact Subgroup.mem_top _
  set W : Subgroup d.NV := (d.V ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf d.NV
  have hPW : ⁅P, Subgroup.zpowers x'⁆ ≤ W := by
    rw [Subgroup.commutator_le]
    intro m hm z hz
    obtain ⟨k, rfl⟩ := (mem_powers_iff_mem_zpowers.mpr hz : z ∈ Submonoid.powers x')
    have hmV : (m : G) ∈ d.V := hm
    set u : G := (m : G)⁻¹ * (x * m * x⁻¹) with hu
    have huV : u ∈ d.V := d.V.mul_mem (d.V.inv_mem hmV)
      ((Subgroup.mem_normalizer_iff.mp hx m).mp hmV)
    have hux : x * u * x⁻¹ = u := hq m hmV
    have hxu : x * u = u * x := by
      calc x * u = x * u * x⁻¹ * x := by group
        _ = u * x := by rw [hux]
    have hpow : ∀ k : ℕ, x ^ k * (m : G) * (x ^ k)⁻¹ = m * u ^ k := by
      have hstep : x * (m : G) * x⁻¹ = m * u := by rw [hu]; group
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have hcomm : x * u ^ k * x⁻¹ = u ^ k := by
          rw [(Commute.pow_right (show Commute x u from hxu) k).eq, mul_inv_cancel_right]
        calc x ^ (k + 1) * (m : G) * (x ^ (k + 1))⁻¹ =
              x * (x ^ k * (m : G) * (x ^ k)⁻¹) * x⁻¹ := by group
          _ = (x * m * x⁻¹) * (x * u ^ k * x⁻¹) := by rw [ih]; group
          _ = m * u ^ (k + 1) := by rw [hstep, hcomm, pow_succ', mul_assoc]
    rw [Subgroup.mem_subgroupOf]
    have hcoe : ((⁅m, x' ^ k⁆ : d.NV) : G) = (u ^ k)⁻¹ := by
      rw [commutatorElement_def]
      push_cast
      change (m : G) * x ^ k * (m : G)⁻¹ * (x ^ k)⁻¹ = (u ^ k)⁻¹
      have hmu : (m : G) * u ^ k = u ^ k * m :=
        d.V_comm hmV (d.V.pow_mem huV k)
      calc (m : G) * x ^ k * (m : G)⁻¹ * (x ^ k)⁻¹ = m * (x ^ k * (m : G) * (x ^ k)⁻¹)⁻¹ := by
            group
        _ = (u ^ k)⁻¹ := by rw [hpow, hmu]; group
    rw [hcoe]
    refine Subgroup.mem_inf.mpr ⟨d.V.inv_mem (d.V.pow_mem huV k), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [show (u ^ k)⁻¹ * x = x * (u ^ k)⁻¹ by
      rw [← (Commute.inv_left (Commute.pow_left (show Commute x u from hxu).symm k)).eq]]
  have hWZ : ⁅W, Subgroup.zpowers x'⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro w hw z hz
    obtain ⟨k, rfl⟩ := (mem_powers_iff_mem_zpowers.mpr hz : z ∈ Submonoid.powers x')
    rw [Subgroup.mem_bot]
    obtain ⟨-, hwC⟩ := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hw)
    have hwx : (w : G) * x = x * w := Subgroup.mem_centralizer_singleton_iff.mp hwC
    apply Subtype.ext
    rw [commutatorElement_def]
    push_cast
    change (w : G) * x ^ k * (w : G)⁻¹ * (x ^ k)⁻¹ = 1
    rw [(Commute.pow_right (show Commute (w : G) x from hwx) k).eq]
    group
  have hquad : ⁅⁅P, Subgroup.zpowers x'⁆, Subgroup.zpowers x'⁆ = ⊥ :=
    eq_bot_iff.mpr ((Subgroup.commutator_mono hPW le_rfl).trans hWZ.le)
  have h : QuotientGroup.mk' ((Subgroup.centralizer (P : Set d.NV)).subgroupOf
      (Subgroup.normalizer (P : Set d.NV))) ⟨x', hxN⟩ ∈
      pCore 3 (Subgroup.normalizer (P : Set d.NV) ⧸ (Subgroup.centralizer (P : Set d.NV)).subgroupOf
        (Subgroup.normalizer (P : Set d.NV))) := hst P hPp hcorePn x' hxN hquad
  rw [d.pCore_quotient_eq_bot, Subgroup.mem_bot, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
  rw [Subgroup.mem_centralizer_iff]
  intro m hm
  exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp h ⟨m, d.V_le_NV hm⟩ hm)

end P56AbData

end CFSG.Walter.W67
