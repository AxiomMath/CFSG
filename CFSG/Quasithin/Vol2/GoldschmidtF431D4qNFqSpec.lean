module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qNFqBase

public section

namespace CFSG.Quasithin.H13.F431.D4q.NFq

open CFSG.ComponentClassification.RankTwoExceptional.D4 CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.Quasithin.H13.F431.D4q.Struct
open scoped commutatorElement


set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
  (hσ : ∀ c, σ (σ (σ c)) = c)

theorem vc_add_self (a : Vc σ) : a + a = 0 := by
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ (Prod.ext ?_ (Subtype.ext ?_)))
  · exact CharTwo.add_self_eq_zero _
  · exact CharTwo.add_self_eq_zero _
  · exact CharTwo.add_self_eq_zero _
  · exact CharTwo.add_self_eq_zero _

include hσ in
theorem Zg_le_Qg : d4Zz K σ ≤ d4Vr K σ := fun g hg => by
  obtain ⟨f, rfl⟩ := (mem_Zg_iff σ hσ).1 hg
  exact vmk_mem σ hσ 0 f

include hσ in
theorem commutator_mem_Zg {x y : ModGL TwistTag.D4.tag K} (hx : x ∈ d4Vr K σ)
    (hy : y ∈ d4Vr K σ) : ⁅x, y⁆ ∈ d4Zz K σ := by
  have hc : ⁅x, y⁆ ∈ d4Vr K σ := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  obtain ⟨a, f, rfl⟩ := exists_vmk σ hσ hx
  obtain ⟨b, f', rfl⟩ := exists_vmk σ hσ hy
  obtain ⟨c, F, hcF⟩ := exists_vmk σ hσ hc
  have h1 : vmk σ a f * vmk σ b f' = ⁅vmk σ a f, vmk σ b f'⁆ * (vmk σ b f' * vmk σ a f) := by
    simp only [commutatorElement_def]
    group
  rw [hcF, vmk_mul σ hσ, vmk_mul σ hσ, vmk_mul σ hσ] at h1
  obtain ⟨h2, -⟩ := vmk_inj σ h1
  have hc0 : c = 0 := by
    have h3 : c + (a + b) = a + b := by
      rw [add_comm b a] at h2
      exact h2.symm
    exact add_eq_right.mp h3
  rw [hcF, hc0]
  exact (mem_Zg_iff σ hσ).2 ⟨F, rfl⟩

include hσ in
theorem sq_mem_Zg {x : ModGL TwistTag.D4.tag K} (hx : x ∈ d4Vr K σ) : x * x ∈ d4Zz K σ := by
  obtain ⟨a, f, rfl⟩ := exists_vmk σ hσ hx
  rw [vmk_mul σ hσ, vc_add_self σ a]
  exact (mem_Zg_iff σ hσ).2 ⟨_, rfl⟩

include hσ in
theorem Zg_central_Qg {x z : ModGL TwistTag.D4.tag K} (hx : x ∈ d4Vr K σ) (hz : z ∈ d4Zz K σ) :
    x * z = z * x := by
  obtain ⟨a, f, rfl⟩ := exists_vmk σ hσ hx
  obtain ⟨f', rfl⟩ := (mem_Zg_iff σ hσ).1 hz
  have hb1 : beta σ hσ a 0 = 0 := Subtype.ext (by simp [beta, trT])
  have hb2 : beta σ hσ 0 a = 0 := Subtype.ext (by simp [beta, trT])
  rw [vmk_mul σ hσ, vmk_mul σ hσ, hb1, hb2, add_zero, zero_add, zero_add, zero_add,
    add_comm f f']

include hσ in
theorem Zg_central_U {u z : ModGL TwistTag.D4.tag K}
    (hu : u ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) (hz : z ∈ d4Zz K σ) :
    u * z = z * u := by
  obtain ⟨a, b, c, d, e, f, hb, he, hf, rfl⟩ := exists_d4coord σ (toRingHom_pow_three_d4 σ hσ) hu
  have hv : d4v K σ b c d e f ∈ d4Vr K σ :=
    d4v_mem_d4Vr σ (toRingHom_pow_three_d4 σ hσ) hb he hf
  obtain ⟨f', rfl⟩ := (mem_Zg_iff σ hσ).1 hz
  have h1 : d4x₁ K σ a * vmk σ 0 f' = vmk σ 0 f' * d4x₁ K σ a := by
    rw [← x6_eq_vmk]
    exact (commute_d4x₁_d4x₆ σ a f').eq
  rw [mul_assoc, Zg_central_Qg σ hσ hv ((mem_Zg_iff σ hσ).2 ⟨f', rfl⟩), ← mul_assoc, h1,
    mul_assoc]

include hσ in
theorem Qg_conj_U {u x : ModGL TwistTag.D4.tag K}
    (hu : u ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) (hx : x ∈ d4Vr K σ) :
    u * x * u⁻¹ ∈ d4Vr K σ := by
  have hN := graphFixedSimpleComplement_subgroupOf_normal (t := TwistTag.D4) (K := K)
    (σ := σ.toRingHom) ⟨0, by decide⟩
  exact hN.conj_mem ⟨x, graphFixedSimpleComplement_le _ hx⟩ hx ⟨u, hu⟩

include hσ in
theorem commutator_U_mem_Qg {s t : ModGL TwistTag.D4.tag K}
    (hs : s ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)
    (ht : t ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) : ⁅s, t⁆ ∈ d4Vr K σ := by
  have hσ3 := toRingHom_pow_three_d4 σ hσ
  obtain ⟨a, b, c, d, e, f, hb, he, hf, rfl⟩ := exists_d4coord σ hσ3 hs
  obtain ⟨a', b', c', d', e', f', hb', he', hf', rfl⟩ := exists_d4coord σ hσ3 ht
  have hQU := graphFixedSimpleComplement_le (t := TwistTag.D4) (K := K) (σ := σ.toRingHom)
    ⟨0, by decide⟩
  have hv0 : d4v K σ b c d e f ∈ d4Vr K σ := d4v_mem_d4Vr σ hσ3 hb he hf
  have hv := hQU hv0
  have hv0' : d4v K σ b' c' d' e' f' ∈ d4Vr K σ := d4v_mem_d4Vr σ hσ3 hb' he' hf'
  have hv' := hQU hv0'
  have hx : d4x₁ K σ a ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom := by
    simpa using mul_mem hs (inv_mem hv)
  have hy : d4x₁ K σ a' ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom := by
    simpa using mul_mem ht (inv_mem hv')
  set U := graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom with hU
  have hN : ((d4Vr K σ).subgroupOf U).Normal :=
    graphFixedSimpleComplement_subgroupOf_normal ⟨0, by decide⟩
  let π : ↥U →* ↥U ⧸ (d4Vr K σ).subgroupOf U := QuotientGroup.mk' ((d4Vr K σ).subgroupOf U)
  have h1 : ∀ (x v : ModGL TwistTag.D4.tag K) (hxv : x * v ∈ U) (hx : x ∈ U), v ∈ d4Vr K σ →
      π (⟨x * v, hxv⟩ : ↥U) = π (⟨x, hx⟩ : ↥U) := by
    intro x v hxv hx hv
    rw [eq_comm, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    show (x⁻¹ * (x * v)) ∈ d4Vr K σ
    rw [inv_mul_cancel_left]
    exact hv
  have hcomm : ⁅(⟨d4x₁ K σ a, hx⟩ : ↥U), (⟨d4x₁ K σ a', hy⟩ : ↥U)⁆ = 1 := by
    apply Subtype.ext
    show ⁅d4x₁ K σ a, d4x₁ K σ a'⁆ = 1
    rw [commutatorElement_eq_one_iff_mul_comm, ← d4x₁_add σ, ← d4x₁_add σ, add_comm]
  have h2 : π ⁅(⟨d4x₁ K σ a * d4v K σ b c d e f, hs⟩ : ↥U),
      (⟨d4x₁ K σ a' * d4v K σ b' c' d' e' f', ht⟩ : ↥U)⁆ = 1 := by
    rw [map_commutatorElement, h1 _ _ hs hx hv0, h1 _ _ ht hy hv0', ← map_commutatorElement,
      hcomm, map_one]
  have h3 : ⁅(⟨d4x₁ K σ a * d4v K σ b c d e f, hs⟩ : ↥U),
      (⟨d4x₁ K σ a' * d4v K σ b' c' d' e' f', ht⟩ : ↥U)⁆ ∈ (d4Vr K σ).subgroupOf U :=
    (QuotientGroup.eq_one_iff _).1 h2
  exact h3

end CFSG.Quasithin.H13.F431.D4q.NFq
