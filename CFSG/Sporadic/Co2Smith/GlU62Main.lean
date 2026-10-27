module

public import CFSG.Sporadic.Co2Smith.GlU62Ext

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
  CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.CurtisTits
  CFSG.Sporadic.Co2Rank3

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {G : Type} [Group G] {z : G}
  {φ : centralizer ({z} : Set G) ≃* Cz} {ρ : C0c →* G}

theorem extFun_mul
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ) {a b : K} (ha : a ∈ G1c)
    (hb : b ∈ G1c) : extFun hz hm (a * b) = extFun hz hm a * extFun hz hm b := by
  have hd := rhoK_δ1hK_sq (ρ := ρ)
  have hδ := δ1hK_mul_self
  have hiff := mul_mem_G0c_iff ha hb
  by_cases hA : a ∈ G0c <;> by_cases hB : b ∈ G0c
  · rw [extFun_of_mem hz hm (G0c.mul_mem hA hB), extFun_of_mem hz hm hA, extFun_of_mem hz hm hB,
      psi0Inv_mul hz hm hA hB]
  · have hAB : a * b ∉ G0c := fun h => hB ((hiff.1 h).1 hA)
    have hbδ := (mem_G0c_or_mul_δ1hK hb).resolve_left hB
    rw [extFun_of_not_mem hz hm hAB, extFun_of_mem hz hm hA, extFun_of_not_mem hz hm hB,
      mul_assoc a b, psi0Inv_mul hz hm hA hbδ, mul_assoc]
  · have hAB : a * b ∉ G0c := fun h => hA ((hiff.1 h).2 hB)
    have haδ := (mem_G0c_or_mul_δ1hK ha).resolve_left hA
    obtain ⟨hδb, hconj⟩ := psi0Inv_conj hz hm hB
    rw [extFun_of_not_mem hz hm hAB, extFun_of_not_mem hz hm hA, extFun_of_mem hz hm hB]
    calc psi0Inv hz hm (a * b * δ1hK) * rhoK ρ δ1hK
        = psi0Inv hz hm (a * δ1hK * (δ1hK * b * δ1hK)) * rhoK ρ δ1hK := by
          rw [show a * δ1hK * (δ1hK * b * δ1hK) = a * (δ1hK * δ1hK) * b * δ1hK by group, hδ,
            mul_one]
      _ = psi0Inv hz hm (a * δ1hK) * (rhoK ρ δ1hK * psi0Inv hz hm b * rhoK ρ δ1hK) *
            rhoK ρ δ1hK := by rw [psi0Inv_mul hz hm haδ hδb, hconj]
      _ = psi0Inv hz hm (a * δ1hK) * rhoK ρ δ1hK * psi0Inv hz hm b := by
          rw [show psi0Inv hz hm (a * δ1hK) * (rhoK ρ δ1hK * psi0Inv hz hm b * rhoK ρ δ1hK) *
            rhoK ρ δ1hK = psi0Inv hz hm (a * δ1hK) * rhoK ρ δ1hK * psi0Inv hz hm b *
              (rhoK ρ δ1hK * rhoK ρ δ1hK) by group, hd, mul_one]
  · have hAB : a * b ∈ G0c := hiff.2 (iff_of_false hA hB)
    have haδ := (mem_G0c_or_mul_δ1hK ha).resolve_left hA
    have hbδ := (mem_G0c_or_mul_δ1hK hb).resolve_left hB
    obtain ⟨hδbδ, hconj⟩ := psi0Inv_conj hz hm hbδ
    rw [extFun_of_mem hz hm hAB, extFun_of_not_mem hz hm hA, extFun_of_not_mem hz hm hB]
    calc psi0Inv hz hm (a * b)
        = psi0Inv hz hm (a * δ1hK * (δ1hK * (b * δ1hK) * δ1hK)) := by
          rw [show a * δ1hK * (δ1hK * (b * δ1hK) * δ1hK) =
            a * (δ1hK * δ1hK) * b * (δ1hK * δ1hK) by group, hδ, mul_one, mul_one]
      _ = psi0Inv hz hm (a * δ1hK) *
            (rhoK ρ δ1hK * psi0Inv hz hm (b * δ1hK) * rhoK ρ δ1hK) := by
          rw [psi0Inv_mul hz hm haδ hδbδ, hconj]
      _ = psi0Inv hz hm (a * δ1hK) * rhoK ρ δ1hK * (psi0Inv hz hm (b * δ1hK) * rhoK ρ δ1hK) := by
          group

@[expose] noncomputable def extG
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ) :
    G1c →* G where
  toFun k := extFun hz hm k
  map_one' := by
    rw [Subgroup.coe_one, extFun_of_mem hz hm G0c.one_mem, psi0Inv_one]
  map_mul' a b := extFun_mul hz hm a.2 b.2

theorem extG_apply
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ) (k : G1c) :
    extG hz hm k = extFun hz hm k := rfl

theorem extG_injective
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ) :
    Function.Injective (extG hz hm) := by
  rw [injective_iff_map_eq_one]
  intro k hk
  rw [extG_apply] at hk
  by_cases h : (k : K) ∈ G0c
  · rw [extFun_of_mem hz hm h] at hk
    exact Subtype.ext (psi0Inv_injOn hz hm h hk)
  · exfalso
    rw [extFun_of_not_mem hz hm h, mul_eq_one_iff_inv_eq] at hk
    apply rhoK_δ1hK_not_mem hz hm
    rw [← hk]
    exact (thetaG hz hm).range.inv_mem (psi0Inv_mem hz hm ((k : K) * δ1hK))

end CFSG.Sporadic.Co2Smith
