module

public import CFSG.RankThree.PartTwo.Sec14.Wales1411WHJCore
import CFSG.RankThree.PartTwo.Sec14.Wales1411WHJInner
import CFSG.RankThree.PartTwo.Sec14.Wales1411WModels
import CFSG.GH74.GLS.C3.Layer1.Thm1AutA7
import CFSG.RankThree.PartTwo.KFacts.K412Conjugacy
import CFSG.RankThree.PartTwo.KFacts.K412Alternating

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo Equiv
open CFSG.GH74.GLS.C3.Layer1.Thm1 (psiEquiv psi_conj conj_injective_of_A7)

namespace Wales1411W.HJA7

variable {M : Type} [Group M] [Finite M] {Xbar : Subgroup M}

private theorem mem_alternatingGroup_of_pow_three {σ : Perm (Fin 7)} (hσ : σ ^ 3 = 1) :
    σ ∈ alternatingGroup (Fin 7) := by
  rw [Perm.mem_alternatingGroup]
  have h := congrArg Perm.sign hσ
  rw [map_pow, map_one] at h
  rcases Int.units_eq_one_or (Perm.sign σ) with h1 | h1
  · exact h1
  · rw [h1] at h
    exact absurd h (by decide)

theorem mem_range_conj (φ : ↥Xbar ≃* alternatingGroup (Fin 7)) {α : MulAut ↥Xbar}
    (hα : α ^ 3 = 1) : α ∈ (MulAut.conj : ↥Xbar →* MulAut ↥Xbar).range := by
  set σ := psiEquiv φ α with hσ
  have hσ3 : σ ^ 3 = 1 := by rw [hσ, ← map_pow, hα, map_one]
  have hσA := mem_alternatingGroup_of_pow_three hσ3
  refine ⟨φ.symm ⟨σ, hσA⟩, ?_⟩
  apply (psiEquiv φ).injective
  rw [psi_conj, MulEquiv.apply_symm_apply]

private theorem pow_nine_of_mem_eNine {x : Perm (Fin 7)} (hx : x ∈ KFacts.KP2.eNine) :
    x ^ 9 = 1 := by
  have h9 := KFacts.KP2.card_eNine
  have h := pow_card_eq_one' (G := ↥KFacts.KP2.eNine) (x := ⟨x, hx⟩)
  rw [h9] at h
  simpa using congrArg Subtype.val h

end Wales1411W.HJA7

open Wales1411W Wales1411W.HJA7 in
theorem ks1411HJCoreA7 : KS1411HJCoreA7 := by
  intro M _ _ Ybar Abar Xbar Rbar abar hset hX S T hS hT hST _
  obtain ⟨φ⟩ := hX
  haveI := HJInner.normal_X hset
  have hcen := conj_injective_of_A7 φ
  have hinner : ∀ α : MulAut ↥Xbar, α ^ 3 = 1 →
      α ∈ (MulAut.conj : ↥Xbar →* MulAut ↥Xbar).range := fun α hα => mem_range_conj φ hα
  have hAeq := HJInner.eq_inf_sup hset hcen hinner
  set E := (Abar ⊓ Xbar).subgroupOf Xbar with hE
  have hE9 : Nat.card E = 9 := by
    rw [hE, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
    exact HJInner.card_inf hset hcen hinner
  set EP := (E.map φ.toMonoidHom).map (alternatingGroup (Fin 7)).subtype with hEP
  have hEP9 : Nat.card EP = 9 := by
    rw [hEP, Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      Subgroup.card_map_of_injective φ.injective, hE9]
  obtain ⟨g, hg⟩ := KFacts.K412.exists_conj_eq_eNine hEP9
  have hcent : ∀ α : MulAut ↥Xbar,
      (∀ x : ↥Xbar, (x : M) ∈ Abar → α * MulAut.conj x = MulAut.conj x * α) →
      ¬ 3 ∣ orderOf α → α = 1 := by
    intro α hα h3
    set σ := psiEquiv φ α with hσ
    have hσC : g * σ * g⁻¹ ∈ Subgroup.centralizer (KFacts.KP2.eNine : Set (Perm (Fin 7))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      rw [← hg] at hp
      obtain ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩ := hp
      have hxA : ((x : ↥Xbar) : M) ∈ Abar := (Subgroup.mem_subgroupOf.mp hx).1
      have hcomm := congrArg (psiEquiv φ) (hα x hxA)
      rw [map_mul, map_mul, psi_conj] at hcomm
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype]
      rw [← hσ] at hcomm
      calc g * ((φ x : alternatingGroup (Fin 7)) : Perm (Fin 7)) * g⁻¹ * (g * σ * g⁻¹)
          = g * (((φ x : alternatingGroup (Fin 7)) : Perm (Fin 7)) * σ) * g⁻¹ := by group
        _ = g * (σ * ((φ x : alternatingGroup (Fin 7)) : Perm (Fin 7))) * g⁻¹ := by
            rw [hcomm]
        _ = g * σ * g⁻¹ * (g * ((φ x : alternatingGroup (Fin 7)) : Perm (Fin 7)) * g⁻¹) := by
            group
    rw [KFacts.K412.centralizer_eNine] at hσC
    have h9 : (g * σ * g⁻¹) ^ 9 = 1 := pow_nine_of_mem_eNine hσC
    have hσ9 : σ ^ 9 = 1 := by
      have : (g * σ * g⁻¹) ^ 9 = g * σ ^ 9 * g⁻¹ := by
        rw [show g * σ * g⁻¹ = MulAut.conj g σ from rfl, ← map_pow]
        rfl
      rw [this] at h9
      have h1 : σ ^ 9 = g⁻¹ * (g * σ ^ 9 * g⁻¹) * g := by group
      rw [h1, h9]
      group
    have hα9 : α ^ 9 = 1 := by
      apply (psiEquiv φ).injective
      rw [map_pow, ← hσ, hσ9, map_one]
    have hcop : Nat.Coprime (orderOf α) 9 := by
      have h := Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
      norm_num at h
      exact h.symm
    exact orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd (orderOf_dvd_of_pow_eq_one hα9))
  have hYX := HJInner.Y_eq_X hset hcen hinner hcent
  set c : MulAut (alternatingGroup (Fin 7)) := MulAut.conjNormal (H := alternatingGroup (Fin 7)) g
  have hmap : E.map (φ.trans c).toMonoidHom = Res5TypesA7.P7 := by
    apply Subgroup.map_injective (alternatingGroup (Fin 7)).subtype_injective
    rw [Res5TypesA7.P7, Subgroup.map_subgroupOf_eq_of_le KFacts.KP2.eNine_le_alternatingGroup,
      ← hg, hEP, Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hET : ETrans ↥Xbar E := ETrans.of_mulEquiv (φ := φ.trans c) hmap etrans_A7
  exact HJInner.conj_of_etrans2 hset hAeq hYX hET.etrans2 hS hT hST

end CFSG.RankThree.PartTwo.Sec14
