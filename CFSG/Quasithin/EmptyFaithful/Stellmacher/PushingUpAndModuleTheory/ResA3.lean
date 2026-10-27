module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResA1

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CosetGeom Equiv

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace ConfR

variable {δ μ : Geo H M} {U : Subgroup G}

theorem card_P_R (hA : F53Amalgam H M S) (h : ConfR δ μ U) :
    Nat.card (Qv μ) = 2 * Nat.card (pCoreOf 2 U) := by
  obtain ⟨-, h2, -, -⟩ := h.sig.counts hA h.normal_P h.hR
  have h3 : (pCoreOf 2 U).relIndex (Qv μ ⊓ U) * Nat.card (pCoreOf 2 U) =
      Nat.card (Qv μ ⊓ U : Subgroup G) := by
    have := Subgroup.relIndex_mul_card (pCoreOf 2 U) (Qv μ ⊓ U)
    rwa [inf_of_le_left (h.sig.R_le_P)] at this
  rw [h2, h.inf_eq] at h3
  omega

theorem card_R_K (hA : F53Amalgam H M S) (h : ConfR δ μ U) :
    Nat.card (pCoreOf 2 U) = 2 * Nat.card (Qv δ) := by
  obtain ⟨-, -, h3, -⟩ := h.sig.counts hA h.normal_P h.hR
  have hK : Qv δ ≤ pCoreOf 2 U := h.sig.inf_Qv_le_R.trans' (le_inf (h.hQδ.trans h.hQ) le_rfl)
  rw [h.inf_eq, inf_of_le_right h.hQδ] at h3
  have h4 : (Qv δ).relIndex (pCoreOf 2 U) * Nat.card (Qv δ ⊓ pCoreOf 2 U : Subgroup G) =
      Nat.card (pCoreOf 2 U) := Subgroup.relIndex_mul_card (Qv δ) (pCoreOf 2 U)
  rw [inf_of_le_left hK, h3] at h4
  omega

theorem card_U_K (hA : F53Amalgam H M S) (h : ConfR δ μ U) :
    Nat.card U = 12 * Nat.card (Qv δ) := by
  rw [h.card_U hA, h.card_P_R hA, h.card_R_K hA]; ring

end ConfR

namespace SFourC

variable {U T C : Subgroup G} (eT : ↥T ≃* Perm (Fin 4))

@[expose] def tau : Perm (Fin 4) →* G := T.subtype.comp eT.symm.toMonoidHom

theorem tau_apply (x : Perm (Fin 4)) : tau eT x = ((eT.symm x : ↥T) : G) := rfl

theorem tau_injective : Function.Injective (tau eT) := by
  intro x y hxy
  have := Subtype.ext hxy
  simpa using this

theorem tau_mem (x : Perm (Fin 4)) : tau eT x ∈ T := (eT.symm x).2

theorem mem_T_eq (t : G) (ht : t ∈ T) : tau eT (eT ⟨t, ht⟩) = t := by
  rw [tau_apply]; simp

end SFourC

namespace ConfR
open SFourC

theorem R_le_VC {U T C : Subgroup G} (hS : SFourC U T C)
    (eT : ↥T ≃* Perm (Fin 4)) {x : G} (hx : x ∈ pCoreOf 2 U) :
    ∃ w ∈ klein4, ∃ z ∈ C, x = tau eT w * z := by
  have hxU : x ∈ U := (CFSG.LieType.BorelTits.pCoreOf_le 2 U) hx
  obtain ⟨t, ht, z, hz, rfl⟩ := mem_sup_of_commute hS.comm (hS.sup ▸ hxU)
  refine ⟨eT ⟨t, ht⟩, ?_, z, hz, by rw [mem_T_eq eT t ht]⟩
  by_contra hw
  obtain ⟨g, hg⟩ := exists_not_pow_eight _ hw
  apply hg
  set gt : ↥T := eT.symm g with hgt
  have hgU : (gt : G) ∈ U := hS.le_T gt.2
  have hnormR : U ≤ Subgroup.normalizer (pCoreOf 2 U : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 U
  have hx' : (gt : G) * (t * z) * (gt : G)⁻¹ ∈ pCoreOf 2 U :=
    (Subgroup.mem_normalizer_iff.mp (hnormR hgU) _).mp hx
  have hxx : (t * z) * ((gt : G) * (t * z) * (gt : G)⁻¹) ∈ pCoreOf 2 U := Subgroup.mul_mem _ hx hx'
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) U ⟨_, hxx⟩
  have hk' : ((t * z) * ((gt : G) * (t * z) * (gt : G)⁻¹)) ^ 2 ^ k = 1 := by
    simpa using congrArg Subtype.val hk
  set tg : G := (gt : G) * t * (gt : G)⁻¹ with htg
  have htgT : tg ∈ T := T.mul_mem (T.mul_mem gt.2 ht) (T.inv_mem gt.2)
  have hzgt : (gt : G) * z = z * (gt : G) := hS.comm _ gt.2 z hz
  have hform : (t * z) * ((gt : G) * (t * z) * (gt : G)⁻¹) = (t * tg) * (z * z) := by
    have : (gt : G) * (t * z) * (gt : G)⁻¹ = tg * z := by
      rw [htg]
      calc (gt : G) * (t * z) * (gt : G)⁻¹ = (gt : G) * t * ((gt : G)⁻¹ * (gt : G)) * z * (gt : G)⁻¹ := by group
        _ = (gt : G) * t * (z * (gt : G)⁻¹ ) := by
          have : (gt : G)⁻¹ * (gt : G) = 1 := inv_mul_cancel _
          rw [this]; group
        _ = _ := by
          have : z * (gt : G)⁻¹ = (gt : G)⁻¹ * z := by
            rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hzgt]; group
          rw [this]; group
    rw [this]
    have h2 : tg * z = z * tg := hS.comm _ htgT z hz
    have h3 : t * z = z * t := hS.comm _ ht z hz
    calc t * z * (tg * z) = t * (z * tg) * z := by group
      _ = t * (tg * z) * z := by rw [h2]
      _ = t * tg * (z * z) := by group
  rw [hform] at hk'
  have hcomm : Commute (t * tg) (z * z) := by
    have h1 := hS.comm _ (T.mul_mem ht htgT) z hz
    exact (Commute.mul_right h1 h1)
  rw [hcomm.mul_pow] at hk'
  have hz2 : (z * z) ^ 2 ^ k ∈ C := C.pow_mem (C.mul_mem hz hz) _
  have hT2 : (t * tg) ^ 2 ^ k ∈ T := T.pow_mem (T.mul_mem ht htgT) _
  have hinv : (t * tg) ^ 2 ^ k = ((z * z) ^ 2 ^ k)⁻¹ := eq_inv_of_mul_eq_one_left hk'
  have hone : (t * tg) ^ 2 ^ k = 1 := by
    have hmem : (t * tg) ^ 2 ^ k ∈ T ⊓ C := ⟨hT2, hinv ▸ C.inv_mem hz2⟩
    rw [hS.inf] at hmem
    exact Subgroup.mem_bot.mp hmem
  have h5 : ((⟨t * tg, T.mul_mem ht htgT⟩ : ↥T)) ^ 2 ^ k = 1 := Subtype.ext hone
  have h6 := congrArg eT h5
  rw [map_pow, map_one] at h6
  have h7 : eT ⟨t * tg, T.mul_mem ht htgT⟩ = eT ⟨t, ht⟩ * (g * eT ⟨t, ht⟩ * g⁻¹) := by
    have : (⟨t * tg, T.mul_mem ht htgT⟩ : ↥T) = ⟨t, ht⟩ * (gt * ⟨t, ht⟩ * gt⁻¹) := rfl
    rw [this, map_mul, map_mul, map_mul, hgt, MulEquiv.apply_symm_apply, map_inv, MulEquiv.apply_symm_apply]
  rw [h7] at h6
  exact pow_eight_of_two_pow h6

variable {δ μ : Geo H M} {U T C : Subgroup G}

theorem index_K (hA : F53Amalgam H M S) (h : ConfR δ μ U) :
    ((Qv δ).subgroupOf U).index = 12 := by
  have hKU : Qv δ ≤ U := h.hQδ.trans h.hQ
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ((Qv δ).subgroupOf U)
  have h2 : Nat.card ↥((Qv δ).subgroupOf U) = Nat.card (Qv δ) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKU).toEquiv
  have h3 := h.card_U_K hA
  have hpos : 0 < Nat.card (Qv δ) := Nat.card_pos
  rw [h2, h3] at h1
  have : 12 * Nat.card (Qv δ) = ((Qv δ).subgroupOf U).index * Nat.card (Qv δ) := h1
  exact (Nat.eq_of_mul_eq_mul_right hpos this).symm

theorem tau_mem_stab (hS : SFourC U T C) (h : ConfR δ μ U) (eT : ↥T ≃* Perm (Fin 4))
    (x : Perm (Fin 4)) : tau eT x ∈ stab δ := h.sig.le_stab (hS.le_T (tau_mem eT x))

theorem klein4_le_Qv (hA : F53Amalgam H M S) (h : ConfR δ μ U) (hS : SFourC U T C)
    (eT : ↥T ≃* Perm (Fin 4)) : ∀ w ∈ klein4, tau eT w ∈ Qv δ := by
  set N' : Subgroup (Perm (Fin 4)) := (Qv δ).comap (tau eT) with hN'
  have hnorm : N'.Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hx' : tau eT x ∈ Qv δ := hx
    show tau eT (g * x * g⁻¹) ∈ Qv δ
    rw [map_mul, map_mul, map_inv]
    have := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (stab δ) (tau_mem_stab hS h eT g)
    exact (Subgroup.mem_normalizer_iff.mp this _).mp hx'
  have hp : IsPGroup 2 N' := by
    intro x
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (stab δ) ⟨tau eT x, x.2⟩
    refine ⟨k, Subtype.ext (tau_injective eT ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hne : N' ≠ ⊥ := by
    intro hbot
    have hKU : Qv δ ≤ U := h.hQδ.trans h.hQ
    let f : Perm (Fin 4) → ↥U ⧸ (Qv δ).subgroupOf U :=
      fun x => QuotientGroup.mk ⟨tau eT x, hS.le_T (tau_mem eT x)⟩
    have hf : Function.Injective f := by
      intro x y hxy
      have h1 := QuotientGroup.eq.mp hxy
      rw [Subgroup.mem_subgroupOf] at h1
      have h2 : tau eT (x⁻¹ * y) ∈ Qv δ := by simpa [map_mul, map_inv] using h1
      have h3 : x⁻¹ * y ∈ N' := h2
      rw [hbot, Subgroup.mem_bot] at h3
      exact inv_mul_eq_one.mp h3
    have h4 := Nat.card_le_card_of_injective f hf
    have h5 : Nat.card (↥U ⧸ (Qv δ).subgroupOf U) = 12 := index_K hA h
    rw [h5, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at h4
    revert h4
    decide
  intro w hw
  exact klein4_le_of_normal2 hp hne hw

end ConfR

end CFSG.Quasithin.F53
