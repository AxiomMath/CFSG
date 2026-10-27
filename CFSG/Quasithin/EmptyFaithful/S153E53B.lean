module

public import CFSG.Quasithin.EmptyFaithful.S153E53A

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E

section Two53

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem not_le_S_of_nonabelian (cx : Ctx15350 T Mc M V₁ V₂ t) (h52 : Concl15352 cx) :
    ¬ UH153 T M V₁ Mc ≤ Sgp153 T V₁ := by
  intro hUS
  obtain ⟨a, ha, b, hb, hne⟩ := h52
  exact hne (B2F.isElemAbelian_comm (isElemAbelian_U_of_le_S cx hUS) ha hb)

theorem lemma_15_3_53_two (cx : Ctx15350 T Mc M V₁ V₂ t) (h51 : Concl15351 cx)
    (h52 : Concl15352 cx) : Concl15353Two cx := by
  have hV := cx.c.hyp.elemAbelian
  have h1 := h51.one
  have hUS := not_le_S_of_nonabelian cx h52
  obtain ⟨hcomm, hc8⟩ := commV_autI_U_eq_perp cx h1 hUS
  let P : Subgroup G := (perpSub (qW_spec cx).1 (fixV (autI hV T))).map (inclMod hV)
  have hP8 : Nat.card ↥P = 8 := by
    rw [Subgroup.card_map_of_injective (inclMod_injective hV), ← hcomm]
    exact hc8
  have hUV : ⁅UH153 T M V₁ Mc, VZ T M⁆ = P := by
    rw [Subgroup.commutator_comm, commutator_eq_map_commV hV (U_le_N cx), hcomm]
  have hPVU : P ≤ VZ T M ⊓ UH153 T M V₁ Mc := by
    rw [← hUV, Subgroup.commutator_comm]
    exact four_U cx
  have hVUQ : VZ T M ⊓ UH153 T M V₁ Mc ≤ VZ T M ⊓ pCoreOf 2 Mc :=
    inf_le_inf_left _ (U_le_Q cx)
  have hV16 : Nat.card ↥(VZ T M) = 16 := cx.c.hyp.card_VZ
  have hVQ_card : Nat.card ↥(VZ T M ⊓ pCoreOf 2 Mc) = 8 := by
    have hd1 : 8 ∣ Nat.card ↥(VZ T M ⊓ pCoreOf 2 Mc) := by
      rw [← hP8]
      exact Subgroup.card_dvd_of_le (hPVU.trans hVUQ)
    have hd2 : Nat.card ↥(VZ T M ⊓ pCoreOf 2 Mc) ≤ 16 := by
      rw [← hV16]
      exact Subgroup.card_le_of_le inf_le_left
    have hne16 : Nat.card ↥(VZ T M ⊓ pCoreOf 2 Mc) ≠ 16 := by
      intro h16
      apply h1
      have : VZ T M ⊓ pCoreOf 2 Mc = VZ T M :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h16, hV16])
      rw [← this]
      exact inf_le_right
    have hd3 : 8 ≤ Nat.card ↥(VZ T M ⊓ pCoreOf 2 Mc) := by
      rw [← hP8]
      exact Subgroup.card_le_of_le (hPVU.trans hVUQ)
    omega
  have hVQ : VZ T M ⊓ pCoreOf 2 Mc = P :=
    (Subgroup.eq_of_le_of_card_ge (hPVU.trans hVUQ) (by rw [hVQ_card, hP8])).symm
  have hVU : VZ T M ⊓ UH153 T M V₁ Mc = P :=
    (Subgroup.eq_of_le_of_card_ge hPVU
      (by rw [hP8]; exact (Subgroup.card_le_of_le hVUQ).trans hVQ_card.le)).symm
  have hperp : IsPerp153 cx.c (quasithinOmegaOneCenter T) P := by
    intro v
    constructor
    · intro hv
      obtain ⟨w, hw, rfl⟩ := (mem_map_inclMod_iff hV).1 hv
      refine ⟨w.val_mem, fun a ha => ?_⟩
      have haV : a ∈ VZ T M := (cx.c.hyp.lemma_15_3_2_two.1 ▸ ha : a ∈ VZ T M ⊓
        Subgroup.centralizer (T : Set G)).1
      have hz : (⟨a, haV⟩ : IntMod (VZ T M) hV) ∈ fixV (autI hV T) :=
        (mem_fixV_autI_T_iff cx _).2 ha
      exact ⟨haV, w.val_mem, (mem_perpSub (qW_spec cx).1).1 hw _ hz⟩
    · rintro ⟨hv, hort⟩
      refine (mem_map_inclMod_iff hV).2 ⟨IntMod.mk hV ⟨v, hv⟩, ?_, rfl⟩
      rw [mem_perpSub]
      intro z hz
      have hzZ : z.val ∈ quasithinOmegaOneCenter T := (mem_fixV_autI_T_iff cx z).1 hz
      obtain ⟨ha, hb, h0⟩ := hort _ hzZ
      exact h0
  refine ⟨⟨P, hperp, hVQ, hVU, hUV⟩, ?_⟩
  have e := Subgroup.relIndex_mul_card (VZ T M ⊓ pCoreOf 2 Mc) (VZ T M)
  rw [inf_eq_left.2 (inf_le_left : VZ T M ⊓ pCoreOf 2 Mc ≤ VZ T M), hVQ_card, hV16] at e
  omega

end Two53

end S153E

end CFSG.Quasithin
