module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Core
public import CFSG.SignalizerFunctorTheorem.McBride.Models.Unitary.Order72

public section

open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.UnitaryFrame

variable {Y : Type*} [Group Y]

structure FixedData (C P : Subgroup Y) : Prop where
  card_C : Nat.card C = 72
  le : P ≤ C
  card_P : Nat.card P = 9
  pow_three : ∀ x ∈ P, x ^ 3 = 1
  normalizes : ∀ c ∈ C, ∀ x ∈ P, c * x * c⁻¹ ∈ P
  mem_of_commute : ∀ c ∈ C, ∀ x ∈ P, x ≠ 1 → c * x = x * c → c ∈ P
  trans : ∀ x ∈ P, x ≠ 1 → ∀ y ∈ P, y ≠ 1 → ∃ c ∈ C, c * x * c⁻¹ = y
  fitting : CFSG.fittingSubgroupOf C = P
  exists_central : ∃ z ∈ C, z ∉ P ∧ ∀ x ∈ C, ⁅z, x⁆ ∈ P
  normal_le : ∀ N : Subgroup Y, N ≤ C → (N.subgroupOf C).Normal → N ≠ ⊥ → P ≤ N
  no_klein : ∀ u ∈ C, ∀ v ∈ C, orderOf u = 2 → orderOf v = 2 → u * v = v * u → u = v
  exists_sq_ne_one : ∀ T : Subgroup Y, T ≤ C → Nat.card T = 8 → ∃ x ∈ T, x ^ 2 ≠ 1
  two_dvd_orderOf : ∀ c ∈ C, c ∉ P → 2 ∣ orderOf c

theorem exists_fixedData {C : Subgroup Y} [Finite C] (h : Order72 C) :
    ∃ P : Subgroup Y, FixedData C P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 C) := inferInstance
  have hsub := h.subsingleton_sylow_three
  have hn : (P : Subgroup C).Normal := Sylow.normal_of_subsingleton P
  have hcardP := h.card_sylow_three P
  have hinj : Function.Injective C.subtype := C.subtype_injective
  refine ⟨(P : Subgroup C).map C.subtype, ?_⟩
  refine
    { card_C := h.card
      le := Subgroup.map_subtype_le _
      card_P := ?_
      pow_three := ?_
      normalizes := ?_
      mem_of_commute := ?_
      trans := ?_
      fitting := ?_
      exists_central := ?_
      normal_le := ?_
      no_klein := ?_
      exists_sq_ne_one := ?_
      two_dvd_orderOf := ?_ }
  · rw [Subgroup.card_map_of_injective hinj, hcardP]
  · rintro _ ⟨x, hx, rfl⟩
    exact congrArg Subtype.val (h.pow_three_eq_one P hx)
  · rintro c hc _ ⟨x, hx, rfl⟩
    exact ⟨⟨c, hc⟩ * x * ⟨c, hc⟩⁻¹, hn.conj_mem x hx ⟨c, hc⟩, rfl⟩
  · rintro c hc _ ⟨x, hx, rfl⟩ hx1 hcx
    refine ⟨⟨c, hc⟩, h.mem_of_commute P hx (fun h1 => hx1 (by rw [h1]; rfl))
      (Subtype.ext hcx), rfl⟩
  · rintro _ ⟨x, hx, rfl⟩ hx1 _ ⟨y, hy, rfl⟩ hy1
    obtain ⟨c, hc⟩ := h.exists_conj_eq P hx (fun h1 => hx1 (by rw [h1]; rfl)) hy
      (fun h1 => hy1 (by rw [h1]; rfl))
    exact ⟨c, c.2, congrArg Subtype.val hc⟩
  · have := h.fittingSubgroup_eq P
    unfold CFSG.fittingSubgroupOf
    rw [this]
  · obtain ⟨z, hzP, hz⟩ := h.exists_central_quotient P
    refine ⟨z, z.2, fun hzmem => hzP ?_, fun x hx => ?_⟩
    · obtain ⟨z', hz', hzz'⟩ := hzmem
      have : z' = z := Subtype.ext hzz'
      exact this ▸ hz'
    · exact ⟨⁅z, ⟨x, hx⟩⁆, hz _, rfl⟩
  · intro N hNC hNn hN1
    have hN1' : N.subgroupOf C ≠ ⊥ := by
      intro hbot
      apply hN1
      rw [← Subgroup.map_subgroupOf_eq_of_le hNC, hbot, Subgroup.map_bot]
    have := h.le_of_normal P hNn hN1'
    calc (P : Subgroup C).map C.subtype ≤ (N.subgroupOf C).map C.subtype :=
          Subgroup.map_mono this
      _ = N := Subgroup.map_subgroupOf_eq_of_le hNC
  · intro u hu v hv hu2 hv2 huv
    have := h.eq_of_commute_involutions (u := ⟨u, hu⟩) (v := ⟨v, hv⟩)
      (by rw [Subgroup.orderOf_mk, hu2]) (by rw [Subgroup.orderOf_mk, hv2])
      (Subtype.ext huv)
    exact congrArg Subtype.val this
  · intro T hTC hT8
    have hT' : Nat.card (T.subgroupOf C) = 8 := by
      rw [← hT8]
      exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTC).toEquiv)
    obtain ⟨x, hx, hx2⟩ := h.exists_sq_ne_one hT'
    exact ⟨x, hx, fun h1 => hx2 (Subtype.ext h1)⟩
  · intro c hc hcP
    have h2 := h.two_dvd_orderOf_of_not_mem P (x := ⟨c, hc⟩) (fun hmem => hcP ⟨_, hmem, rfl⟩)
    rwa [Subgroup.orderOf_mk] at h2

end CFSG.SignalizerFunctorTheorem.McBride.UnitaryFrame
