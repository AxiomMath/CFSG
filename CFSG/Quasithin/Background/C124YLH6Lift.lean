module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

public section

namespace CFSG.Quasithin.C124.YL.H6

open Subgroup

theorem central_not_mem_commutator {H : Type*} [Group H] [Finite H] (P : Subgroup H)
    [IsMulCommutative P] (z : H) (hzc : z ∈ Subgroup.center H)
    (hidx : Nat.Coprime (orderOf z) P.index) (hz1 : z ≠ 1) : z ∉ commutator H := by
  intro hz
  have hfin : P.FiniteIndex := inferInstance
  let V : H →* Abelianization P := MonoidHom.transfer (Abelianization.of : P →* Abelianization P)
  have key : ∀ (k : ℕ) (g₀ : H), g₀⁻¹ * z ^ k * g₀ ∈ P → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hc : z ^ k ∈ Subgroup.center H := Subgroup.pow_mem _ hzc k
    rw [Subgroup.mem_center_iff] at hc
    rw [mul_assoc, ← hc g₀]
    simp
  have h1 : V z = Abelianization.of ⟨z ^ P.index, MonoidHom.transfer_eq_pow_aux z key⟩ := by
    exact MonoidHom.transfer_eq_pow (Abelianization.of : P →* Abelianization P) z key
  have h2 : V z = 1 := by
    have : commutator H ≤ V.ker := Abelianization.commutator_subset_ker V
    exact this hz
  rw [h1] at h2
  have h3 : (⟨z ^ P.index, MonoidHom.transfer_eq_pow_aux z key⟩ : P) ∈ commutator P := by
    rw [← Abelianization.ker_of]
    exact h2
  rw [_root_.commutator_eq_bot, Subgroup.mem_bot] at h3
  have h4 : z ^ P.index = 1 := congrArg Subtype.val h3
  have h5 : orderOf z ∣ P.index := orderOf_dvd_of_pow_eq_one h4
  have h6 : orderOf z = 1 := Nat.Coprime.eq_one_of_dvd hidx h5
  exact hz1 (orderOf_eq_one_iff.1 h6)

variable {Γ : Type*} [Group Γ]

theorem commutator_subgroup_eq_map (Hh : Subgroup Γ) :
    ⁅Hh, Hh⁆ = (commutator ↥Hh).map Hh.subtype :=
  (Subgroup.map_subtype_commutator Hh).symm

theorem central_not_mem_commutator_sub [Finite Γ] (Hh : Subgroup Γ) (P : Subgroup ↥Hh)
    [IsMulCommutative P] (z : Γ) (hzH : z ∈ Hh) (hzc : z ∈ Subgroup.center Γ)
    (hidx : Nat.Coprime (orderOf z) P.index) (hz1 : z ≠ 1) : z ∉ ⁅Hh, Hh⁆ := by
  intro hz
  rw [commutator_subgroup_eq_map] at hz
  obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.1 hz
  have hwe : w = ⟨z, hzH⟩ := Subtype.ext hwz
  rw [hwe] at hw
  have hc : (⟨z, hzH⟩ : ↥Hh) ∈ Subgroup.center ↥Hh := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.1 hzc g)
  have hord : orderOf (⟨z, hzH⟩ : ↥Hh) = orderOf z := by
    rw [← Subgroup.orderOf_coe]
  refine central_not_mem_commutator P ⟨z, hzH⟩ hc (by rw [hord]; exact hidx) ?_ hw
  intro h
  exact hz1 (congrArg Subtype.val h)

theorem commutator_eq_self_of_equiv_alt_five {Y : Subgroup Γ}
    (e : ↥Y ≃* alternatingGroup (Fin 5)) : ⁅Y, Y⁆ = Y := by
  rw [commutator_subgroup_eq_map]
  have h5 : 5 ≤ Nat.card (Fin 5) := by simp
  have h : commutator ↥Y = ⊤ := by
    have h1 := commutator_alternatingGroup_eq_top h5
    have h2 : (commutator (alternatingGroup (Fin 5))).map e.symm.toMonoidHom = commutator ↥Y := by
      rw [_root_.commutator, _root_.commutator, Subgroup.map_commutator, Subgroup.map_top,
        MonoidHom.range_eq_top_of_surjective _ e.symm.surjective]
    rw [← h2, h1, Subgroup.map_top, MonoidHom.range_eq_top_of_surjective _ e.symm.surjective]
  rw [h, Subgroup.map_top, Subgroup.range_subtype]

end CFSG.Quasithin.C124.YL.H6
