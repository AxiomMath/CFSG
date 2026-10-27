module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Conj
public import CFSG.RankThree.GF2n.DihedralCompl
public import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec2

open scoped commutatorElement
open CFSG.QuasithinUnique.Setup.X7

variable {X : Type*} [Group X] {N : Type*} [AddCommGroup N] [Module (ZMod 2) N] [Finite N]
  (ρ : Representation (ZMod 2) X N) {x : X}

theorem commSub_zpowers_eq_range (hx : x * x = 1) :
    commSub ρ (Subgroup.zpowers x) = LinearMap.range (ρ x - 1) := by
  refine le_antisymm ?_ (range_le_commSub (Subgroup.mem_zpowers x))
  refine iSup₂_le fun a ha => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have hk : (x : X) ^ k = 1 ∨ (x : X) ^ k = x := by
    have h2 : (x : X) ^ (2 : ℤ) = 1 := by rw [zpow_two, hx]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [← Int.emod_add_mul_ediv k 2, h, zero_add, zpow_mul, h2, one_zpow]
    · right
      rw [← Int.emod_add_mul_ediv k 2, h, zpow_add, zpow_mul, h2, one_zpow, mul_one, zpow_one]
  rcases hk with hk | hk
  · rw [hk]
    simp
  · rw [hk]

theorem commSub_zpowers_le_fixedSub_zpowers (hx : x * x = 1) :
    commSub ρ (Subgroup.zpowers x) ≤ fixedSub ρ (Subgroup.zpowers x) := by
  rw [commSub_zpowers_eq_range ρ hx, fixedSub_zpowers]
  rintro _ ⟨v, rfl⟩
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply]
  have h1 : (ρ x) ((ρ x) v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, hx, map_one, Module.End.one_apply]
  change (ρ x) ((ρ x) v - v) - ((ρ x) v - v) = 0
  rw [map_sub, h1]
  have hneg : (ρ x) v - v = -(v - (ρ x) v) := by abel
  rw [hneg, sub_neg_eq_add]
  exact CFSG.RankThree.GF2n.add_self_eq_zero_of_charTwo (ZMod 2) _

theorem natCard_fixedSub_zpowers_mul (hx : x * x = 1) :
    Nat.card (fixedSub ρ (Subgroup.zpowers x)) *
        Nat.card (commSub ρ (Subgroup.zpowers x)) = Nat.card N := by
  rw [fixedSub_zpowers, commSub_zpowers_eq_range ρ hx]
  rw [natCard_eq_two_pow_finrank, natCard_eq_two_pow_finrank,
    natCard_eq_two_pow_finrank, ← pow_add]
  congr 1
  have h := LinearMap.finrank_range_add_finrank_ker (ρ x - 1)
  omega

theorem natCard_le_natCard_fixedSub_zpowers_sq (hx : x * x = 1) :
    Nat.card N ≤ Nat.card (fixedSub ρ (Subgroup.zpowers x)) ^ 2 := by
  have hprod := natCard_fixedSub_zpowers_mul ρ hx
  have hle : Nat.card (commSub ρ (Subgroup.zpowers x)) ≤
      Nat.card (fixedSub ρ (Subgroup.zpowers x)) :=
    Nat.card_le_card_of_injective
      (Submodule.inclusion (commSub_zpowers_le_fixedSub_zpowers ρ hx))
      (Submodule.inclusion_injective _)
  calc Nat.card N = Nat.card (fixedSub ρ (Subgroup.zpowers x)) *
        Nat.card (commSub ρ (Subgroup.zpowers x)) := hprod.symm
    _ ≤ Nat.card (fixedSub ρ (Subgroup.zpowers x)) *
        Nat.card (fixedSub ρ (Subgroup.zpowers x)) := Nat.mul_le_mul_left _ hle
    _ = Nat.card (fixedSub ρ (Subgroup.zpowers x)) ^ 2 := by ring

theorem natCard_eq_natCard_fixedSub_zpowers_sq_iff (hx : x * x = 1) :
    Nat.card N = Nat.card (fixedSub ρ (Subgroup.zpowers x)) ^ 2 ↔
      commSub ρ (Subgroup.zpowers x) = fixedSub ρ (Subgroup.zpowers x) := by
  have hprod := natCard_fixedSub_zpowers_mul ρ hx
  constructor
  · intro h
    have hcancel : Nat.card (commSub ρ (Subgroup.zpowers x)) =
        Nat.card (fixedSub ρ (Subgroup.zpowers x)) := by
      apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := fixedSub ρ (Subgroup.zpowers x)))
      rw [hprod, h, pow_two]
    have hfr : Module.finrank (ZMod 2) (commSub ρ (Subgroup.zpowers x)) =
        Module.finrank (ZMod 2) (fixedSub ρ (Subgroup.zpowers x)) := by
      have h1 := natCard_eq_two_pow_finrank (commSub ρ (Subgroup.zpowers x))
      have h2 := natCard_eq_two_pow_finrank (fixedSub ρ (Subgroup.zpowers x))
      exact Nat.pow_right_injective (by norm_num : 1 < 2) (h1.symm.trans (hcancel.trans h2))
    exact Submodule.eq_of_le_of_finrank_eq
      (commSub_zpowers_le_fixedSub_zpowers ρ hx) hfr
  · intro h
    rw [h] at hprod
    rw [← hprod, pow_two]

theorem fixedSub_zpowers_conj {k : Type*} [Field k] {N' : Type*} [AddCommGroup N']
    [Module k N'] (ρ : Representation k X N') (g x : X) :
    fixedSub ρ (Subgroup.zpowers (g * x * g⁻¹)) =
      (fixedSub ρ (Subgroup.zpowers x)).map (ρ g) := by
  have hzp : (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom =
      Subgroup.zpowers (g * x * g⁻¹) := by
    rw [MonoidHom.map_zpowers]
    rfl
  rw [← hzp, fixedSub_map_conj]

theorem commSub_zpowers_conj (g x : X) :
    commSub ρ (Subgroup.zpowers (g * x * g⁻¹)) =
      (commSub ρ (Subgroup.zpowers x)).map (ρ g) := by
  have hzp : (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom =
      Subgroup.zpowers (g * x * g⁻¹) := by
    rw [MonoidHom.map_zpowers]
    rfl
  rw [← hzp, commSub_map_conj]

end CFSG.RankThree.GF2n.Tim81.Sec2
