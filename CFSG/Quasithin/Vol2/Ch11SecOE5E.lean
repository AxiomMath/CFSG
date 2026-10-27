module

public import CFSG.Quasithin.Vol2.Ch11SecOE5D
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.OE5

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LinearGroups CFSG.RankThree.Classical CFSG.RankThree.PartOne.HNB

theorem card_psu35 : Nat.card (unitaryPSU hF25 3) = 126000 := by
  have h := (unitaryScalars hF25 3).card_eq_card_quotient_mul_card_subgroup
  rw [card_su35 hF25, card_unitaryScalars hF25 (by norm_num),
    show Nat.gcd 3 (5 ^ 1 + 1) = 3 by decide] at h
  show Nat.card (unitarySU 5 1 F25 3 ⧸ unitaryScalars hF25 3) = 126000
  omega

theorem pow_sixteen_of_mem {x : unitarySU 5 1 F25 3} (hx : x ∈ S0) : x ^ 16 = 1 := by
  have h := Subgroup.orderOf_dvd_natCard S0 hx
  rw [card_S0] at h
  exact orderOf_dvd_iff_pow_eq_one.mp h

theorem eq_one_of_mem_S0_ker {x : unitarySU 5 1 F25 3} (hx : x ∈ S0)
    (h1 : unitaryProj hF25 3 x = 1) : x = 1 := by
  have hZ : x ∈ unitaryScalars hF25 3 := by
    rw [← ker_unitaryProj]
    exact h1
  have h3 : orderOf x ∣ 3 := by
    have := Subgroup.orderOf_dvd_natCard _ hZ
    rwa [card_unitaryScalars hF25 (by norm_num), show Nat.gcd 3 (5 ^ 1 + 1) = 3 by decide]
      at this
  have h16 : orderOf x ∣ 16 := orderOf_dvd_of_pow_eq_one (pow_sixteen_of_mem hx)
  have := Nat.dvd_gcd h3 h16
  rw [show Nat.gcd 3 16 = 1 by decide, Nat.dvd_one, orderOf_eq_one_iff] at this
  exact this

theorem injective_S0 : Function.Injective ((unitaryProj hF25 3).comp S0.subtype) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  exact Subgroup.mem_bot.mpr (Subtype.ext (eq_one_of_mem_S0_ker x.2 hx))

theorem card_PS0 : Nat.card (S0.map (unitaryProj hF25 3)) = 16 := by
  have h : ((unitaryProj hF25 3).comp S0.subtype).range = S0.map (unitaryProj hF25 3) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← h, ← card_S0]
  exact (Nat.card_congr (MonoidHom.ofInjective injective_S0).toEquiv).symm

theorem isSylowTwoOf_PS0 : CFSG.QuasithinUnique.IsSylowTwoOf (S0.map (unitaryProj hF25 3)) ⊤ := by
  refine ⟨le_top, isPGroup_S0.map _, ?_⟩
  rw [show ((S0.map (unitaryProj hF25 3)).subgroupOf ⊤).index =
    (S0.map (unitaryProj hF25 3)).index from Subgroup.relIndex_top_right _]
  have h := (S0.map (unitaryProj hF25 3)).card_mul_index
  rw [card_PS0, card_psu35] at h
  omega

theorem invT_central {x : unitarySU 5 1 F25 3} (hx : x ∈ S0) :
    x * unitaryInvT hF25 = unitaryInvT hF25 * x := by
  have ha : aU * unitaryInvT hF25 = unitaryInvT hF25 * aU := by
    rw [← aU_pow_four]
    exact (Commute.self_pow aU 4).eq
  have hw : wU * unitaryInvT hF25 = unitaryInvT hF25 * wU := by
    apply mat_injective
    rw [mat_mul, mat_mul, mat_wU, show mat (unitaryInvT hF25) = negNegOneDiag F25 from
      coe_unitaryInvT hF25, wMat, negNegOneDiag, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have hle : S0 ≤ Subgroup.centralizer {unitaryInvT hF25} := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr ha
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hw
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)

theorem projInvT_central {x : unitaryPSU hF25 3} (hx : x ∈ S0.map (unitaryProj hF25 3)) :
    x * unitaryProj hF25 3 (unitaryInvT hF25) = unitaryProj hF25 3 (unitaryInvT hF25) * x := by
  obtain ⟨s, hs, rfl⟩ := hx
  rw [← map_mul, ← map_mul, invT_central hs]

theorem eq_of_central_PS0 {y : unitaryPSU hF25 3} (hy : y ∈ S0.map (unitaryProj hF25 3))
    (hc : ∀ x ∈ S0.map (unitaryProj hF25 3), x * y = y * x) :
    y = 1 ∨ y = unitaryProj hF25 3 (unitaryInvT hF25) := by
  obtain ⟨s, hs, rfl⟩ := hy
  have hcomm : ∀ x ∈ S0, s * x = x * s := by
    intro x hx
    have h1 := hc (unitaryProj hF25 3 x) ⟨x, hx, rfl⟩
    have hmem : s * x * s⁻¹ * x⁻¹ ∈ S0 :=
      S0.mul_mem (S0.mul_mem (S0.mul_mem hs hx) (S0.inv_mem hs)) (S0.inv_mem hx)
    have hker : unitaryProj hF25 3 (s * x * s⁻¹ * x⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h1]
      group
    have h2 := eq_one_of_mem_S0_ker hmem hker
    calc s * x = (s * x * s⁻¹ * x⁻¹) * (x * s) := by group
      _ = x * s := by rw [h2, one_mul]
  have ha := hcomm aU ((le_sup_left : Subgroup.zpowers aU ≤ S0) (Subgroup.mem_zpowers aU))
  have hw := hcomm wU ((le_sup_right : Subgroup.zpowers wU ≤ S0) (Subgroup.mem_zpowers wU))
  rcases eq_of_commute ha hw (pow_sixteen_of_mem hs) with h | h
  · left
    rw [h, map_one]
  · right
    rw [h]

end CFSG.Quasithin.Vol2.Ch11.SecS.OE5
