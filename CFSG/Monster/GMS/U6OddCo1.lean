module

public import CFSG.Monster.GMS.U6OddReduce
public import CFSG.Monster.GMS.U6OddGroup
public import CFSG.Monster.GMS.S365Native
public import CFSG.Sporadic.Co1.Module.U6OddCert

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Co1.U6OddNative (u1 u2)
open CFSG.Sporadic.Co1.Module.U6Odd (U0 card_U0 finite_co1 norm_ex_five norm_ex_seven
  norm_ex_eleven s0_exists y₀_mem_cls conj_fix)
open CFSG.Sporadic.SmallF2 (toVecD)

namespace U6Odd

theorem u6Hyp :
    U6Hyp ↥U0 := by
  have hfin := finite_co1
  have hp2 : ¬ 5 ^ 2 ∣ Nat.card U0 := by rw [card_U0]; norm_num
  have hp7 : ¬ 7 ^ 2 ∣ Nat.card U0 := by rw [card_U0]; norm_num
  have hp11 : ¬ 11 ^ 2 ∣ Nat.card U0 := by rw [card_U0]; norm_num
  refine ⟨by rw [card_U0]; norm_num, ?_, ?_, ?_, ?_⟩
  · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨g, hg, hord, hD⟩ := norm_ex_five
    intro P hP N hN hodd
    exact odd_dvd_of_dvd_mul_two_pow 3 hodd
      (norm_field U0 hp2 hg hord hD P hP N hN : Nat.card N ∣ 15 * 2 ^ 3)
  · have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨g, hg, hord, hD⟩ := norm_ex_seven
    intro P hP N hN hodd
    exact odd_dvd_of_dvd_mul_two_pow 1 hodd
      (norm_field U0 hp7 hg hord hD P hP N hN : Nat.card N ∣ 21 * 2 ^ 1)
  · have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    obtain ⟨g, hg, hord, hD⟩ := norm_ex_eleven
    intro P hP N hN _
    exact norm_field U0 hp11 hg hord hD P hP N hN
  · obtain ⟨S, hS, hSU, hSab⟩ := s0_exists
    have hcard : Nat.card (S.subgroupOf U0) = 3 ^ 6 := by
      rw [← hS.trans (by norm_num : 729 = 3 ^ 6)]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSU).toEquiv
    obtain ⟨T, hT⟩ := exists_sylow_three (H := ↥U0) (by rw [card_U0]; norm_num) _ hcard
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine abelian_lt_of_sylow T ?_
    intro A hAT hab
    rw [hT] at hAT
    have hAS : A.map U0.subtype ≤ S := by
      rintro _ ⟨a, ha, rfl⟩
      exact hAT ha
    have hcardA : Nat.card (A.map U0.subtype) = Nat.card A :=
      Subgroup.card_map_of_injective U0.subtype_injective
    rw [← hcardA]
    exact hSab _ hAS (abelian_map_subtype U0 A hab)

theorem odd_lt_of_le_U0
    (M : Subgroup Co1) (hM : M ≤ U0) (hodd : Odd (Nat.card M)) :
    Nat.card M < 3000 := by
  have hfin := finite_co1
  have hcard : Nat.card (M.subgroupOf U0) = Nat.card M :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM).toEquiv
  have := u6Hyp.odd_card_lt (M.subgroupOf U0) (by rw [hcard]; exact hodd)
  rwa [hcard] at this

end U6Odd

theorem u6OddFact :
    U6OddFact := by
  intro u₁ u₂ hu₁ hu₂ hu₁₂ M hM hodd
  have hv₂ : toVecD 24 u1 = CFSG.Sporadic.Co1.Module.v₂ := CFSG.Sporadic.Co1.Module.toVecD_v₂
  have hx : toVecD 24 u1 ∈ co1Orbit 0 := by
    rw [CFSG.Sporadic.Co1.Module.Pairs.co1Orbit_zero, hv₂]
    exact MulAction.mem_orbit_self _
  have hy : toVecD 24 u2 ∈ co1Orbit 0 := by
    rw [CFSG.Sporadic.Co1.Module.Pairs.co1Orbit_zero]
    exact y₀_mem_cls.1
  have hxy : toVecD 24 u1 + toVecD 24 u2 ∈ co1Orbit 0 := by
    rw [CFSG.Sporadic.Co1.Module.Pairs.co1Orbit_zero, hv₂]
    exact y₀_mem_cls.2
  obtain ⟨h, hh₁, hh₂⟩ := S365.exists_co1Act_pair hu₁ hu₂ hu₁₂ hx hy hxy
  let M' : Subgroup Co1 := M.map (MulAut.conj h).toMonoidHom
  have hM' : M' ≤ U0 := by
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨conj_fix hh₁ (hM hm).1, conj_fix hh₂ (hM hm).2⟩
  have hcard : Nat.card M' = Nat.card M := Subgroup.card_map_of_injective (MulAut.conj h).injective
  rw [← hcard]
  exact U6Odd.odd_lt_of_le_U0 M' hM' (by rw [hcard]; exact hodd)

end CFSG.Monster.GMS
