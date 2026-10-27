module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.S15221

open CFSG.Open CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem exists_card_eq_three_mul {Y : Subgroup G} (h : (pCoreOf 2 Y).relIndex Y = 3) :
    ∃ a : ℕ, Nat.card Y = 3 * 2 ^ a := by
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (pCoreOf_isPGroup 2 Y)
  refine ⟨a, ?_⟩
  have h1 := Subgroup.relIndex_mul_card (pCoreOf 2 Y) Y
  rw [inf_of_le_left (pCoreOf_le 2 Y), h, ha] at h1
  exact h1.symm

theorem three_dvd_card_of_relIndex {Y : Subgroup G} (h : (pCoreOf 2 Y).relIndex Y = 3) :
    3 ∣ Nat.card Y := by
  obtain ⟨a, ha⟩ := exists_card_eq_three_mul h
  rw [ha]
  exact Dvd.intro _ rfl

theorem orderOf_dvd_three_of_odd {Y : Subgroup G} (h : (pCoreOf 2 Y).relIndex Y = 3) {y : G}
    (hy : y ∈ Y) (hodd : Odd (orderOf y)) : orderOf y ∣ 3 := by
  obtain ⟨a, ha⟩ := exists_card_eq_three_mul h
  have h1 : orderOf y ∣ 3 * 2 ^ a := ha ▸ Subgroup.orderOf_dvd_natCard Y hy
  have h2 : Nat.Coprime (orderOf y) 2 := by
    rw [Nat.coprime_comm, Nat.coprime_two_left]
    exact hodd
  exact (Nat.Coprime.pow_right a h2).dvd_of_dvd_mul_right h1

theorem le_thetaOf_of_eq_oTwoUpper {Y C : Subgroup G} (hY : Y = oTwoUpper Y)
    (h : (pCoreOf 2 Y).relIndex Y = 3) (hYC : Y ≤ C) : Y ≤ thetaOf C := by
  conv_lhs => rw [hY]
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  have h3 := orderOf_dvd_three_of_odd h hx.1 hx.2
  rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h1 | h1
  · have : x = 1 := orderOf_eq_one_iff.mp h1
    rw [SetLike.mem_coe, this]
    exact Subgroup.one_mem _
  · exact Subgroup.subset_closure ⟨hYC hx.1, h1⟩

theorem inf_pCoreOf_le_pCoreOf {Y P : Subgroup G} (hYP : Y ≤ P) :
    Y ⊓ pCoreOf 2 P ≤ pCoreOf 2 Y := by
  refine le_pCoreOf 2 inf_le_left ?_ ((pCoreOf_isPGroup 2 P).to_le inf_le_right)
  refine ⟨fun x hx h => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  refine ⟨Y.mul_mem (Y.mul_mem h.2 hx.1) (Y.inv_mem h.2), ?_⟩
  have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 P (hYP h.2)) x).mp hx.2
  simpa using this

end CFSG.Quasithin.S15221
