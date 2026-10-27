module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TCFin
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsLocal
public import CFSG.RankThree.PartTwo.Sec8.Item812Res3ProofTools
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4TC
public import CFSG.Sporadic.Schreier.J4SSylowBase
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.Quasithin.H13.T614

open CFSG.Sporadic.Schreier.Tits CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin
  CFSG.RankThree.PartTwo.Sec8 CFSG.LieType.Ree
open scoped commutatorElement

theorem three_witness_transport {G H : Type} [Group G] [Group H] (e : G ≃* H) {x y : H}
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hy1 : y ≠ 1) (hxy : x * y = y * x)
    (hnot : x ∉ Subgroup.zpowers y) :
    ∃ u v : G, u ^ 3 = 1 ∧ v ^ 3 = 1 ∧ v ≠ 1 ∧ u * v = v * u ∧ u ∉ Subgroup.zpowers v := by
  refine ⟨e.symm x, e.symm y, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow e.symm x 3, hx, map_one]
  · rw [← map_pow e.symm y 3, hy, map_one]
  · intro h
    apply hy1
    have h2 := congrArg e h
    rwa [MulEquiv.apply_symm_apply, map_one] at h2
  · rw [← map_mul e.symm, ← map_mul e.symm, hxy]
  · intro h
    apply hnot
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have h2 := congrArg e hk
    simp only [map_zpow, MulEquiv.apply_symm_apply] at h2
    exact h2

theorem exists_three_witness_of_card_27 {C : Type} [Group C] [Finite C] {x y : C}
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hz1 : ⁅x, y⁆ ≠ 1) (hzx : Commute ⁅x, y⁆ x)
    (hzy : Commute ⁅x, y⁆ y) (hcard : Nat.card (Subgroup.closure ({x, y} : Set C)) = 3 ^ 3) :
    ∃ u v : C, u ^ 3 = 1 ∧ v ^ 3 = 1 ∧ v ≠ 1 ∧ u * v = v * u ∧ u ∉ Subgroup.zpowers v := by
  set G' : Subgroup C := Subgroup.closure ({x, y} : Set C) with hG'
  set z : C := ⁅x, y⁆ with hz
  have hx' : x ∈ G' := Subgroup.subset_closure (by simp)
  have hy' : y ∈ G' := Subgroup.subset_closure (by simp)
  have hzG : z ∈ G' := by
    rw [hz, commutatorElement_def]
    exact G'.mul_mem (G'.mul_mem (G'.mul_mem hx' hy') (G'.inv_mem hx')) (G'.inv_mem hy')
  have hordz : orderOf z ∣ 3 ^ 3 := by
    rw [← hcard]
    have h := orderOf_dvd_natCard (⟨z, hzG⟩ : G')
    rwa [Subgroup.orderOf_mk] at h
  have hz3 : 3 ∣ orderOf z := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hordz
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hk
      exact hz1 hk
    rw [hk]
    exact dvd_pow_self 3 hk0
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers z) 3
    (by rw [Nat.card_zpowers]; exact hz3)
  have hW3 : (w : C) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one w
    rw [hw] at h
    simpa using congrArg Subtype.val h
  have hW1 : (w : C) ≠ 1 := by
    intro h
    have hw1 : w = 1 := Subtype.ext h
    rw [hw1, orderOf_one] at hw
    norm_num at hw
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp w.2
  have hWx : Commute (w : C) x := by
    rw [← hk]
    exact Commute.zpow_left hzx k
  have hWy : Commute (w : C) y := by
    rw [← hk]
    exact Commute.zpow_left hzy k
  refine ⟨x, (w : C), hx, hW3, hW1, hWx.symm.eq, ?_⟩
  intro h
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h
  have hxy : Commute x y := by
    rw [← hm]
    exact Commute.zpow_left hWy m
  exact hz1 (commutatorElement_eq_one_iff_mul_comm.mpr hxy.eq)

theorem titsRankThreeFact_holds :
    TitsRankThreeFact := by
  intro Y _ hfin hY
  obtain ⟨e⟩ := titsModelEquiv Y 2 1 hY
  haveI : Fact (Nat.card (ZMod 2) = 2) := ⟨Nat.card_zmod 2⟩
  obtain ⟨x, y, -, hx3, hy3, hz1, hzx, hzy, hcard, -, -, -⟩ :=
    CFSG.SectionRank.Tits_sylow3_cubic_witness (K := ZMod 2) (Nat.card_zmod 2)
  have ι : commutator (reeFixed ReeTag.F4 (ZMod 2) 0) ≃* titsD := titsDerivedIso (K := ZMod 2)
  haveI : Finite (commutator (reeFixed ReeTag.F4 (ZMod 2) 0)) :=
    Finite.of_equiv titsD ι.symm.toEquiv
  obtain ⟨u, v, hu3, hv3, hv1, huv, hunot⟩ :=
    exists_three_witness_of_card_27 hx3 hy3 hz1 hzx hzy hcard
  obtain ⟨u', v', hu3', hv3', hv1', huv', hunot'⟩ :=
    three_witness_transport (ι.trans e.symm).symm hu3 hv3 hv1 huv hunot
  refine ⟨Subgroup.zpowers v' ⊔ Subgroup.zpowers u', ?_, ?_⟩
  · exact Item812Res3.isElemAbelian_sup_zpowers hv3' hu3' huv'.symm
  · rw [Item812Res3.card_sup_zpowers_eq_sq Nat.prime_three hv3' hv1' hu3' hunot' huv'.symm]
    norm_num

end CFSG.Quasithin.H13.T614

end
