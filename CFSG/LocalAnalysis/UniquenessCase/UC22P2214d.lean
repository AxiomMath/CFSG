module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22g
import CFSG.Blueprint.LieModelAPI
import CFSG.Milestones.ASVolI.A3Aut.L2
import CFSG.Milestones.ASVolI.A3Aut.C5Sp4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner inner_normal congr_conj equivalence)

section Criteria

theorem uc22p2214_out_mem_of_mem_sup {Y H : Type*} [Group Y] [Group H] (φ : H →* MulAut Y)
    (hI : (MulAut.conj : Y →* MulAut Y).range ⊓ φ.range = ⊥) {r : ℕ} (hr : r.Prime) (hrH : ¬ r ∣ Nat.card H)
    {α : MulAut Y} (hmem : α ∈ (MulAut.conj : Y →* MulAut Y).range ⊔ φ.range) (hα : α ^ r = 1) :
    α ∈ (MulAut.conj : Y →* MulAut Y).range := by
  haveI : (MulAut.conj : Y →* MulAut Y).range.Normal := inner_normal Y
  rw [← SetLike.mem_coe, Subgroup.normal_mul] at hmem
  obtain ⟨y, hy, z, ⟨h, rfl⟩, rfl⟩ := Set.mem_mul.1 hmem
  have h1 : φ h ^ r ∈ (MulAut.conj : Y →* MulAut Y).range := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    have h2 := congrArg (QuotientGroup.mk (s := (MulAut.conj : Y →* MulAut Y).range)) hα
    rwa [QuotientGroup.mk_pow, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff y).2 hy, one_mul,
      QuotientGroup.mk_one] at h2
  have h3 : φ h ^ r = 1 := by
    have h4 : φ h ^ r ∈ (MulAut.conj : Y →* MulAut Y).range ⊓ φ.range := ⟨h1, h ^ r, map_pow φ h r⟩
    rwa [hI, Subgroup.mem_bot] at h4
  have h5 : orderOf (φ h) ∣ Nat.card H := (orderOf_map_dvd φ h).trans (orderOf_dvd_natCard h)
  rcases (Nat.dvd_prime hr).1 (orderOf_dvd_of_pow_eq_one h3) with h6 | h6
  · rw [orderOf_eq_one_iff.1 h6, mul_one]
    exact hy
  · rw [h6] at h5
    exact absurd h5 hrH

theorem uc22p2214_out_mem_of_card_dvd {X : Type*} [Group X] {m r : ℕ} (hm : Nat.card (Outer X) ∣ m)
    (hr : r.Prime) (hrm : ¬ r ∣ m) {α : MulAut X} (hα : α ^ r = 1) :
    α ∈ (MulAut.conj : X →* MulAut X).range := by
  set a : Outer X := (α : MulAut X ⧸ inner X) with ha
  have h1 : orderOf a ∣ r :=
    orderOf_dvd_of_pow_eq_one (by rw [ha, ← QuotientGroup.mk_pow, hα, QuotientGroup.mk_one])
  have h2 : orderOf a ∣ m := (orderOf_dvd_natCard a).trans hm
  rcases (Nat.dvd_prime hr).1 h1 with h3 | h3
  · exact (QuotientGroup.eq_one_iff α).1 (orderOf_eq_one_iff.1 h3)
  · rw [h3] at h2
    exact absurd h2 hrm

theorem uc22p2214_out_mem_of_congr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {α : MulAut X}
    (h : MulAut.congr e α ∈ (MulAut.conj : Y →* MulAut Y).range) :
    α ∈ (MulAut.conj : X →* MulAut X).range := by
  obtain ⟨y, hy⟩ := h
  refine ⟨e.symm y, (MulAut.congr e).injective ?_⟩
  rw [congr_conj, MulEquiv.apply_symm_apply, hy]

end Criteria

section Groups

variable {X : Type} [Group X] {n r : ℕ}

theorem uc22p2214_inner_of_prime_L2 (hX : IsL2 X n) (hr : r.Prime) (hrn : ¬ r ∣ n) {α : MulAut X}
    (hα : α ^ r = 1) : α ∈ (MulAut.conj : X →* MulAut X).range := by
  obtain ⟨-, F, _, _, hF, _, ⟨e⟩⟩ := uc22p22g_isL2_psl hX
  refine uc22p2214_out_mem_of_congr e (uc22p2214_out_mem_of_mem_sup (CFSG.GorensteinWalter.psl2FieldAut F)
    CFSG.ASVolI.burnsideAut_psl2_inn_inf_field hr ?_ (CFSG.ASVolI.burnsideAut_psl2_aut_mem _)
    (by rw [← map_pow, hα, map_one]))
  rwa [(CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two F hF).1]

theorem uc22p2214_inner_of_prime_Sz (hX : IsSz X n) (hr : r.Prime) (hrn : ¬ r ∣ n)
    {α : MulAut X} (hα : α ^ r = 1) : α ∈ (MulAut.conj : X →* MulAut X).range := by
  obtain ⟨-, -, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.suzukiModel hX
  refine uc22p2214_out_mem_of_card_dvd ?_ hr hrn hα
  rw [Nat.card_congr (equivalence e).toEquiv]
  exact (CFSG.LieType.Suzuki.suzukiGroup_outer_isCyclic_card_dvd ha hK).2

theorem uc22p2214_inner_of_prime_Sp4 (hX : IsSp4 X n) (hr : r.Prime) (hrn : ¬ r ∣ 2 * n) {α : MulAut X}
    (hα : α ^ r = 1) : α ∈ (MulAut.conj : X →* MulAut X).range := by
  obtain ⟨⟨-, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide)
  haveI : CharP K 2 := uc22p22d_charP_two hn hK
  have hβ : MulAut.congr e α ^ r = 1 := by rw [← map_pow, hα, map_one]
  have hodd : Odd r := hr.odd_of_ne_two (by rintro rfl; exact hrn (dvd_mul_right 2 n))
  refine uc22p2214_out_mem_of_congr e (uc22p2214_out_mem_of_mem_sup
    (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut 2 K)
    CFSG.ASVolI.burnsideAut_c5Sp4_inn_inf_field hr ?_
    (CFSG.ASVolI.burnsideAut_c5Sp4_odd_mem (hodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one hβ))) hβ)
  rw [(CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K hK).1]
  exact fun h => hrn (h.mul_left 2)

theorem uc22p2214_inner_of_prime_U3 (hX : IsU3 X n) (hr : r.Prime) (hrn : ¬ r ∣ 6 * n) {α : MulAut X}
    (hα : α ^ r = 1) : α ∈ (MulAut.conj : X →* MulAut X).range := by
  obtain ⟨⟨hp, hn, -, hne⟩, K, _, _, hK, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide)
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K :=
    ⟨hp, hn, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq : ¬(3 = 3 ∧ 2 ^ n = 2) := fun ⟨_, h2⟩ => hne (by rw [h2])
  refine uc22p2214_out_mem_of_card_dvd ?_ hr hrn hα
  rw [Nat.card_congr (equivalence (e.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU
      (by norm_num)).symm)).toEquiv,
    (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_full_diagonal_outer_order hU le_rfl hq).2.2.2.2.1]
  calc 2 * n * Nat.gcd 3 (2 ^ n + 1) ∣ 2 * n * 3 := Nat.mul_dvd_mul_left _ (Nat.gcd_dvd_left _ _)
    _ = 6 * n := by ring

end Groups

end CFSG.LocalAnalysis.UniquenessCase.UC22
