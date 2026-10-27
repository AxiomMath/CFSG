module

public import CFSG.Quasithin.Background.GoldschmidtRankOneLift

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.GH74.Uniqueness.Bender

variable {n : ℕ} {F : Type} [Field F] [Finite F]

theorem benderType_statedProj (hn : 2 ≤ n) (hF : Nat.card F = (2 ^ n) ^ 2) :
    ∃ e : ℕ, BenderType (StatedProj (StatedSU 3 (2 ^ n) F)) n 3 e := by
  have hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (StatedProj (StatedSU 3 (2 ^ n) F)) .PSU 3 2 n :=
    ⟨⟨Nat.prime_two, by omega, le_rfl, fun h => ?_⟩, F, inferInstance, inferInstance, hF,
      ⟨MulEquiv.refl _⟩⟩
  · obtain ⟨e⟩ := CFSG.ComponentClassification.GMS78.nonempty_mulEquiv_psu3_of_stated hn hmodel
    have hP : CFSG.Theory.Comparator.PSU3Model n = CFSG.Open.PSU3 2 n :=
        CFSG.Models.benderPSU3Model_eq_psu3 n
    exact ⟨_, BenderType.unitary n hn (e.trans (MulEquiv.subgroupCongr hP.symm))⟩
  · have h2 : 2 ^ n = 2 ^ 1 := by simpa using congrArg Prod.snd h
    have := Nat.pow_right_injective le_rfl h2
    omega

theorem isRankOneSylowCyclic_statedProj (hn : 2 ≤ n)
    (hF : Nat.card F = (2 ^ n) ^ 2) : IsRankOneSylowCyclic (StatedProj (StatedSU 3 (2 ^ n) F)) := by
  obtain ⟨e, hB⟩ := benderType_statedProj hn hF
  exact isRankOneSylowCyclic_of_benderType hB

omit [Finite F] in
theorem det_eq_one_of_mem_statedSU {m q : ℕ} {A : GL (Fin m) F} (hA : A ∈ StatedSU m q F) :
    Matrix.GeneralLinearGroup.det A = 1 :=
  MonoidHom.mem_ker.1 ((CFSG.Open.StatedAPI.statedSL_eq_ker_det m F).le
    (CFSG.Open.StatedAPI.statedSU_le_statedSL m q F hA))

omit [Finite F] in
theorem statedSU_three_kernel (z : StatedSU 3 (2 ^ n) F)
    (hz : z ∈ ((StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (2 ^ n) F))) :
    z ^ 3 = 1 := by
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hz
  have hc' : (z : GL (Fin 3) F) = Matrix.GeneralLinearGroup.scalar (Fin 3) c := hc.symm
  have hdet := det_eq_one_of_mem_statedSU z.2
  rw [hc', Matrix.GeneralLinearGroup.det_scalar] at hdet
  have hc3 : c ^ 3 = 1 := by simpa using hdet
  refine Subtype.ext ?_
  rw [Subgroup.coe_pow, hc', ← map_pow, hc3, map_one]
  rfl

omit [Finite F] in
theorem statedSU_scalars_le_center {m q : ℕ} :
    (StatedScalars (Fin m) F).subgroupOf (StatedSU m q F) ≤ Subgroup.center (StatedSU m q F) := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro g
  have hzc : (z : GL (Fin m) F) ∈ Subgroup.center (GL (Fin m) F) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact hz
  exact Subtype.ext (Subgroup.mem_center_iff.mp hzc g)

omit [Finite F] in
theorem statedSU_three_scalars_odd (z : StatedSU 3 (2 ^ n) F)
    (hz : z ∈ (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (2 ^ n) F)) :
    Odd (orderOf z) := by
  have h3 : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one (statedSU_three_kernel z hz)
  rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h
  · rw [h]
    exact odd_one
  · rw [h]
    exact ⟨1, rfl⟩

theorem isRankOneSylow_statedSU (hn : 2 ≤ n)
    (hF : Nat.card F = (2 ^ n) ^ 2) : IsRankOneSylow (StatedSU 3 (2 ^ n) F) := by
  have hnq : (3, 2 ^ n) ≠ (3, 2) := fun h => by
    have h2 : 2 ^ n = 2 ^ 1 := by simpa using congrArg Prod.snd h
    have := Nat.pow_right_injective le_rfl h2
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : Group.IsPerfect (StatedSU 3 (2 ^ n) F) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hF (n := 3) le_rfl hnq
  refine isRankOneSylow_of_central_cover
    (QuotientGroup.mk' ((StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (2 ^ n) F)))
    (QuotientGroup.mk'_surjective _) ?_ ?_
    (fun z _ => by rw [Group.isPerfect_def.mp hperf]; exact Subgroup.mem_top z)
    (isRankOneSylowCyclic_statedProj hn hF)
  · rw [QuotientGroup.ker_mk']
    exact statedSU_scalars_le_center
  · intro z hz
    rw [QuotientGroup.ker_mk'] at hz
    exact statedSU_three_scalars_odd z hz

end CFSG.Quasithin
