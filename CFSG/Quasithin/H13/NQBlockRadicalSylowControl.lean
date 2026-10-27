module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.H13.NQBlockOriginalReducedModule
public import CFSG.Quasithin.SteinbergCCLocalSylowAction

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem omegaOneCenterOf_characteristic (R : Subgroup G) :
    ((omegaOneCenterOf 2 R).subgroupOf R).Characteristic := by
  rw [characteristic_iff_map_le]
  rintro φ _ ⟨z, hz, rfl⟩
  have hz' : (z : G) ∈ omegaOneCenterOf 2 R := hz
  change ((φ z : ↥R) : G) ∈ omegaOneCenterOf 2 R
  rw [mem_omegaOneCenterOf_iff] at hz' ⊢
  obtain ⟨-, hzc, hz2⟩ := hz'
  refine ⟨(φ z).2, fun r hr => ?_, ?_⟩
  · obtain ⟨r', hr'⟩ := φ.surjective ⟨r, hr⟩
    have e : r = ((φ r' : ↥R) : G) := (congrArg Subtype.val hr').symm
    subst e
    have h1 : z * r' = r' * z := Subtype.ext (hzc r' r'.2)
    have h2 := congrArg φ h1
    rw [map_mul, map_mul] at h2
    exact congrArg Subtype.val h2
  · have h1 : z ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hz2)
    change ((φ z : ↥R) : G) ^ 2 = 1
    rw [← Subgroup.coe_pow, ← map_pow, h1, map_one, Subgroup.coe_one]

theorem omegaOneCenterOf_two_ne_bot {R : Subgroup G} (hR2 : IsPGroup 2 R) (hR1 : R ≠ ⊥) :
    omegaOneCenterOf 2 R ≠ ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial ↥R := (Subgroup.nontrivial_iff_ne_bot R).mpr hR1
  have hc := hR2.center_nontrivial
  obtain ⟨⟨z, hzc⟩, hz1⟩ := exists_ne (1 : center ↥R)
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  obtain ⟨k, hk⟩ := hR2 z
  obtain ⟨y, hyc, hy1, hy2⟩ : ∃ y ∈ center ↥R, y ≠ 1 ∧ y ^ 2 = 1 := by
    have hord : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    obtain ⟨m, hm, hmz⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
    have hm0 : m ≠ 0 := by
      intro h0
      rw [h0, pow_zero, orderOf_eq_one_iff] at hmz
      exact hz1' hmz
    refine ⟨z ^ 2 ^ (m - 1), Subgroup.pow_mem _ hzc _, fun h => ?_, ?_⟩
    · have := orderOf_le_of_pow_eq_one (pow_pos two_pos _) h
      rw [hmz] at this
      have h2 : 2 ^ (m - 1) < 2 ^ m := Nat.pow_lt_pow_right one_lt_two (by omega)
      omega
    · rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm0), ← hmz,
        pow_orderOf_eq_one]
  intro h0
  apply hy1
  have h1 : (y : G) ∈ omegaOneCenterOf 2 R := by
    rw [mem_omegaOneCenterOf_iff]
    refine ⟨y.2, fun r hr => ?_, ?_⟩
    · exact congrArg Subtype.val ((mem_center_iff.mp hyc ⟨r, hr⟩).symm)
    · rw [← Subgroup.coe_pow, hy2, Subgroup.coe_one]
  rw [h0, mem_bot] at h1
  exact Subtype.ext h1

end CFSG.Quasithin.H13.NQBlock
