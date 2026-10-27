module

import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch1Sec3Basic
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S15223P4

namespace B

variable {G : Type} [Group G] [Finite G]

theorem pow_eq_pow_of_odd_mul {a b r m : ℕ} (hr : ¬ 2 ∣ r) (hm : ¬ 2 ∣ m)
    (h : 2 ^ a * r = 2 ^ b * m) : a = b := by
  have hcr : Nat.Coprime (2 ^ a) m :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hm)
  have hcm : Nat.Coprime (2 ^ b) r :=
    Nat.Coprime.pow_left b ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hr)
  have h1 : 2 ^ a ∣ 2 ^ b := hcr.dvd_of_dvd_mul_right ⟨r, h.symm⟩
  have h2 : 2 ^ b ∣ 2 ^ a := hcm.dvd_of_dvd_mul_right ⟨m, h⟩
  exact le_antisymm ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h1)
    ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h2)

theorem card_sylow_eq {A X : Subgroup G} (hA : IsSylowTwoOf A X) {q k m : ℕ}
    (hq : ∃ b : ℕ, q = 2 ^ b) (hm : ¬ 2 ∣ m) (hX : Nat.card X = q * (2 ^ k * m)) :
    Nat.card A = q * 2 ^ k := by
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).mp hA.isPGroup
  obtain ⟨b, rfl⟩ := hq
  have h1 := Subgroup.relIndex_mul_card A X
  rw [inf_eq_left.2 hA.le] at h1
  have hodd : ¬ 2 ∣ A.relIndex X := hA.2.2
  have h2 : 2 ^ a * A.relIndex X = 2 ^ (b + k) * m := by
    rw [← ha, mul_comm, h1, hX, pow_add]
    ring
  have := pow_eq_pow_of_odd_mul hodd hm h2
  rw [ha, this, pow_add]

theorem relIndex_eq_of_card {U X : Subgroup G} (hUX : U ≤ X) {n : ℕ}
    (h : Nat.card X = n * Nat.card U) : U.relIndex X = n := by
  have h1 := Subgroup.relIndex_mul_card U X
  rw [inf_eq_left.2 hUX] at h1
  have hpos : 0 < Nat.card U := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [h1, h]

omit [Finite G] in
theorem false_of_orderOf_three_mem {P : Subgroup G} (hP : IsPGroup 2 ↥P) {z : G} (hz : z ∈ P)
    (h3 : orderOf z = 3) : False := by
  obtain ⟨n, hn⟩ := hP ⟨z, hz⟩
  have hzn : z ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hd := orderOf_dvd_of_pow_eq_one hzn
  rw [h3] at hd
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
  omega

omit [Finite G] in
theorem mem_pCoreOf_of_mem_pCore {X : Subgroup G} {x : ↥X} (hx : x ∈ CFSG.pCore 2 ↥X) :
    (x : G) ∈ pCoreOf 2 X := (CFSG.mem_openPCoreOf_iff x).mpr hx

omit [Finite G] in
theorem relIndex_pCoreOf_eq_card_quot (X : Subgroup G) :
    (pCoreOf 2 X).relIndex X = Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) := by
  unfold Subgroup.relIndex pCoreOf
  rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective X.subtype_injective,
    Subgroup.index_eq_card]

omit [Finite G] in
theorem card_eq_pCoreOf_mul_quot (X : Subgroup G) :
    Nat.card X = Nat.card (pCoreOf 2 X) * Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) := by
  rw [← relIndex_pCoreOf_eq_card_quot]
  exact card_eq_card_pCoreOf_mul_relIndex X

theorem exists_card_pCoreOf_eq_pow (X : Subgroup G) : ∃ b : ℕ, Nat.card (pCoreOf 2 X) = 2 ^ b :=
  (IsPGroup.iff_card (p := 2)).mp (pCoreOf_isPGroup 2 X)

end B

end S15223P4

end CFSG.Quasithin
