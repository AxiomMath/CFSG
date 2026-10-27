module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.F7Geometry
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.CosetGeom

theorem eq_of_pow_mul_eq_of_odd {k j m m' : ℕ} (hm : ¬ 2 ∣ m) (hm' : ¬ 2 ∣ m')
    (h : 2 ^ k * m = 2 ^ j * m') : k = j := by
  rcases lt_trichotomy k j with hkj | hkj | hkj
  · exfalso
    have h2 : 2 ^ j = 2 ^ k * 2 ^ (j - k) := by
      rw [← pow_add]
      congr 1
      omega
    rw [h2, mul_assoc] at h
    have h' := Nat.eq_of_mul_eq_mul_left (by positivity) h
    apply hm
    rw [h']
    exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  · exact hkj
  · exfalso
    have h2 : 2 ^ k = 2 ^ j * 2 ^ (k - j) := by
      rw [← pow_add]
      congr 1
      omega
    rw [h2, mul_assoc] at h
    have h' := Nat.eq_of_mul_eq_mul_left (by positivity) h.symm
    apply hm'
    rw [h']
    exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _

theorem card_sylow_eq_pow {G : Type*} [Group G] [Finite G] {L S : Subgroup G} (hSL : S ≤ L)
    (hS : IsSylowTwoOf S L) {j m : ℕ} (hm : ¬ 2 ∣ m) (hL : Nat.card ↥L = 2 ^ j * m) :
    Nat.card ↥S = 2 ^ j := by
  obtain ⟨k, hk⟩ := hS.2.1.exists_card_eq
  have h1 := Subgroup.card_mul_index (S.subgroupOf L)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSL).toEquiv, hk, hL] at h1
  have hodd : ¬ 2 ∣ (S.subgroupOf L).index := hS.2.2
  rw [hk, eq_of_pow_mul_eq_of_odd hodd hm h1]

end CFSG.Quasithin
