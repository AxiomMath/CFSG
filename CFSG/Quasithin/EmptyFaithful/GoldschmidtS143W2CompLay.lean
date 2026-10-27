module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompPerf
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.Quasithin

namespace S143

namespace InspW2

theorem false_of_quasisimple_sylow_le_small {X : Type*} [Group X] [Finite X] {K : Subgroup X}
    (hK : CFSG.IsQuasisimple K) {w : X} (hwc : ∀ g ∈ K, g * w = w * g) (hw2 : w * w = 1)
    (hw1 : w ≠ 1) (Sy : Sylow 2 K) {S₂ : Subgroup X} (hc : Nat.card S₂ ≤ 4) (hw : w ∈ S₂)
    (hle : (Sy : Subgroup K).map K.subtype ≤ S₂) : False := by
  have : Group.IsPerfect K := hK.1
  have : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hK
  set S : Subgroup X := (Sy : Subgroup K).map K.subtype with hS
  have hcardS : Nat.card S = Nat.card (Sy : Subgroup K) :=
    Subgroup.card_map_of_injective K.subtype_injective
  by_cases hsmall : Nat.card (Sy : Subgroup K) ≤ 2
  · refine false_of_perfect_sylow_two_quot (C := ⊥) bot_le Sy ?_
    rw [Subgroup.relIndex_bot_left]; exact hsmall
  ·
    have hdvd : Nat.card S ∣ Nat.card S₂ := Subgroup.card_dvd_of_le hle
    have hpos : 0 < Nat.card S₂ := Nat.card_pos
    have hSeq : S = S₂ := by
      apply Subgroup.eq_of_le_of_card_ge hle
      obtain ⟨m, hm⟩ := hdvd
      have h3 : 3 ≤ Nat.card S := by omega
      have hm1 : m = 1 := by
        rcases m with _ | _ | m
        · omega
        · rfl
        · nlinarith
      rw [hm, hm1, mul_one]
    have hwS : w ∈ S := hSeq ▸ hw
    obtain ⟨k, hk, hkw⟩ := Subgroup.mem_map.mp hwS
    have hkw' : (k : X) = w := hkw
    have hcen : k ∈ Subgroup.center K := Subgroup.mem_center_iff.mpr fun g =>
      Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, hkw']; exact hwc g g.2)
    have hCle : Subgroup.zpowers k ≤ Subgroup.center K := Subgroup.zpowers_le.mpr hcen
    have : (Subgroup.zpowers k).Normal := Subgroup.normal_of_le_center hCle
    have hCS : Subgroup.zpowers k ≤ (Sy : Subgroup K) := Subgroup.zpowers_le.mpr hk
    have hk2 : orderOf k = 2 := by
      apply orderOf_eq_prime
      · apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one, pow_two, hkw']; exact hw2
      · intro h1; apply hw1; rw [← hkw', h1]; rfl
    have hCcard : Nat.card (Subgroup.zpowers k) = 2 := by rw [Nat.card_zpowers, hk2]
    refine false_of_perfect_sylow_two_quot hCle Sy ?_
    have h1 := Subgroup.relIndex_mul_card (H := Subgroup.zpowers k) (K := (Sy : Subgroup K))
    rw [inf_eq_left.mpr hCS, hCcard] at h1
    have h4 : Nat.card (Sy : Subgroup K) ≤ 4 := by rw [← hcardS, hSeq]; exact hc
    omega

end InspW2

end S143

end CFSG.Quasithin
