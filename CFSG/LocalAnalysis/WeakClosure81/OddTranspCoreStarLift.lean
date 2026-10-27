module

public import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreTwo
public import CFSG.Timmesfeld.Bridge.Asc72Basic
import CFSG.OddTranspositions.PartThree.OddTranspClosure
import CFSG.OddTranspositions.SevenFourEight.PCoreNotCentral

public section

namespace CFSG.LocalAnalysis.WeakClosure81.CoreStar

open CFSG.Timmesfeld.Bridge.Asc72

variable {Y Q : Type} [Group Y] [Group Q]

private theorem commute_of_map {D : Set Y} (hD : IsOddTransp D)
    (π : Y →* Q) (hker : π.ker ≤ Subgroup.center Y) {a b : Y}
    (ha : a ∈ D) (hb : b ∈ D) (hc : Commute (π a) (π b)) : Commute a b := by
  have hq : Commute (QuotientGroup.mk' π.ker a) (QuotientGroup.mk' π.ker b) := by
    apply Commute.of_map (QuotientGroup.kerLift_injective π)
    change Commute (π a) (π b)
    exact hc
  exact CFSG.OddTranspositions.PartThree.commute_of_commute_mk_of_le_center'
    hD hker ha hb hq

private theorem orderOf_mul_mem_of_map {D : Set Y} (hD : IsOddTransp D)
    (π : Y →* Q) (hker : π.ker ≤ Subgroup.center Y) {a b : Y}
    (ha : a ∈ D) (hb : b ∈ D)
    (h3 : orderOf (π a * π b) ∈ ({1, 2, 3} : Set ℕ)) :
    orderOf (a * b) ∈ ({1, 2, 3} : Set ℕ) := by
  rcases hD.commute_or_odd ha hb with hc | hodd
  · have hp : (a * b) ^ 2 = 1 := by
      rw [hc.mul_pow, pow_two, pow_two, hD.mul_self_eq_one ha,
        hD.mul_self_eq_one hb, mul_one]
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hp) with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
  · have heq : orderOf (π a * π b) =
        orderOf (QuotientGroup.mk' π.ker a * QuotientGroup.mk' π.ker b) := by
      have hh := orderOf_injective (QuotientGroup.kerLift π)
        (QuotientGroup.kerLift_injective π) (QuotientGroup.mk' π.ker (a * b))
      change orderOf (π (a * b)) = orderOf (QuotientGroup.mk' π.ker (a * b)) at hh
      simpa only [map_mul] using hh
    have hdvd := CFSG.OddTranspositions.orderOf_mul_dvd_three_of_le_center hker
      (hD.mul_self_eq_one ha) (hD.mul_self_eq_one hb) hodd (heq ▸ h3)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Or.inl h1
    · exact Or.inr (Or.inr h3)

private theorem orderOf_mul_eq_three_of_map {D : Set Y} (hD : IsOddTransp D)
    (π : Y →* Q) (hker : π.ker ≤ Subgroup.center Y) {a b : Y}
    (ha : a ∈ D) (hb : b ∈ D) (h3 : orderOf (π a * π b) = 3) :
    orderOf (a * b) = 3 := by
  have hdvd : 3 ∣ orderOf (a * b) := by
    simpa only [map_mul, h3] using orderOf_map_dvd π (a * b)
  rcases orderOf_mul_mem_of_map hD π hker ha hb (Or.inr (Or.inr h3)) with h1 | h2 | h3
  · rw [h1] at hdvd
    norm_num at hdvd
  · rw [h2] at hdvd
    norm_num at hdvd
  · exact h3

private theorem exists_isConj_preimage (π : Y →* Q) (hπ : Function.Surjective π)
    {t : Y} {a : Q} (ha : IsConj (π t) a) : ∃ x : Y, IsConj t x ∧ π x = a := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp ha
  obtain ⟨g', rfl⟩ := hπ g
  exact ⟨g' * t * g'⁻¹, isConj_iff.mpr ⟨g', rfl⟩, by simp⟩

theorem hasCoreStar_of_map_of_ker_le_center (π : Y →* Q) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center Y) {t : Y} (hD : IsOddTransp {x : Y | IsConj t x})
    (h : HasCoreStar Q (π t)) : HasCoreStar Y t := by
  obtain ⟨a, b, c, ha, hb, hc, ota, otb, otc, cab, cac, cbc, nab, nac, nbc⟩ := h
  obtain ⟨x, hx, hπx⟩ := exists_isConj_preimage π hπ ha
  obtain ⟨y, hy, hπy⟩ := exists_isConj_preimage π hπ hb
  obtain ⟨z, hz, hπz⟩ := exists_isConj_preimage π hπ hc
  refine ⟨x, y, z, hx, hy, hz, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact orderOf_mul_eq_three_of_map hD π hker (IsConj.refl t) hx (by rwa [hπx])
  · exact orderOf_mul_eq_three_of_map hD π hker (IsConj.refl t) hy (by rwa [hπy])
  · exact orderOf_mul_eq_three_of_map hD π hker (IsConj.refl t) hz (by rwa [hπz])
  · exact (commute_of_map hD π hker hx hy (by rwa [hπx, hπy])).eq
  · exact (commute_of_map hD π hker hx hz (by rwa [hπx, hπz])).eq
  · exact (commute_of_map hD π hker hy hz (by rwa [hπy, hπz])).eq
  · exact fun hxy => nab (by rw [← hπx, ← hπy, hxy])
  · exact fun hxz => nac (by rw [← hπx, ← hπz, hxz])
  · exact fun hyz => nbc (by rw [← hπy, ← hπz, hyz])

theorem orderOf_mul_mem_of_map_of_ker_le_center (π : Y →* Q)
    (hker : π.ker ≤ Subgroup.center Y) {t : Y} (hD : IsOddTransp {x : Y | IsConj t x})
    {d e : Y} (hd : IsConj t d) (he : IsConj t e)
    (h : orderOf (π d * π e) ∈ ({1, 2, 3} : Set ℕ)) :
    orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ) :=
  orderOf_mul_mem_of_map hD π hker hd he h

end CFSG.LocalAnalysis.WeakClosure81.CoreStar
