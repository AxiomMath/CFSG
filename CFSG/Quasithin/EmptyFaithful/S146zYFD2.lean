module

public import CFSG.Quasithin.EmptyFaithful.S146zYFD1
public import CFSG.Quasithin.Vol2.F134LieD4Cells

public section

namespace CFSG.Quasithin.S146zY

namespace D4Five

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.Quasithin.F134.LieD4

theorem not_three_dvd_two_pow_of_d4 (m : ℕ) : ¬ 3 ∣ 2 ^ m := fun h => by
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
    (Nat.prime_three.dvd_of_dvd_pow h)
  omega

section Triality


variable {K : Type} [Field K]

theorem le_graphFixedRootBorel_of_card_twentyFive [Finite K] (σ : K ≃+* K) {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 3) (hσc : ∀ c, σ c = c ^ (2 ^ n))
    {Q H : Subgroup (ModGL TwistTag.D4.tag K)}
    (hBQ : graphFixedRootBorel TwistTag.D4 K σ.toRingHom ≤ Q)
    (hQC : Q ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hQ : Q ≠ graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (hHQ : H ≤ Q)
    (hUH : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤ H)
    (hH : Nat.card H = 25 * Nat.card (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)) :
    H ≤ graphFixedRootBorel TwistTag.D4 K σ.toRingHom := by
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hK3 : Nat.card K = 2 ^ (3 * n) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK3
  have hσ : Function.Surjective σ.toRingHom := σ.surjective
  have hQJ := (fixed_Borel_overgroup_classification TwistTag.D4 K σ Q hBQ hQC).1
  obtain ⟨b, hJb⟩ : ∃ b : Fin TwistTag.D4.foldedTag.rank,
      {a | canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a) ∈ Q} ⊆
        {b} := by
    obtain ⟨a, ha⟩ : ∃ a : Fin TwistTag.D4.foldedTag.rank,
        canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a) ∉ Q := by
      by_contra h
      have hJ : {a | canonicalRep (coxeterSystem TwistTag.D4.tag) K
          (TwistTag.D4.orbitReflection a) ∈ Q} = Set.univ :=
        Set.eq_univ_of_forall fun a => by
          by_contra ha
          exact h ⟨a, ha⟩
      apply hQ
      rw [hQJ, hJ]
      exact (fixed_standard_parabolic_cells TwistTag.D4 K σ).2.2.2.2.2
    have ha2 : a.val < 2 := a.2
    refine ⟨⟨1 - a.val, by change 1 - a.val < 2; omega⟩, fun j hj => ?_⟩
    have hja : j ≠ a := fun e => ha (e ▸ hj)
    have hj2 : j.val < 2 := j.2
    rw [Set.mem_singleton_iff, Fin.ext_iff]
    rw [Ne, Fin.ext_iff] at hja
    change j.val = 1 - a.val
    omega
  have hHb : H ≤ graphFixedParabolic TwistTag.D4 K σ.toRingHom {b} :=
    hHQ.trans (hQJ.le.trans (((fixed_standard_parabolic_cells TwistTag.D4 K σ).2.2.2.1 _ {b}).2
      hJb))
  have hUrel : (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).relIndex H = 25 := by
    have h := Subgroup.relIndex_mul_card (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) H
    rw [inf_eq_left.2 hUH, hH] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hBdvd : (graphFixedRootBorel TwistTag.D4 K σ.toRingHom).relIndex H ∣ 25 :=
    hUrel ▸ Subgroup.relIndex_dvd_of_le_left H graphFixedPosUnipotent_le_graphFixedRootBorel
  rcases le_or_relIndex_eq hσ hUH hHb with hHB | hrel
  · exact hHB
  · exfalso
    rw [hrel, card_graphFixedInversionUnipotent_D4 σ hn hK hσc b] at hBdvd
    have hd : (TwistTag.D4.orbit b).card = 3 ∨ (TwistTag.D4.orbit b).card = 1 := by
      have : ∀ c : Fin TwistTag.D4.foldedTag.rank,
          (TwistTag.D4.orbit c).card = 3 ∨ (TwistTag.D4.orbit c).card = 1 := by decide
      exact this b
    obtain ⟨i, hi, hie⟩ := (Nat.dvd_prime_pow Nat.prime_five).1
      (show 1 + (2 ^ n) ^ (TwistTag.D4.orbit b).card ∣ 5 ^ 2 by norm_num; exact hBdvd)
    rw [← pow_mul] at hie
    have hpos : 0 < 2 ^ (n * (TwistTag.D4.orbit b).card) := by positivity
    have h3 := not_three_dvd_two_pow_of_d4 (n * (TwistTag.D4.orbit b).card)
    have hcase : 2 ^ (n * (TwistTag.D4.orbit b).card) = 2 ^ 2 := by
      interval_cases i <;> simp at hie <;> omega
    have hnd := Nat.pow_right_injective (le_refl 2) hcase
    have hd1 : (TwistTag.D4.orbit b).card = 1 := by
      rcases hd with hd | hd
      · rw [hd] at hnd
        omega
      · exact hd
    have hn2 : n = 2 := by
      rw [hd1] at hnd
      omega
    have hB5 := not_five_dvd_card_graphFixedRootBorel (t := TwistTag.D4) hσ
      (not_five_dvd_card_sub_one_of_eq_two_pow hn2 hK)
    have hPb := card_graphFixedParabolic_singleton hσ b
    have hq4 : (2 ^ n) ^ (TwistTag.D4.orbit b).card = 4 := by
      rw [hn2, hd1]
      norm_num
    rw [card_graphFixedInversionUnipotent_D4 σ hn hK hσc b, hq4] at hPb
    have hPdvd : 25 ∣ Nat.card (graphFixedParabolic TwistTag.D4 K σ.toRingHom {b}) :=
      (Dvd.intro _ hH.symm).trans (Subgroup.card_dvd_of_le hHb)
    rw [hPb] at hPdvd
    have h55 : 5 * 5 ∣ Nat.card (graphFixedRootBorel TwistTag.D4 K σ.toRingHom) * 5 := by
      simpa using hPdvd
    exact hB5 (Nat.dvd_of_mul_dvd_mul_right (by norm_num) h55)

end Triality

end D4Five

end CFSG.Quasithin.S146zY
