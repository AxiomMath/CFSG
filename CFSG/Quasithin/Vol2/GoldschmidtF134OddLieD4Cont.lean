module

public import CFSG.Quasithin.Vol2.F134LieD4Cells
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieD4Arith
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieD4Borel

public section

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.Quasithin.F134.LieD4

namespace CFSG.Quasithin.H13.NQCore.D4


variable {K : Type} [Field K]

theorem exists_le_graphFixedParabolic_singleton (σ : K ≃+* K)
    {Q : Subgroup (ModGL TwistTag.D4.tag K)}
    (hBQ : graphFixedRootBorel TwistTag.D4 K σ.toRingHom ≤ Q)
    (hQC : Q ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hQ : Q ≠ graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    ∃ b : Fin TwistTag.D4.foldedTag.rank,
      Q ≤ graphFixedParabolic TwistTag.D4 K σ.toRingHom {b} := by
  have hQJ := (fixed_Borel_overgroup_classification TwistTag.D4 K σ Q hBQ hQC).1
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
  refine ⟨⟨1 - a.val, by change 1 - a.val < 2; omega⟩, ?_⟩
  refine hQJ.le.trans (((fixed_standard_parabolic_cells TwistTag.D4 K σ).2.2.2.1 _ {_}).2
    fun j hj => ?_)
  have hja : j ≠ a := fun e => ha (e ▸ hj)
  have hj2 : j.val < 2 := j.2
  rw [Set.mem_singleton_iff, Fin.ext_iff]
  rw [Ne, Fin.ext_iff] at hja
  change j.val = 1 - a.val
  omega

theorem le_graphFixedRootBorel_of_card_eq_prime [Finite K] (σ : K ≃+* K) {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 3) (hσc : ∀ c, σ c = c ^ (2 ^ n)) {p a : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (ha : a = 2 ∨ a = 3) {Q H : Subgroup (ModGL TwistTag.D4.tag K)}
    (hBQ : graphFixedRootBorel TwistTag.D4 K σ.toRingHom ≤ Q)
    (hQC : Q ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hQ : Q ≠ graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (hHQ : H ≤ Q)
    (hUH : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤ H)
    (hH : Nat.card H = p ^ a * Nat.card (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)) :
    H ≤ graphFixedRootBorel TwistTag.D4 K σ.toRingHom := by
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hK3 : Nat.card K = 2 ^ (3 * n) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK3
  have hσ : Function.Surjective σ.toRingHom := σ.surjective
  have hp2 : p ≠ 2 := by omega
  obtain ⟨b, hQb⟩ := exists_le_graphFixedParabolic_singleton σ hBQ hQC hQ
  have hHb := hHQ.trans hQb
  have hUrel : (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).relIndex H = p ^ a := by
    have h := Subgroup.relIndex_mul_card (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) H
    rw [inf_eq_left.2 hUH, hH] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hBdvd : (graphFixedRootBorel TwistTag.D4 K σ.toRingHom).relIndex H ∣ p ^ a :=
    hUrel ▸ Subgroup.relIndex_dvd_of_le_left H graphFixedPosUnipotent_le_graphFixedRootBorel
  rcases le_or_relIndex_eq hσ hUH hHb with hHB | hrel
  · exact hHB
  exfalso
  rw [hrel, card_graphFixedInversionUnipotent_D4 σ hn hK hσc b] at hBdvd
  have hd : (TwistTag.D4.orbit b).card = 1 ∨ (TwistTag.D4.orbit b).card = 3 := by
    have : ∀ c : Fin TwistTag.D4.foldedTag.rank,
        (TwistTag.D4.orbit c).card = 1 ∨ (TwistTag.D4.orbit c).card = 3 := by decide
    exact this b
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 hBdvd
  have hi0 : i ≠ 0 := by
    rintro rfl
    simp at hi
  have hpd : p ∣ 1 + (2 ^ n) ^ (TwistTag.D4.orbit b).card := hi ▸ dvd_pow_self p hi0
  have hpK : ¬ p ∣ Nat.card K - 1 := by
    rw [hK]
    exact not_dvd_pow_three_sub_one hp hp2 (Nat.one_le_two_pow) hd hpd
  have hB := not_dvd_card_graphFixedRootBorel (t := TwistTag.D4) hσ hp hp2 hpK
  have hPb := card_graphFixedParabolic_singleton hσ b
  rw [card_graphFixedInversionUnipotent_D4 σ hn hK hσc b] at hPb
  have hPdvd : p ^ a ∣ Nat.card (graphFixedParabolic TwistTag.D4 K σ.toRingHom {b}) :=
    (Dvd.intro _ hH.symm).trans (Subgroup.card_dvd_of_le hHb)
  rw [hPb] at hPdvd
  exact false_of_dvd_of_dvd_mul hp hp5 ha hB hBdvd hPdvd

end CFSG.Quasithin.H13.NQCore.D4
