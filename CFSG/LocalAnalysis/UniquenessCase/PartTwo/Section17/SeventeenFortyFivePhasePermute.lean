module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20k
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ro
import CFSG.RankThree.PartTwo.Sec8.HeringU38Tools
import CFSG.GroupTheory.PermutingProducts
import CFSG.Quasithin.Background.HTriPermute
import CFSG.LocalAnalysis.UniquenessCase.UC22P22r
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rm
import CFSG.LocalAnalysis.UniquenessCase.UCFront10

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ASVolI.ChIJK (IsSplitBNPair)
open scoped Pointwise

theorem two_pow_add_one_not_dvd_prime_pow {r : ℕ} (hr : r.Prime) (hr3 : r % 3 = 1) (k j : ℕ) :
    ¬ 2 ^ k + 1 ∣ r ^ j := by
  intro h
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hr).1 h
  have hmod : (2 ^ k + 1) % 3 = 1 := by
    rw [hi, Nat.pow_mod, hr3]
    norm_num
  have h3 : ¬ 3 ∣ 2 ^ k := fun h3 => by
    have := Nat.le_of_dvd two_pos (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega
  omega

theorem le_normalizer_or_fermat_dvd_of_splitBN {K : Type} [Group K] [Finite K]
    {B N : Subgroup K} (hBN : IsSplitBNPair 2 B N) (U : Sylow 2 K) {E : Subgroup K}
    (hE : Odd (Nat.card E)) (hperm : Permutes E (U : Subgroup K)) :
    E ≤ normalizer ((U : Subgroup K) : Set K) ∨ ∃ k : ℕ, 1 ≤ k ∧ 2 ^ k + 1 ∣ Nat.card E := by
  by_cases hY : E ⊔ (U : Subgroup K) ≤ normalizer ((U : Subgroup K) : Set K)
  · exact Or.inl (le_sup_left.trans hY)
  · right
    obtain ⟨k, hk1, hdvd⟩ := uc22p20k_div_of_splitBN hBN U (E ⊔ U) le_sup_right hY
    obtain ⟨a, ha⟩ := U.isPGroup'.exists_card_eq
    have hcop : Nat.Coprime (Nat.card E) (2 ^ a) := hE.coprime_two_right.pow_right a
    have hEU : E ⊓ (U : Subgroup K) = ⊥ :=
      disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard (by rwa [ha]))
    rw [CFSG.Quasithin.H.Tri.card_sup_eq_mul hperm hEU, ha] at hdvd
    have hodd : Nat.Coprime (2 ^ k + 1) (2 ^ a) := by
      refine Nat.Coprime.pow_right a (Nat.Coprime.symm ?_)
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      intro h
      have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
      omega
    exact ⟨k, hk1, hodd.dvd_of_dvd_mul_right hdvd⟩

theorem permutes_inf_inf_of_permutes {Y : Type} [Group Y] [Finite Y] {L A T : Subgroup Y}
    (hL : L.Normal) (hA : Odd (Nat.card A)) (hT : IsPGroup 2 T) (hperm : Permutes A T) :
    Permutes (A ⊓ L) (T ⊓ L) := by
  have hAU : Permutes A (T ⊓ L) := uc22p22r_permutes_inf_odd hA
    (fun u hu => congrArg Subtype.val (pow_card_eq_one' (G := A) (x := ⟨u, hu⟩)))
    Subgroup.le_normalizer_of_normal hT hperm
  exact (CFSG.GroupTheory.permutes_inf_of_le (B := T ⊓ L) (T := A) (N := L) inf_le_right
    hAU.symm).symm

theorem le_normalizer_inf_of_permutes_of_inf_le {Y : Type} [Group Y] [Finite Y]
    {L A T : Subgroup Y} (hL : L.Normal) (hA : Odd (Nat.card A)) (hT : IsPGroup 2 T)
    (hperm : Permutes A T) (hAL : A ⊓ L ≤ normalizer ((T ⊓ L : Subgroup Y) : Set Y)) :
    A ≤ normalizer ((T ⊓ L : Subgroup Y) : Set Y) := by
  have hAU : Permutes A (T ⊓ L) := uc22p22r_permutes_inf_odd hA
    (fun u hu => congrArg Subtype.val (pow_card_eq_one' (G := A) (x := ⟨u, hu⟩)))
    Subgroup.le_normalizer_of_normal hT hperm
  have key : ∀ a ∈ A, ∀ u ∈ T ⊓ L, a * u * a⁻¹ ∈ T ⊓ L := by
    intro a ha u hu
    have hmem : a * u ∈ (A : Set Y) * ((T ⊓ L : Subgroup Y) : Set Y) :=
      Set.mul_mem_mul ha hu
    rw [hAU] at hmem
    obtain ⟨u₂, hu₂, a₂, ha₂, hprod⟩ := hmem
    set θ : Y := a₂ * a⁻¹ with hθdef
    have hθA : θ ∈ A := A.mul_mem ha₂ (A.inv_mem ha)
    have hyL : a * u * a⁻¹ ∈ L := hL.conj_mem u hu.2 a
    have hθeq : θ = u₂⁻¹ * (a * u * a⁻¹) := by
      rw [hθdef, ← hprod]
      group
    have hθL : θ ∈ L :=
      hθeq ▸ L.mul_mem (L.inv_mem hu₂.2) hyL
    have ht : a * u * a⁻¹ = u₂ * θ := by
      rw [hθdef, ← hprod]
      group
    have hθnorm : θ ∈ normalizer ((T ⊓ L : Subgroup Y) : Set Y) := hAL ⟨hθA, hθL⟩
    have hsem : SemiconjBy a u (a * u * a⁻¹) := by
      show a * u = (a * u * a⁻¹) * a
      group
    have hord : orderOf u = orderOf (a * u * a⁻¹) := SemiconjBy.orderOf_eq a hsem
    obtain ⟨k, hk⟩ := hT.exists_orderOf_dvd_pow ⟨u, hu.1⟩
    have hk' : orderOf u ∣ 2 ^ k := by
      simpa [Subgroup.orderOf_mk] using hk
    have hoddθ : Odd (orderOf θ) :=
      hA.of_dvd_nat (Subgroup.orderOf_dvd_natCard A hθA)
    have hcop : Nat.Coprime (orderOf θ) (orderOf (a * u * a⁻¹)) := by
      rw [← hord]
      exact (hoddθ.coprime_two_right.pow_right k).coprime_dvd_right hk'
    exact HeringU38.mem_of_mul_coprime hθnorm hu₂ hcop ht
  intro a ha
  rw [mem_normalizer_iff]
  intro u
  refine ⟨fun hu => key a ha u hu, fun hu => ?_⟩
  have := key a⁻¹ (A.inv_mem ha) _ hu
  simpa [mul_assoc] using this

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

end
