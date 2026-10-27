module

public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofHJList
import CFSG.RankThree.PartOne.MultRes.ON
import CFSG.Sporadic.ON
public import CFSG.RankThree.PartTwo.KFacts.KS14MultCore

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14

namespace Proof1515

theorem not_sq_dvd_card_triple_ON {p : ℕ} (hp : p.Prime) (hp6 : Nat.Coprime 6 p) (hp7 : p ≠ 7) :
    ¬ p ^ 2 ∣ 1382446517760 := by
  intro hd
  have h2 : Nat.Coprime p 2 := (Nat.Coprime.coprime_dvd_left (by norm_num) hp6).symm
  have h3 : Nat.Coprime p 3 := (Nat.Coprime.coprime_dvd_left (by norm_num) hp6).symm
  have h7 : Nat.Coprime p 7 := (Nat.coprime_primes hp Nat.prime_seven).mpr hp7
  have hc : Nat.Coprime (p ^ 2) (2 ^ 9 * 3 ^ 5 * 7 ^ 3) :=
    Nat.Coprime.mul_right (Nat.Coprime.mul_right (h2.pow 2 9) (h3.pow 2 5)) (h7.pow 2 3)
  have hd' : p ^ 2 ∣ 32395 := by
    rw [show (1382446517760 : ℕ) = 2 ^ 9 * 3 ^ 5 * 7 ^ 3 * 32395 by norm_num] at hd
    exact hc.dvd_of_dvd_mul_left hd
  have hle : p ^ 2 ≤ 32395 := Nat.le_of_dvd (by norm_num) hd'
  have hp180 : p < 180 := by
    by_contra h
    have : 180 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left (not_lt.mp h) 2
    omega
  have hcheck : ∀ q < 180, 2 ≤ q → ¬ q ^ 2 ∣ 32395 := by decide +kernel
  exact hcheck p hp180 hp.two_le hd'

end Proof1515

open Proof1515

theorem ks1515ONMult :
    KS1515ONMult := by
  intro X _ _ Z _ hX hZc hcop hTC
  have : Group.IsPerfect X := hX
  obtain ⟨hc3, ⟨ε⟩⟩ := hTC
  have hcen : Subgroup.center X = (Subgroup.center (X ⧸ Z)).comap (QuotientGroup.mk' Z) := by
    apply le_antisymm
    · intro z hz
      rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Z y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz x]
    · intro k hk
      rw [Subgroup.mem_comap, Subgroup.mem_center_iff] at hk
      have hk' : QuotientGroup.mk' (Subgroup.center X) k ∈
          Subgroup.center (X ⧸ Subgroup.center X) := by
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
        have h1 := hk (QuotientGroup.mk' Z x)
        rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
          QuotientGroup.eq] at h1
        rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
          QuotientGroup.eq]
        exact hZc h1
      rw [Group.IsPerfect.center_quotient_center_eq_bot, Subgroup.mem_bot,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk'
      exact hk'
  have hmap : (Subgroup.center X).map (QuotientGroup.mk' Z) = Subgroup.center (X ⧸ Z) := by
    rw [hcen]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Z) _
  have e : X ⧸ Subgroup.center X ≃* CFSG.Blueprint.NativeSporadic.ON :=
    (QuotientGroup.quotientQuotientEquivQuotient Z (Subgroup.center X) hZc).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hmap).trans ε)
  have h7 : ¬ 7 ∣ Nat.card Z := by
    intro h7
    have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    have h7c : 7 ∣ Nat.card (Subgroup.center X) := h7.trans (Subgroup.card_dvd_of_le hZc)
    obtain ⟨N, hN, π, hperf, -, hsurj, hker, hpg, hne⟩ :=
      CFSG.RankThree.PartOne.Mult.exists_central_p_extension (K := X) h7c
    have : Group.IsPerfect (X ⧸ N) := hperf
    exact hne (CFSG.RankThree.PartOne.MultRes.sporadicKernelTrivial_on_seven (X ⧸ N)
      (X ⧸ Subgroup.center X) π ⟨e⟩ hsurj hker hpg)
  have hXZ : Nat.card (X ⧸ Z) = 1382446517760 := by
    have h1 := (Subgroup.center (X ⧸ Z)).card_mul_index
    rw [hc3, Subgroup.index_eq_card, Nat.card_congr ε.toEquiv, CFSG.Sporadic.ON.card_ON] at h1
    omega
  refine KFacts.KS14.eq_bot_of_isPerfect_of_sylow_comm hZc fun p hp hpZ P => ?_
  have : Fact p.Prime := ⟨hp⟩
  have hp6 : Nat.Coprime 6 p := Nat.Coprime.coprime_dvd_right hpZ hcop
  have hp7 : p ≠ 7 := by
    rintro rfl
    exact h7 hpZ
  refine KFacts.KS14.sylow_comm_of_not_sq_dvd hZc ?_ P
  rw [hXZ]
  exact not_sq_dvd_card_triple_ON hp hp6 hp7


theorem step1515HJList_of_items
    (h148 : Item148R) (hbot : Item145BotS14) (h142 : Item142R)
    (h134 : Item134) (h48 : Sec4.Item4_8) (h135 : Item135Simple) (hA7 : Step1515HJListA7)
    (hcov : Step1515HJListCover) : Step1515HJList :=
  step1515HJList_of h148 hbot h142 h134 h48 h135 ks1515ONMult hA7 hcov

end CFSG.RankThree.PartTwo.Sec15
