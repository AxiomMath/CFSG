module

public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.GroupTheory.HyperplaneGeneration
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
import CFSG.LocalAnalysis.RankThreeEvenClassification.LocalRank

public section

namespace CFSG.RankThree.PartOne.SecRank

open CFSG.Assembly CFSG.Assembly.RankThreeEven

theorem localRank_three_le_of_centralizer {H : Type} [Group H] [Finite H] (m : ℕ)
    (h : ∀ t : H, orderOf t = 2 → ¬ 3 ^ (m + 1) ∣ Nat.card (Subgroup.centralizer ({t} : Set H))) :
    localRank 3 H ≤ m + 1 := by
  by_contra hlt
  obtain ⟨L, hL, hLr⟩ := CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_attained 3
    Nat.prime_three H (by change 0 < localRank 3 H; omega)
  change Assembly.pRank 3 L = localRank 3 H at hLr
  obtain ⟨E, hEL, hE, hEc⟩ := CFSG.RankThreeEvenClassification.Helpers.pRank_attained 3
    Nat.prime_three L
  obtain ⟨P, hP, hP2, rfl⟩ := hL
  set k := Assembly.pRank 3 (Subgroup.normalizer (P : Set H)) with hk
  have hk3 : m + 2 ≤ k := by omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ := Subgroup.conjMulDistribMulActionOfLeNormalizer E P hEL
  have : IsElementaryAbelian 3 E :=
    { toIsMulCommutative := hE.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
        Subtype.ext (hE.2 g g.2) }
  have : Nontrivial E := Finite.one_lt_card_iff_nontrivial.1 (by
    rw [hEc]
    calc 1 < 3 ^ 1 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega))
  have hp : ¬ 3 ∣ Nat.card P := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP2
    rw [hn]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (A := E) (H := P) hp
  obtain ⟨B, hB, hBne⟩ : ∃ B : Subgroup E, B.index = 3 ∧
      CFSG.fixedPointSubgroup B P ≠ ⊥ := by
    by_contra hno
    push Not at hno
    have hP1 : (⊤ : Subgroup P) = ⊥ := by
      rw [← hgen]
      exact iSup_eq_bot.mpr fun B => iSup_eq_bot.mpr fun hB => hno B hB
    apply hP
    rw [eq_bot_iff]
    intro x hx
    have h1 : (⟨x, hx⟩ : P) ∈ (⊥ : Subgroup P) := hP1 ▸ Subgroup.mem_top _
    rw [Subgroup.mem_bot] at h1
    exact (Subgroup.mem_bot).2 (congrArg Subtype.val h1)
  set Q := CFSG.fixedPointSubgroup B P
  have hQ2 : IsPGroup 2 Q := hP2.to_subgroup Q
  have hdvd : 2 ∣ Nat.card Q := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ2
    rcases n with _ | n
    · exact (hBne ((Subgroup.eq_bot_iff_card Q).mpr (by simpa using hn))).elim
    · rw [hn, pow_succ]
      exact dvd_mul_left 2 _
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  set t' : H := ((t : P) : H)
  have ht' : orderOf t' = 2 := by
    rw [show t' = ((t : P) : H) from rfl, Subgroup.orderOf_coe, Subgroup.orderOf_coe, ht]
  have hfix : ∀ b : B, (b : H) * t' * (b : H)⁻¹ = t' := fun b => by
    have h1 : (b : E) • (t : P) = t := t.2 b
    exact congrArg Subtype.val h1
  set B' := B.map E.subtype
  have hB'C : B' ≤ Subgroup.centralizer ({t'} : Set H) := by
    rintro _ ⟨b, hb, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hfix ⟨b, hb⟩
    exact (eq_mul_inv_iff_mul_eq.mp this.symm).symm
  have hBc : Nat.card B' * 3 = 3 ^ k := by
    rw [Subgroup.card_map_of_injective E.subtype_injective]
    have h1 := Subgroup.card_mul_index B
    rw [hB, hEc] at h1
    exact h1
  have h9 : 3 ^ (m + 1) ∣ Nat.card B' := by
    obtain ⟨j, hj⟩ : ∃ j, k = j + m + 2 := ⟨k - (m + 2), by omega⟩
    have : Nat.card B' = 3 ^ (j + m + 1) := by
      have h := hBc
      rw [hj, pow_succ] at h
      omega
    rw [this]
    exact pow_dvd_pow 3 (by omega)
  exact h t' ht' (h9.trans (Subgroup.card_dvd_of_le hB'C))


end CFSG.RankThree.PartOne.SecRank
