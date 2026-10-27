module

public import CFSG.LocalAnalysis.WeakClosure81.W16LBorelDefs
public import CFSG.GH74.Uniqueness.Bender.UnitaryIrreducible

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.GH74.Uniqueness.Bender
open Subgroup

section Certified


theorem borel166Conclusion_of_benderType_u3 {K : Type} [Group K] [Finite K] {n e : ℕ}
    (hB : BenderType K n 3 e) (Q : Sylow 2 K) {Y : Subgroup K} (hY : Nat.card Y = 2 ^ n)
    (hYe : IsElemAbelian 2 Y) (hYQ : Y ≤ (Q : Subgroup K)) :
    Borel166Conclusion Y (Q : Subgroup K) := by
  classical
  obtain ⟨t, hc⟩ := hB.exists_benderCore Q
  have hn2 : 2 ≤ n := hB.two_le.2
  have hYZle : Y ≤ rootCenter (Q : Subgroup K) := fun y hy =>
    hc.mem_rootCenter_of_mul_self (hYQ hy) (by simpa [pow_two] using hYe.2 y hy)
  have hYZ : Y = rootCenter (Q : Subgroup K) :=
    Subgroup.eq_of_le_of_card_ge hYZle (by simp [hc.card_center, hY])
  haveI : IsCyclic (cartan (Q : Subgroup K) t) := hc.isCyclic
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := cartan (Q : Subgroup K) t)
  set h : K := (g : K) with hh
  have hgen : ∀ d ∈ cartan (Q : Subgroup K) t, ∃ k : ℤ, h ^ k = d := by
    intro d hd
    have hmem : (⟨d, hd⟩ : cartan (Q : Subgroup K) t) ∈ Subgroup.zpowers g := hg _
    rw [Subgroup.mem_zpowers_iff] at hmem
    obtain ⟨k, hk⟩ := hmem
    refine ⟨k, ?_⟩
    have hk' : ((g ^ k : cartan (Q : Subgroup K) t) : K) = d := congrArg Subtype.val hk
    rw [Subgroup.coe_zpow] at hk'
    simpa [hh] using hk'
  have hmemD : h ∈ cartan (Q : Subgroup K) t := g.2
  have hdB : h ∈ borel (Q : Subgroup K) := cartan_le_borel (Q : Subgroup K) t hmemD
  have hodd : Odd (orderOf h) :=
    Odd.of_dvd_nat hc.odd_card_cartan
      (Subgroup.orderOf_dvd_natCard (cartan (Q : Subgroup K) t) hmemD)
  have h2n : 3 ≤ 2 ^ n - 1 := by
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with he | he
    · exfalso
      have h0 : Nat.card (cartan (Q : Subgroup K) t) = 0 := by
        rw [hc.card_cartan, he, mul_zero]
      have hpos : 0 < Nat.card (cartan (Q : Subgroup K) t) := Nat.card_pos
      omega
    · exact he
  have hDgt1 : 1 < Nat.card (cartan (Q : Subgroup K) t) := by
    rw [hc.card_cartan]
    calc 1 < 3 * 1 := by norm_num
      _ ≤ (2 ^ n - 1) * e := Nat.mul_le_mul h2n he1
  have hj1 : h ≠ 1 := by
    intro h1
    have hg1 : g = 1 := Subtype.ext (by simpa [hh] using h1)
    have hgorder : orderOf g = Nat.card (cartan (Q : Subgroup K) t) :=
      orderOf_eq_card_of_forall_mem_zpowers hg
    have : orderOf g = 1 := by rw [hg1, orderOf_one]
    omega
  have hnormY : h ∈ normalizer (Y : Set K) := by
    rw [hYZ]
    exact Subgroup.mem_normalizer_fintype fun z hz => conj_mem_rootCenter hdB hz
  have hnormP : h ∈ normalizer ((Q : Subgroup K) : Set K) := hdB
  refine ⟨h, hnormY, hnormP, hodd, ?_, ?_⟩
  · intro P₀ hYP₀ hP₀Q hinv
    have hinvD : ∀ d ∈ cartan (Q : Subgroup K) t, ∀ w ∈ P₀, d * w * d⁻¹ ∈ P₀ := by
      intro d hd w hw
      have hnorm : h ∈ Subgroup.normalizer (P₀ : Set K) :=
        Subgroup.mem_normalizer_fintype fun x hx => hinv x hx
      obtain ⟨k, hk⟩ := hgen d hd
      rw [← hk]
      exact (Subgroup.mem_set_normalizer_iff.mp
        ((Subgroup.normalizer (P₀ : Set K)).zpow_mem hnorm k) w).mp hw
    rcases hB.irreducible_unitary Q hc.sq_eq_one hc.not_mem P₀
      (by rw [← hYZ]; exact hYP₀) hP₀Q hinvD with h | h
    · left; rw [hYZ]; exact h
    · exact Or.inr h
  · intro x hxQ hdx
    have hdxZ : h * x * h⁻¹ * x⁻¹ ∈ rootCenter (Q : Subgroup K) := by
      rw [hYZ] at hdx; exact hdx
    rw [hYZ]
    exact hB.fixedPointFree_unitary Q hc.sq_eq_one hc.not_mem hmemD hj1 hxQ hdxZ

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
