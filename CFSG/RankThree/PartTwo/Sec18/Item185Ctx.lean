module

public import CFSG.RankThree.PartTwo.Sec18.SylowFiveTwo
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec18.Transport

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item185Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly (IsElemAbelian)

variable {G : Type} [Group G] [Finite G]

structure Ctx (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G) (P : Subgroup G) :
    Prop extends Sec18H G A M H c where
  sylow_W : IsSylowOf 3 P (Subgroup.normalizer (A : Set G))
  sylow_G : IsSylowOf 3 P ⊤
  normalizer_le : Subgroup.normalizer (A : Set G) ≤
    Subgroup.normalizer ((A ⊓ inSubgroup perfectResidual H : Subgroup G) : Set G)
  dichotomy : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) ∨
    SylowFive.CaseTwo P A (A ⊓ inSubgroup perfectResidual H) c
  planeQ8 : PlaneQ8 A (A ⊓ inSubgroup perfectResidual H)
    (lc H c ⊓ Subgroup.normalizer (A : Set G)) c

section Certified


theorem ctx_of
    (h1812 : Item181_2) (h184 : Item184_1) (h1842 : Item184_2) (h1846 : Item184_6)
    {A M H : Subgroup G} {c : G} (hH : Sec18H G A M H c) {P : Subgroup G}
    (hP : IsSylowOf 3 P (Subgroup.normalizer (A : Set G))) : Ctx G A M H c P := by
  refine ⟨hH, hP, h1846 G A M H c hH P hP,
    (wStar_structure_of_sec18H h1812 h184 h1842 hH).1, ?_, planeQ8_of_sec18H h1812 h184 hH⟩
  by_cases hWc : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)
  · exact Or.inl hWc
  · exact Or.inr (SylowFive.caseTwo_of_sec18H h1812 h184 h1842 hH hP
      (wStar_structure_of_sec18H h1812 h184 h1842 hH).1 hWc)

end Certified

theorem card_le_of_le_M {A M : Subgroup G} (h : Sec18Std G A M) {E : Subgroup G} (hE : E ≤ M)
    (hEa : IsElemAbelian 3 E) : Nat.card E ≤ 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (Sec5.isPGroup_of_isElemAbelian hEa)
  have h1 : k ≤ CFSG.Assembly.pRank 3 M :=
    Sec5.le_pRank_of_elemAbelian Nat.prime_three hE hEa hk
  have h2 : CFSG.Open.pRank 3 M ≤ 3 :=
    (pRank_le_localRank_of_isTwoLocal Nat.prime_three h.mem_scriptM.1.1).trans
      h.toTheoremFourHyp.localRank_three.le
  have hk3 : k ≤ 3 := h1.trans h2
  rw [hk]
  calc 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
    _ = 27 := by norm_num

theorem card_le_sq_of_le_M {A M : Subgroup G} (h : Sec18Std G A M) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) {E : Subgroup G} (hE : E ≤ M) (hEa : IsElemAbelian p E) :
    Nat.card E ≤ p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (Sec5.isPGroup_of_isElemAbelian hEa)
  have h1 : k ≤ CFSG.Assembly.pRank p M :=
    Sec5.le_pRank_of_elemAbelian hp hE hEa hk
  have h2 : CFSG.Open.pRank p M ≤ 2 := by
    refine (pRank_le_localRank_of_isTwoLocal hp h.mem_scriptM.1.1).trans ?_
    have := h.toTheoremFourHyp.localRank_lt p hp hp3
    omega
  have hk2 : k ≤ 2 := h1.trans h2
  rw [hk]
  exact Nat.pow_le_pow_right hp.pos hk2

private theorem commute_of_sq_commute {x y : G} (hx : ∃ j : ℕ, x ^ 3 ^ j = 1)
    (h : x ^ 2 * y = y * x ^ 2) : x * y = y * x := by
  obtain ⟨j, hj⟩ := hx
  have hcop : Nat.Coprime 2 (orderOf x) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hj)
      (Nat.Coprime.pow_right j (by norm_num))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have h' := (show Commute (x ^ 2) y from h).pow_left m
  rw [hm] at h'
  exact h'

theorem commute_of_normalizes_zpowers {P : Subgroup G} {c : G} (hP : IsPGroup 3 P)
    (hc3 : orderOf c = 3) (h : P ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    ∀ x ∈ P, x * c = c * x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro x hx
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  have hmem : x * c * x⁻¹ ∈ Subgroup.zpowers c :=
    (Subgroup.mem_normalizer_iff.mp (h hx) c).mp (Subgroup.mem_zpowers c)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hk3 : c ^ (k % 3) = x * c * x⁻¹ := by
    have hmod := zpow_mod_orderOf c k
    rw [hc3] at hmod
    rw [← hk]
    exact_mod_cast hmod
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h0 | h1 | h2
  ·
    exfalso
    rw [h0, zpow_zero] at hk3
    have hc1 : c = 1 := by
      calc c = x⁻¹ * (x * c * x⁻¹) * x := by group
        _ = x⁻¹ * 1 * x := by rw [← hk3]
        _ = 1 := by group
    rw [hc1, orderOf_one] at hc3
    exact absurd hc3 (by norm_num)
  ·
    rw [h1, zpow_one] at hk3
    exact mul_inv_eq_iff_eq_mul.mp hk3.symm
  ·
    exfalso
    rw [h2] at hk3
    have hk2 : x * c * x⁻¹ = c ^ 2 := by rw [← hk3]; norm_cast
    have hxc : x * c = c ^ 2 * x := mul_inv_eq_iff_eq_mul.mp hk2
    have hxc2 : x * c ^ 2 = c * x := by
      calc x * c ^ 2 = (x * c) * c := by rw [sq, mul_assoc]
        _ = c ^ 2 * x * c := by rw [hxc]
        _ = c ^ 2 * (x * c) := by group
        _ = c ^ 2 * (c ^ 2 * x) := by rw [hxc]
        _ = c ^ 4 * x := by group
        _ = c * x := by rw [show c ^ 4 = c ^ 3 * c by group, hc3', one_mul]
    have hsq : x ^ 2 * c = c * x ^ 2 := by
      calc x ^ 2 * c = x * (x * c) := by rw [sq, mul_assoc]
        _ = x * (c ^ 2 * x) := by rw [hxc]
        _ = x * c ^ 2 * x := by rw [mul_assoc]
        _ = c * x * x := by rw [hxc2]
        _ = c * x ^ 2 := by rw [sq, mul_assoc]
    obtain ⟨j, hj⟩ := hP ⟨x, hx⟩
    have hxj : x ^ 3 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hcomm : x * c = c * x := commute_of_sq_commute ⟨j, hxj⟩ hsq
    have hcc : c = c ^ 2 := by
      rw [← hk2, hcomm, mul_inv_cancel_right]
    have hc1 : c = 1 := by
      have e : c ^ 3 = c := by
        calc c ^ 3 = c ^ 2 * c := by group
          _ = c * c := by rw [← hcc]
          _ = c ^ 2 := by rw [sq]
          _ = c := hcc.symm
      exact e.symm.trans hc3'
    rw [hc1, orderOf_one] at hc3
    exact absurd hc3 (by norm_num)

end CFSG.RankThree.PartTwo.Sec18.Item185Proof
