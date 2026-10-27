module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open Subgroup

private lemma m4_card_centralizer_conj {G : Type*} [Group G] {x y : G} (h : IsConj x y) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) =
      Nat.card (Subgroup.centralizer ({y} : Set G)) := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj c).toEquiv fun g => ?_)
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
  constructor
  · intro hg
    rw [show c * g * c⁻¹ * (c * x * c⁻¹) = c * (g * x) * c⁻¹ by group, hg]
    group
  · intro hg
    have : c * (g * x) * c⁻¹ = c * (x * g) * c⁻¹ := by
      rw [show c * (g * x) * c⁻¹ = c * g * c⁻¹ * (c * x * c⁻¹) by group, hg]
      group
    simpa using this

theorem exists_commute_isConj_of_not_isConj {G : Type*} [Group G] [Finite G] {c x : G}
    (hcx : ∀ t : G, orderOf t = 2 → IsConj c t ∨ IsConj x t) (hc2 : orderOf c = 2)
    (hord : (Nat.card (Subgroup.centralizer ({c} : Set G))).factorization 2 <
      (Nat.card G).factorization 2) :
    ∀ t : G, orderOf t = 2 → ¬ IsConj c t → ∃ a : G, IsConj c a ∧ a ≠ t ∧ a * t = t * a := by
  intro t ht2 htc
  have hcne1 : c ≠ 1 := by
    rintro rfl
    simp at hc2
  have hP : IsPGroup 2 (zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc2]; norm_num)
  obtain ⟨T, hPT⟩ := hP.exists_le_sylow
  have hcT : c ∈ (T : Subgroup G) := hPT (mem_zpowers c)
  have hTnt : Nontrivial (T : Subgroup G) := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro hbot
    exact hcne1 (Subgroup.mem_bot.1 (hbot ▸ hcT))
  haveI : Nontrivial (T : Subgroup G) := hTnt
  have hTp : IsPGroup 2 (T : Subgroup G) := T.isPGroup'
  have hcnt : Nontrivial (Subgroup.center (T : Subgroup G)) := hTp.center_nontrivial
  have hcp : IsPGroup 2 (Subgroup.center (T : Subgroup G)) := hTp.to_subgroup _
  have hdvd : 2 ∣ Nat.card (Subgroup.center (T : Subgroup G)) := by
    rcases hcp.card_eq_or_dvd with h | h
    · exfalso
      haveI : Nontrivial (Subgroup.center (T : Subgroup G)) := hcnt
      exact not_subsingleton _ (Nat.card_eq_one_iff_unique.1 h).1
    · exact h
  obtain ⟨w0, hw0⟩ :=
    exists_prime_orderOf_dvd_card' (G := Subgroup.center (T : Subgroup G)) 2 hdvd
  let w : G := ((w0 : (T : Subgroup G)) : G)
  have hwdef : w = ((w0 : (T : Subgroup G)) : G) := rfl
  have hw2 : orderOf w = 2 := by
    rw [hwdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hw0
  have hwcent : ∀ p ∈ (T : Subgroup G), p * w = w * p := by
    intro p hp
    have h := congrArg Subtype.val (Subgroup.mem_center_iff.1 w0.2 ⟨p, hp⟩)
    simpa [hwdef] using h
  have hnotconj : ¬ IsConj c w := by
    intro hconj
    have hle : (T : Subgroup G) ≤ Subgroup.centralizer ({w} : Set G) := by
      intro p hp
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hwcent p hp
    have hdvdT : Nat.card (T : Subgroup G) ∣
        Nat.card (Subgroup.centralizer ({w} : Set G)) := Subgroup.card_dvd_of_le hle
    have hTcard : Nat.card (T : Subgroup G) = 2 ^ (Nat.card G).factorization 2 :=
      Sylow.card_eq_multiplicity T
    have hccard : Nat.card (Subgroup.centralizer ({w} : Set G)) =
        Nat.card (Subgroup.centralizer ({c} : Set G)) :=
      (m4_card_centralizer_conj hconj).symm
    have hdvd' : 2 ^ (Nat.card G).factorization 2 ∣
        Nat.card (Subgroup.centralizer ({c} : Set G)) := by
      rw [← hTcard, ← hccard]
      exact hdvdT
    have hle2 : (Nat.card G).factorization 2 ≤
        (Nat.card (Subgroup.centralizer ({c} : Set G))).factorization 2 := by
      haveI : Nonempty (Subgroup.centralizer ({c} : Set G)) :=
        ⟨1, Subgroup.mem_centralizer_singleton_iff.2 (by simp)⟩
      exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 hdvd'
    exact (not_le.2 hord) hle2
  have hxnw : IsConj x w := by
    rcases hcx w hw2 with h | h
    · exact absurd h hnotconj
    · exact h
  have hxnt : IsConj x t := by
    rcases hcx t ht2 with h | h
    · exact absurd h htc
    · exact h
  have hwt : IsConj w t := hxnw.symm.trans hxnt
  obtain ⟨h, hh⟩ := isConj_iff.1 hwt
  have hca : IsConj c (h * c * h⁻¹) := isConj_iff.2 ⟨h, rfl⟩
  refine ⟨h * c * h⁻¹, hca, ?_, ?_⟩
  · intro heq
    exact htc (heq ▸ hca)
  · rw [← hh]
    calc (h * c * h⁻¹) * (h * w * h⁻¹) = h * (c * w) * h⁻¹ := by group
      _ = h * (w * c) * h⁻¹ := by rw [hwcent c hcT]
      _ = (h * w * h⁻¹) * (h * c * h⁻¹) := by group

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
