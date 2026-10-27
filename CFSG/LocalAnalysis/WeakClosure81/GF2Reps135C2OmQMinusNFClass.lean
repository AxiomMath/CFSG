module

public import CFSG.LieType.Universal.Spin.Twisted.Short
public import CFSG.RankThree.OrthogonalInvolutions.OmegaClasses
import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalOmegaMinusStd

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.RankThree.OrthogonalInvolutions Module QuadraticMap

theorem omqnf_involution_type {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {y : spinGroup (quadMinus n K b c)}
    (hy : y * y = 1) (hy1 : y ≠ 1) :
    (∃ r : ℕ, 1 ≤ r ∧ 2 * r ≤ n - 1 ∧
        suzukiLetter (quadMinus n K b c) (spinAction (quadMinus n K b c) y) = SuzukiLetter.a ∧
        finrank K (commSpace (spinAction (quadMinus n K b c) y)) = 2 * r) ∨
      (∃ j : ℕ, Odd j ∧ j ≤ n - 1 ∧
        suzukiLetter (quadMinus n K b c) (spinAction (quadMinus n K b c) y) = SuzukiLetter.c ∧
        finrank K (commSpace (spinAction (quadMinus n K b c) y)) = j + 1) := by
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite n K hirr
  have hdim : finrank K (Vm n K) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin]
    omega
  have htt : spinAction (quadMinus n K b c) y * spinAction (quadMinus n K b c) y = 1 := by
    rw [← map_mul, hy, map_one]
  have ht1 : spinAction (quadMinus n K b c) y ≠ 1 := by
    intro h
    exact hy1 (CFSG.StandardType.RootCentOmega.spinAction_quadMinus_injective hirr
      (by rw [h, map_one]))
  have htE : spinAction (quadMinus n K b c) y ∈
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup (quadMinus n K b c) := by
    rw [← range_spinAction_quadMinus hn hirr]
    exact ⟨y, rfl⟩
  have htΩ : spinAction (quadMinus n K b c) y ∈
      omegaGroup (quadMinus n K b c) hQ :=
    CFSG.StandardType.RootCentOmega.elementaryGroup_quadMinus_le_omegaGroup
      (hirr := hirr) hn htE
  have hr_even : Even (finrank K (commSpace (spinAction (quadMinus n K b c) y))) := htΩ.2
  have hr_ge : 1 ≤ finrank K (commSpace (spinAction (quadMinus n K b c) y)) :=
    one_le_finrank_commSpace ht1
  have hr_le : finrank K (commSpace (spinAction (quadMinus n K b c) y)) ≤ n := by
    have := two_mul_finrank_commSpace_le htt
    rw [hdim] at this
    omega
  have hcases : suzukiLetter (quadMinus n K b c) (spinAction (quadMinus n K b c) y) =
        SuzukiLetter.a ∨
      suzukiLetter (quadMinus n K b c) (spinAction (quadMinus n K b c) y) = SuzukiLetter.b ∨
      suzukiLetter (quadMinus n K b c) (spinAction (quadMinus n K b c) y) = SuzukiLetter.c := by
    cases h : suzukiLetter (quadMinus n K b c) (spinAction (quadMinus n K b c) y) <;> simp
  rcases hcases with hsuz | hsuz | hsuz
  · have hzero : ∀ x ∈ commSpace (spinAction (quadMinus n K b c) y), quadMinus n K b c x = 0 :=
      (suzukiLetter_eq_a_iff.mp hsuz).2
    have hr3 : finrank K (commSpace (spinAction (quadMinus n K b c) y)) ≤ n - 1 :=
      CFSG.StandardType.GGOppRadOmega.finrank_le_of_quadMinus hirr hzero
    obtain ⟨k, hk⟩ := hr_even
    exact Or.inl ⟨k, by omega, by omega, hsuz, by omega⟩
  · exfalso
    have hodd : Odd (finrank K (commSpace (spinAction (quadMinus n K b c) y))) :=
      suzukiLetter_eq_b_iff.mp hsuz
    exact Nat.not_odd_iff_even.mpr hr_even hodd
  · obtain ⟨k, hk⟩ := hr_even
    exact Or.inr ⟨2 * k - 1, ⟨k - 1, by omega⟩, by omega, hsuz, by omega⟩

theorem omqnf_exists_conj_of_spinAction_eq {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {y : spinGroup (quadMinus n K b c)} (hy : y * y = 1) (hy1 : y ≠ 1)
    {T : Vm n K ≃ₗ[K] Vm n K}
    (hTO : T ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c)) (hT2 : orderOf T = 2)
    (hlet : suzukiLetter (quadMinus n K b c) T =
      suzukiLetter (quadMinus n K b c) (spinAction (quadMinus n K b c) y))
    (hrank : finrank K (commSpace T) =
      finrank K (commSpace (spinAction (quadMinus n K b c) y)))
    (hnot : ¬(suzukiLetter (quadMinus n K b c) (spinAction (quadMinus n K b c) y) =
        SuzukiLetter.a ∧
      finrank K (commSpace (spinAction (quadMinus n K b c) y)) = n))
    {z : spinGroup (quadMinus n K b c)} (hz : spinAction (quadMinus n K b c) z = T) :
    ∃ g : spinGroup (quadMinus n K b c), g * y * g⁻¹ = z := by
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite n K hirr
  have hdim : finrank K (Vm n K) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin]
    omega
  have htt : spinAction (quadMinus n K b c) y * spinAction (quadMinus n K b c) y = 1 := by
    rw [← map_mul, hy, map_one]
  have ht1 : spinAction (quadMinus n K b c) y ≠ 1 := by
    intro h
    exact hy1 (CFSG.StandardType.RootCentOmega.spinAction_quadMinus_injective hirr
      (by rw [h, map_one]))
  have htO : spinAction (quadMinus n K b c) y ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c) := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    exact map_spinAction (quadMinus n K b c) y v
  have htE : spinAction (quadMinus n K b c) y ∈
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup (quadMinus n K b c) := by
    rw [← range_spinAction_quadMinus hn hirr]
    exact ⟨y, rfl⟩
  have htΩ : spinAction (quadMinus n K b c) y ∈
      omegaGroup (quadMinus n K b c) hQ :=
    CFSG.StandardType.RootCentOmega.elementaryGroup_quadMinus_le_omegaGroup
      (hirr := hirr) hn htE
  have ht2 : orderOf (spinAction (quadMinus n K b c) y) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact htt) ht1
  have hset := omega_conj_eq_of_not_typeA_half hQ hdim htΩ ht2 hnot
  have hmem : T ∈ {x | ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus n K b c),
      g * spinAction (quadMinus n K b c) y * g⁻¹ = x} :=
    (isConj_iff_suzukiLetter_eq hQ htO ht2 hTO hT2).mpr ⟨hlet, hrank⟩
  rw [← hset] at hmem
  obtain ⟨g, hgΩ, hconj⟩ := hmem
  obtain ⟨h, hh⟩ := CFSG.StandardType.GGOppRadOmega.exists_spinAction_eq_of_mem_omegaGroup_minus
    (n := n) hirr hn hgΩ
  refine ⟨h, ?_⟩
  apply CFSG.StandardType.RootCentOmega.spinAction_quadMinus_injective hirr
  rw [map_mul, map_mul, map_inv, hh, hz]
  exact hconj

end CFSG.LocalAnalysis.WeakClosure81
