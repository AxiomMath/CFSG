module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMFiveLin
import CFSG.LocalAnalysis.StandardType.GGQTwoDCoxEvenOrbit
import CFSG.LocalAnalysis.StandardType.GGQTwoDRMFormA
import CFSG.LocalAnalysis.StandardType.GGWitOrthPolar
import CFSG.LocalAnalysis.StandardType.ZS.ClassReflClosure
import CFSG.LieType.Universal.SpinOmega.Reflections

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

private lemma dot_eq_two_of_dQuadTwo_eq_one {b : DVec 5} (h : dQuadTwo 5 b = 1) :
    b ⬝ᵥ b = 2 := by
  have h1 : (2 : ZMod 3) * (b ⬝ᵥ b) = 1 := by
    rwa [dQuadTwo_eq_two_dDot, dDot_apply] at h
  have h22 : (2 : ZMod 3) * 2 = 1 := by decide
  calc b ⬝ᵥ b = (2 * 2) * (b ⬝ᵥ b) := by rw [h22, one_mul]
    _ = 2 * (2 * (b ⬝ᵥ b)) := by ring
    _ = 2 * 1 := by rw [h1]
    _ = 2 := by decide

private lemma dot_two_support_dichotomy (b : DVec 5) (h : b ⬝ᵥ b = 2) :
    (∃ i j : Fin 5, i ≠ j ∧ dVecSupp b = {i, j} ∧
        (b i = 1 ∨ b i = -1) ∧ (b j = 1 ∨ b j = -1)) ∨
      (∀ i, b i ≠ 0) := by
  classical
  have hunit : ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = -1 := by decide
  set A : Finset (Fin 5) := dVecSupp b with hA
  have hterm : ∀ i, b i * b i = if i ∈ A then 1 else 0 := by
    intro i
    by_cases hi : b i = 0
    · have hmem : i ∉ A := by
        rw [hA, mem_dVecSupp]
        exact fun hne => hne hi
      rw [hi, if_neg hmem]
      ring
    · have hmem : i ∈ A := by
        rw [hA, mem_dVecSupp]
        exact hi
      rcases hunit (b i) with h0 | h1 | h1
      · exact absurd h0 hi
      · rw [h1, if_pos hmem]
        norm_num
      · rw [h1, if_pos hmem]
        norm_num
  have hsum : ∑ i : Fin 5, b i * b i = (A.card : ZMod 3) := by
    simp_rw [hterm]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard3 : (A.card : ZMod 3) = 2 := by
    rw [← hsum]
    exact h
  have hcard : A.card = 2 ∨ A.card = 5 := by
    set n : ℕ := A.card with hn
    have hn3 : (n : ZMod 3) = 2 := by simpa [hn] using hcard3
    have hle : n ≤ 5 := by
      rw [hn]
      calc A.card ≤ Fintype.card (Fin 5) := Finset.card_le_univ A
        _ = 5 := by simp
    have hn25 : n = 2 ∨ n = 5 := by
      interval_cases n <;> revert hn3 <;> decide
    simpa [hn] using hn25
  rcases hcard with h2 | h5
  · obtain ⟨i, j, hij, hAij⟩ := Finset.card_eq_two.mp h2
    have hb_supp : dVecSupp b = {i, j} := by rw [← hA]; exact hAij
    have hbi : b i = 1 ∨ b i = -1 := by
      have hi : i ∈ A := by rw [hAij]; simp
      rw [hA, mem_dVecSupp] at hi
      rcases hunit (b i) with h0 | h1 | h1
      · exact absurd h0 hi
      · exact Or.inl h1
      · exact Or.inr h1
    have hbj : b j = 1 ∨ b j = -1 := by
      have hj : j ∈ A := by rw [hAij]; simp
      rw [hA, mem_dVecSupp] at hj
      rcases hunit (b j) with h0 | h1 | h1
      · exact absurd h0 hj
      · exact Or.inl h1
      · exact Or.inr h1
    exact Or.inl ⟨i, j, hij, hb_supp, hbi, hbj⟩
  · right
    have hfull : A = Finset.univ := by
      exact Finset.eq_univ_of_card A (by rw [h5, Fintype.card_fin])
    intro i
    have hi : i ∈ A := by rw [hfull]; exact Finset.mem_univ i
    rw [hA, mem_dVecSupp] at hi
    exact hi

private lemma reflect_apply_of_quadTwo {b x : DVec 5} (hb : dQuadTwo 5 b = 1) :
    CFSG.ClassicalGroups.Orthogonal.reflect (dQuadTwo 5) b x =
      x - (b ⬝ᵥ x) • b := by
  rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply (by rw [hb]; decide),
    dQuadTwo_polar_eq, hb, div_one]

private lemma reflect_mem_dEven_of_support_two {b : DVec 5} {i j : Fin 5}
    (hij : i ≠ j) (hb : dQuadTwo 5 b = 1)
    (hbi : b i = 1 ∨ b i = -1) (hbj : b j = 1 ∨ b j = -1)
    (hsupp : ∀ k, k ≠ i → k ≠ j → b k = 0) :
    CFSG.ClassicalGroups.Orthogonal.reflect (dQuadTwo 5) b ∈ dEven 5 := by
  let s : ZMod 3 := if decide (b i * b j = 1) then (-1 : ZMod 3) else 1
  let c : DVec 5 := dBasis 5 i - s • dBasis 5 j
  have hs : s = -(b i * b j) := by
    dsimp [s]
    rcases hbi with h | h <;> rcases hbj with h' | h' <;> rw [h, h'] <;> decide
  have hbi2 : b i * b i = 1 := by
    rcases hbi with h | h <;> rw [h] <;> decide
  have hci : c i = 1 := by
    simp [c, dBasis, Pi.basisFun_apply, hij]
  have hcj : c j = -s := by
    simp [c, dBasis, Pi.basisFun_apply, Ne.symm hij]
  have hck : ∀ k, k ≠ i → k ≠ j → c k = 0 := by
    intro k hki hkj
    simp [c, dBasis, Pi.basisFun_apply, hki, hkj]
  have hbc : b = b i • c := by
    funext k
    by_cases hki : k = i
    · rw [hki]
      change b i = b i * c i
      rw [hci, mul_one]
    · by_cases hkj : k = j
      · rw [hkj]
        change b j = b i * c j
        rw [hcj, hs, neg_neg]
        rw [show b i * (b i * b j) = b j by
          rw [← mul_assoc, hbi2, one_mul]]
      · rw [hsupp k hki hkj]
        change 0 = b i * c k
        rw [hck k hki hkj, mul_zero]
  have hT : ∀ v, CFSG.ClassicalGroups.Orthogonal.reflect (dQuadTwo 5) b v =
      v - dDot 5 c v • c := by
    intro v
    rw [reflect_apply_of_quadTwo hb, hbc, dDot_apply, smul_dotProduct, smul_eq_mul,
      smul_smul, mul_assoc, mul_comm (c ⬝ᵥ v) (b i), ← mul_assoc, hbi2, one_mul]
  have hc : c = dBasis 5 i -
      (if decide (b i * b j = 1) then (-1 : ZMod 3) else 1) • dBasis 5 j := by
    dsimp [c, s]
  have heq : CFSG.ClassicalGroups.Orthogonal.reflect (dQuadTwo 5) b =
      dTau 5 (decide (b i * b j = 1)) i j :=
    eq_dTau_of_dDot_reflection (ε := decide (b i * b j = 1)) hij hc hT
  rw [heq]
  exact dTau_mem_dEven 5 (decide (b i * b j = 1)) hij

private lemma exists_dEven_smul_of_full_support {a b : DVec 5}
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) :
    ∃ (g : DVec 5 ≃ₗ[ZMod 3] DVec 5) (c : ZMod 3),
      g ∈ dEven 5 ∧ c ≠ 0 ∧ g a = c • b := by
  classical
  have hunit : ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = -1 := by decide
  have hae : ∀ i, a i = 1 ∨ a i = -1 := fun i => hunit _ (ha i)
  have hbe : ∀ i, b i = 1 ∨ b i = -1 := fun i => hunit _ (hb i)
  let A : Finset (Fin 5) := Finset.univ.filter fun i => b i * a i = -1
  have hA_mem : ∀ i, i ∈ A ↔ b i * a i = -1 := by
    intro i
    simp [A]
  have hA : dFlip 5 A a = b := by
    funext i
    rw [dFlip_apply]
    rcases hae i with hai | hai <;> rcases hbe i with hbi | hbi <;>
      rw [hai, hbi] <;>
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, hai, hbi] <;> decide
  have hAcompl : dFlip 5 Aᶜ a = -b := by
    funext i
    rw [dFlip_apply, Pi.neg_apply]
    rcases hae i with hai | hai <;> rcases hbe i with hbi | hbi <;>
      rw [hai, hbi] <;>
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl, hai,
        hbi] <;> decide
  by_cases hEven : Even A.card
  · refine ⟨dFlip 5 A, 1, dFlip_mem_dEven 5 hEven, one_ne_zero, ?_⟩
    rw [hA, one_smul]
  · have hOdd : Odd A.card := Nat.not_even_iff_odd.mp hEven
    have hOddFive : Odd (5 : ℕ) := ⟨2, rfl⟩
    have hAcEven : Even Aᶜ.card := by
      rw [Finset.card_compl, Fintype.card_fin]
      exact Nat.Odd.sub_odd hOddFive hOdd
    refine ⟨dFlip 5 Aᶜ, -1, dFlip_mem_dEven 5 hAcEven, by decide, ?_⟩
    rw [hAcompl, neg_one_smul]

private lemma conj_reflect_mem_sup_of_full {a b : DVec 5}
    {t : DVec 5 ≃ₗ[ZMod 3] DVec 5}
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (ht : t = CFSG.ClassicalGroups.Orthogonal.reflect (dQuadTwo 5) a) :
    CFSG.ClassicalGroups.Orthogonal.reflect (dQuadTwo 5) b ∈
      dEven 5 ⊔ Subgroup.zpowers t := by
  obtain ⟨g, c, hg, hc, hga⟩ := exists_dEven_smul_of_full_support ha hb
  have hgIsom : ZS.IsIsom 3 (dQuadTwo 5) g := by
    intro v
    rw [dQuadTwo_eq_two_dDot, dQuadTwo_eq_two_dDot, dEven_dDot hg v v]
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (dQuadTwo 5) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hgIsom
  have hconj : g * CFSG.ClassicalGroups.Orthogonal.reflect (dQuadTwo 5) a * g⁻¹ =
      CFSG.ClassicalGroups.Orthogonal.reflect (dQuadTwo 5) (g a) :=
    CFSG.ClassicalGroups.Orthogonal.reflect_conj hgO a
  have hsq : CFSG.ClassicalGroups.Orthogonal.reflect (dQuadTwo 5) (g a) =
      CFSG.ClassicalGroups.Orthogonal.reflect (dQuadTwo 5) b := by
    rw [hga]
    exact CFSG.LieType.Universal.Spin.reflect_smul_of_ne_zero (Q := dQuadTwo 5) hc b
  rw [← hsq, ← hconj, ← ht]
  refine (dEven 5 ⊔ Subgroup.zpowers t).mul_mem
    ((dEven 5 ⊔ Subgroup.zpowers t).mul_mem ?_ ?_) ?_
  · exact Subgroup.mem_sup_left hg
  · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers_iff.mpr ⟨1, zpow_one t⟩)
  · exact Subgroup.mem_sup_left ((dEven 5).inv_mem hg)

theorem dNormTwo_five_le_sup {t : DVec 5 ≃ₗ[ZMod 3] DVec 5}
    (ht : t ∈ ZS.ClassRefl 3 (dQuadTwo 5) 1) (hnot : t ∉ dEven 5) :
    dNormTwo 5 ≤ dEven 5 ⊔ Subgroup.zpowers t := by
  rw [dNormTwo, Subgroup.closure_le]
  intro s hs
  have hp : (3 : ℕ) ≠ 2 := by norm_num
  have hc : (1 : ZMod 3) ≠ 0 := by decide
  have hQ := dQuadTwo_polar_nondegenerate 5
  obtain ⟨b, hbQ, rfl⟩ := (ZS.mem_classRefl_iff hp hQ hc s).mp hs
  obtain ⟨a, haQ, hta⟩ := (ZS.mem_classRefl_iff hp hQ hc t).mp ht
  rcases dot_two_support_dichotomy b (dot_eq_two_of_dQuadTwo_eq_one hbQ) with
      ⟨i, j, hij, hsuppij, hbi, hbj⟩ | hbfull
  · have hsupp : ∀ k, k ≠ i → k ≠ j → b k = 0 := by
      intro k hki hkj
      by_contra hk
      have hmem : k ∈ dVecSupp b := mem_dVecSupp.mpr hk
      rw [hsuppij] at hmem
      rcases Finset.mem_insert.mp hmem with h | h
      · exact hki h
      · exact hkj (Finset.mem_singleton.mp h)
    exact Subgroup.mem_sup_left
      (reflect_mem_dEven_of_support_two hij hbQ hbi hbj hsupp)
  · rcases dot_two_support_dichotomy a (dot_eq_two_of_dQuadTwo_eq_one haQ) with
        ⟨i, j, hij, hsuppij, hai, haj⟩ | hafull
    · exfalso
      apply hnot
      rw [hta]
      have hsupp : ∀ k, k ≠ i → k ≠ j → a k = 0 := by
        intro k hki hkj
        by_contra hk
        have hmem : k ∈ dVecSupp a := mem_dVecSupp.mpr hk
        rw [hsuppij] at hmem
        rcases Finset.mem_insert.mp hmem with h | h
        · exact hki h
        · exact hkj (Finset.mem_singleton.mp h)
      exact reflect_mem_dEven_of_support_two hij haQ hai haj hsupp
    · exact conj_reflect_mem_sup_of_full hafull hbfull hta

end

end CFSG.StandardType.QTwo

end
