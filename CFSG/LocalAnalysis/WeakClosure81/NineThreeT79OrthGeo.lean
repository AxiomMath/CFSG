module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open QuadraticMap

private lemma nine3_polar_self_zero {F M : Type} [Field F] [CharP F 2] [AddCommGroup M]
    [Module F M] (Q : QuadraticMap F M F) (x : M) : polar Q x x = 0 := by
  rw [polar_self, two_smul ℕ (Q x), CharTwo.add_self_eq_zero]

private lemma nine3_polar_comb_left {F M : Type} [Field F] [CharP F 2] [AddCommGroup M]
    [Module F M] (Q : QuadraticMap F M F) (y u v : M) {a b : F} :
    polar Q (y + a • u + b • v) u = polar Q y u + b * polar Q v u := by
  have huu : polar Q u u = 0 := nine3_polar_self_zero Q u
  simp only [polar_add_left, polar_smul_left, huu, smul_zero, mul_zero, add_zero,
    smul_eq_mul]

private lemma nine3_polar_comb_right {F M : Type} [Field F] [CharP F 2] [AddCommGroup M]
    [Module F M] (Q : QuadraticMap F M F) (y u v : M) {a b : F} :
    polar Q (y + a • u + b • v) v = polar Q y v + a * polar Q u v := by
  have hvv : polar Q v v = 0 := nine3_polar_self_zero Q v
  simp only [polar_add_left, polar_smul_left, hvv, smul_zero, mul_zero, add_zero,
    smul_eq_mul]

private lemma nine3_polar_preserve {F M : Type} [Field F] [AddCommGroup M] [Module F M]
    (Q : QuadraticMap F M F) {y u v z : M} {a b : F} (hyu : polar Q y u = 0)
    (hyv : polar Q y v = 0) :
    polar Q y (z + a • u + b • v) = polar Q y z := by
  simp only [polar_add_right, polar_smul_right, hyu, hyv, smul_zero, add_zero]

private lemma nine3_card_two_eq_one {F : Type} [Field F] [Fintype F]
    (h : Fintype.card F = 2) {x : F} (hx : x ≠ 0) : x = 1 := by
  classical
  have hcard2 : ({0, x} : Finset F).card = 2 :=
    Finset.card_pair_eq_two_iff.mpr (Ne.symm hx)
  have hEq : ({0, x} : Finset F) = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      (by rw [Finset.card_univ, h, hcard2])
  have h1 : (1 : F) ∈ ({0, x} : Finset F) := by
    rw [hEq]
    exact Finset.mem_univ 1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with h10 | h1x
  · exact absurd h10 one_ne_zero
  · exact h1x.symm

private lemma nine3_card_two_add_eq_zero {F : Type} [Field F] [Fintype F] [CharP F 2]
    (h : Fintype.card F = 2) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) : x + y = 0 := by
  rw [nine3_card_two_eq_one h hx, nine3_card_two_eq_one h hy]
  exact CharTwo.add_self_eq_zero 1

private lemma nine3_orth_project {F M : Type} [Field F] [CharP F 2] [AddCommGroup M]
    [Module F M] (Q : QuadraticMap F M F) {p q s w y z : M}
    (hpq : polar Q p q ≠ 0) (hsw : polar Q s w ≠ 0)
    (hsp : polar Q s p = 0) (hsq : polar Q s q = 0)
    (hwp : polar Q w p = 0) (hwq : polar Q w q = 0)
    (hyp : polar Q y p = 0) (hyq : polar Q y q = 0)
    (hys : polar Q y s = 0) (hyw : polar Q y w = 0) :
    ∃ z' : M, polar Q z' p = 0 ∧ polar Q z' q = 0 ∧ polar Q z' s = 0 ∧
      polar Q z' w = 0 ∧ polar Q y z' = polar Q y z := by
  set A : F := polar Q z q / polar Q p q with hA
  set B : F := polar Q z p / polar Q p q with hB
  set z₁ : M := z + A • p + B • q with hz₁
  have hz1p : polar Q z₁ p = 0 := by
    rw [hz₁, nine3_polar_comb_left Q z p q, hB, polar_comm Q q p,
      div_mul_cancel₀ _ hpq, CharTwo.add_self_eq_zero]
  have hz1q : polar Q z₁ q = 0 := by
    rw [hz₁, nine3_polar_comb_right Q z p q, hA, div_mul_cancel₀ _ hpq,
      CharTwo.add_self_eq_zero]
  set C : F := polar Q z₁ w / polar Q s w with hC
  set D : F := polar Q z₁ s / polar Q s w with hD
  set z' : M := z₁ + C • s + D • w with hz'
  have hz'p : polar Q z' p = 0 := by
    rw [hz', polar_add_left, polar_add_left, polar_smul_left, polar_smul_left,
      hz1p, hsp, hwp]
    simp
  have hz'q : polar Q z' q = 0 := by
    rw [hz', polar_add_left, polar_add_left, polar_smul_left, polar_smul_left,
      hz1q, hsq, hwq]
    simp
  have hz's : polar Q z' s = 0 := by
    rw [hz', nine3_polar_comb_left Q z₁ s w, hD, polar_comm Q w s,
      div_mul_cancel₀ _ hsw, CharTwo.add_self_eq_zero]
  have hz'w : polar Q z' w = 0 := by
    rw [hz', nine3_polar_comb_right Q z₁ s w, hC, div_mul_cancel₀ _ hsw,
      CharTwo.add_self_eq_zero]
  have hy_z1 : polar Q y z₁ = polar Q y z := by
    rw [hz₁]
    exact nine3_polar_preserve Q hyp hyq
  have hy_z' : polar Q y z' = polar Q y z₁ := by
    rw [hz']
    exact nine3_polar_preserve Q hys hyw
  exact ⟨z', hz'p, hz'q, hz's, hz'w, hy_z'.trans hy_z1⟩

private lemma nine3_orth_exists_w {F M : Type} [Field F] [CharP F 2] [AddCommGroup M]
    [Module F M] (Q : QuadraticMap F M F)
    (hB : ∀ x : M, (∀ y : M, polar Q x y = 0) → x = 0) {p q s : M}
    (hpq : polar Q p q ≠ 0) (hs : Q s ≠ 0) (hsp : polar Q s p = 0)
    (hsq : polar Q s q = 0) :
    ∃ w : M, polar Q w p = 0 ∧ polar Q w q = 0 ∧ polar Q s w ≠ 0 := by
  have hs0 : s ≠ 0 := fun h => hs (by rw [h]; exact QuadraticMap.map_zero Q)
  obtain ⟨y, hy⟩ : ∃ y : M, polar Q s y ≠ 0 := by
    by_contra h
    rw [not_exists] at h
    exact hs0 (hB s (fun z => not_not.1 (h z)))
  refine ⟨y + (polar Q y q / polar Q p q) • p + (polar Q y p / polar Q p q) • q,
    ?_, ?_, ?_⟩
  · rw [nine3_polar_comb_left Q y p q, polar_comm Q q p, div_mul_cancel₀ _ hpq,
      CharTwo.add_self_eq_zero]
  · rw [nine3_polar_comb_right Q y p q, div_mul_cancel₀ _ hpq,
      CharTwo.add_self_eq_zero]
  · rw [nine3_polar_preserve Q hsp hsq]
    exact hy

theorem nine3_orth_exists_nonsing {F M : Type} [Field F] [Finite F] [CharP F 2] [AddCommGroup M]
    [Module F M] [FiniteDimensional F M] (Q : QuadraticMap F M F)
    (hB : ∀ x : M, (∀ y : M, polar Q x y = 0) → x = 0) {p q p' s : M}
    (hp : Q p ≠ 0) (hq : Q q ≠ 0) (hp' : Q p' ≠ 0) (hs : Q s ≠ 0)
    (hpq : polar Q p q ≠ 0) (hp'q : polar Q p' q ≠ 0) (hpp' : polar Q p p' = 0)
    (hne : ∀ t : F, p' ≠ t • p) (hsp : polar Q s p = 0) (hsq : polar Q s q = 0)
    (hsp' : polar Q s p' = 0) :
    ∃ s' : M, Q s' ≠ 0 ∧ polar Q s' p = 0 ∧ polar Q s' q = 0 ∧ polar Q s s' ≠ 0 := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨w, hwp, hwq, hsw⟩ := nine3_orth_exists_w Q hB hpq hs hsp hsq
  have hcard2le : 2 ≤ Fintype.card F := Nat.succ_le_of_lt Fintype.one_lt_card
  rcases lt_or_eq_of_le hcard2le with hgt | heq
  ·
    by_cases hqw : Q w = 0
    · set t₀ : F := -(polar Q s w) / Q s with ht₀
      have hgt' : ({0, t₀} : Finset F).card < (Finset.univ : Finset F).card := by
        rw [Finset.card_univ]
        exact lt_of_le_of_lt Finset.card_le_two hgt
      obtain ⟨t, _, ht⟩ := Finset.exists_mem_notMem_of_card_lt_card
        (s := ({0, t₀} : Finset F)) (t := Finset.univ) hgt'
      have ht' : t ≠ 0 ∧ t ≠ t₀ := by
        simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using ht
      have hQval : Q (w + t • s) = t * (t * Q s + polar Q s w) := by
        rw [QuadraticMap.map_add Q, hqw, QuadraticMap.map_smul, polar_smul_right,
          polar_comm Q w s]
        simp only [zero_add, smul_eq_mul]
        ring
      have hnonzero : t * (t * Q s + polar Q s w) ≠ 0 := by
        apply mul_ne_zero ht'.1
        intro h
        apply ht'.2
        have h' : t * Q s = - polar Q s w := add_eq_zero_iff_eq_neg.mp h
        calc t = t * Q s / Q s := (mul_div_cancel_right₀ t hs).symm
          _ = - polar Q s w / Q s := by rw [h']
          _ = t₀ := ht₀.symm
      refine ⟨w + t • s, ?_, ?_, ?_, ?_⟩
      · rw [hQval]
        exact hnonzero
      · rw [polar_add_left, polar_smul_left, hwp, hsp]
        simp
      · rw [polar_add_left, polar_smul_left, hwq, hsq]
        simp
      · rw [polar_add_right, polar_smul_right, nine3_polar_self_zero Q s, smul_zero,
          add_zero]
        exact hsw
    · exact ⟨w, hqw, hwp, hwq, hsw⟩
  ·
    have hcard : Fintype.card F = 2 := heq.symm
    have hsum_Q : Q p' + Q p = 0 := nine3_card_two_add_eq_zero hcard hp' hp
    have hsum_pq : polar Q p' q + polar Q p q = 0 :=
      nine3_card_two_add_eq_zero hcard hp'q hpq
    by_cases hqw : Q w = 0
    · by_cases hc : polar Q p' w = 0
      · have hp'addp_ne : p' + p ≠ 0 := by
          intro h
          apply hne 1
          have hp2 : p + p = (0 : M) := by
            rw [← two_smul F p,
              show (2 : F) = 0 from CharP.cast_eq_zero (R := F) (p := 2), zero_smul]
          have hneg : (-p : M) = p := (eq_neg_of_add_eq_zero_left hp2).symm
          have h' : p' = -p := eq_neg_of_add_eq_zero_left h
          rw [hneg] at h'
          simpa using h'
        have hyp : polar Q (p' + p) p = 0 := by
          rw [polar_add_left, polar_comm Q p' p, hpp', nine3_polar_self_zero Q p]
          simp
        have hyq : polar Q (p' + p) q = 0 := by
          rw [polar_add_left, hsum_pq]
        have hys : polar Q (p' + p) s = 0 := by
          rw [polar_add_left, polar_comm Q p' s, hsp', polar_comm Q p s, hsp]
          simp
        have hyw : polar Q (p' + p) w = 0 := by
          rw [polar_add_left, hc, polar_comm Q p w, hwp]
          simp
        have hQy : Q (p' + p) = 0 := by
          rw [QuadraticMap.map_add Q, hsum_Q, polar_comm Q p' p, hpp']
          simp
        obtain ⟨z, hz⟩ : ∃ z : M, polar Q (p' + p) z ≠ 0 := by
          by_contra h
          rw [not_exists] at h
          exact hp'addp_ne (hB (p' + p) (fun z => not_not.1 (h z)))
        obtain ⟨z', hz'p, hz'q, hz's, hz'w, hyz'⟩ :=
          nine3_orth_project (Q := Q) (p := p) (q := q) (s := s) (w := w)
            (y := p' + p) (z := z) hpq hsw hsp hsq hwp hwq hyp hyq hys hyw
        have hyz'_ne : polar Q (p' + p) z' ≠ 0 := by
          rw [hyz']
          exact hz
        by_cases hqz : Q z' = 0
        · refine ⟨w + (p' + p + z'), ?_, ?_, ?_, ?_⟩
          · have hw_y : polar Q w (p' + p) = 0 := by
              rw [polar_comm Q w (p' + p), hyw]
            have hw_z' : polar Q w z' = 0 := by
              rw [polar_comm Q w z', hz'w]
            have hw_u : polar Q w (p' + p + z') = 0 := by
              rw [polar_add_right, hw_y, hw_z', add_zero]
            have hQu : Q (p' + p + z') = polar Q (p' + p) z' := by
              rw [QuadraticMap.map_add Q, hQy, hqz]
              simp
            have hQs' : Q (w + (p' + p + z')) = polar Q (p' + p) z' := by
              rw [QuadraticMap.map_add Q, hqw, hw_u, hQu]
              simp
            rw [hQs']
            exact hyz'_ne
          · rw [polar_add_left, hwp, polar_add_left, hyp, hz'p]
            simp
          · rw [polar_add_left, hwq, polar_add_left, hyq, hz'q]
            simp
          · have hsu : polar Q s (p' + p + z') = 0 := by
              have hs_y : polar Q s (p' + p) = 0 := by
                rw [polar_comm Q s (p' + p), hys]
              have hs_z' : polar Q s z' = 0 := by
                rw [polar_comm Q s z', hz's]
              rw [polar_add_right, hs_y, hs_z', add_zero]
            rw [polar_add_right, hsu, add_zero]
            exact hsw
        · refine ⟨w + z', ?_, ?_, ?_, ?_⟩
          · have hw_z' : polar Q w z' = 0 := by
              rw [polar_comm Q w z', hz'w]
            rw [QuadraticMap.map_add Q, hqw, hw_z']
            simpa using hqz
          · rw [polar_add_left, hwp, hz'p]
            simp
          · rw [polar_add_left, hwq, hz'q]
            simp
          · rw [polar_add_right, polar_comm Q s z', hz's]
            simpa using hsw
      · refine ⟨p' + p + w, ?_, ?_, ?_, ?_⟩
        · have hQ1 : Q (p' + p) = 0 := by
            rw [QuadraticMap.map_add Q, hsum_Q, polar_comm Q p' p, hpp']
            simp
          have hQ2 : polar Q (p' + p) w = polar Q p' w := by
            rw [polar_add_left, polar_comm Q p w, hwp]
            simp
          rw [QuadraticMap.map_add Q, hQ1, hqw, hQ2]
          simpa using hc
        · rw [polar_add_left, polar_add_left, hwp, polar_comm Q p' p, hpp',
            nine3_polar_self_zero Q p]
          simp
        · rw [polar_add_left, polar_add_left, hwq, hsum_pq]
          simp
        · rw [polar_add_right, polar_add_right, hsp', hsp]
          simpa using hsw
    · exact ⟨w, hqw, hwp, hwq, hsw⟩

end CFSG.LocalAnalysis.WeakClosure81
