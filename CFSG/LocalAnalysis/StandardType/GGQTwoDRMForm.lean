module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMFormB
import CFSG.LocalAnalysis.StandardType.GGDepARefl

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section RootNorm

variable {m : ℕ}

private theorem dBasis_coord (j l : Fin m) : dBasis m j l = if l = j then 1 else 0 := by
  simp [dBasis, Pi.basisFun_apply, Pi.single_apply]

theorem dEven_reflection_norm {r : DVec m ≃ₗ[ZMod 3] DVec m} (hr : r ∈ dEven m) {c : DVec m}
    {φ : Module.Dual (ZMod 3) (DVec m)} (hφ : φ c = 2) (hrv : ∀ v, r v = v - φ v • c) :
    dDot m c c = 2 := by
  obtain ⟨σ, s, hs, hprod, hact⟩ := hr
  have key : ∀ j, φ (dBasis m j) • c = dBasis m j - s j • dBasis m (σ j) := by
    intro j
    have h := hrv (dBasis m j)
    rw [hact j] at h
    rw [h]
    abel
  by_cases hσ : ∃ j, σ j ≠ j
  · obtain ⟨j, hj⟩ := hσ
    have h1 : dDot m (φ (dBasis m j) • c) (φ (dBasis m j) • c) = 2 := by
      rw [key j]
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
        dDot_basis, if_neg (Ne.symm hj), if_neg hj]
      rcases hs j with h | h <;> rw [h] <;> decide
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
    revert h1
    generalize φ (dBasis m j) = a
    generalize dDot m c c = n
    revert a n
    decide
  · exfalso
    push Not at hσ
    have E1 : ∀ j l, φ (dBasis m j) * c l = (1 - s j) * (if j = l then 1 else 0) := by
      intro j l
      have h := congrFun (key j) l
      rw [hσ j] at h
      simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, dBasis_coord] at h
      by_cases hl : l = j
      · subst hl
        simp only at h ⊢
        rw [h]
        ring
      · simp only [if_neg hl, if_neg (Ne.symm hl)] at h ⊢
        rw [h]
        ring
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero] at hφ
      revert hφ
      decide
    obtain ⟨j, hj⟩ : ∃ j, φ (dBasis m j) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have hφ0 : φ = 0 := (dBasis m).ext fun j => by simpa using hcon j
      rw [hφ0, LinearMap.zero_apply] at hφ
      revert hφ
      decide
    have hcl : ∀ l, l ≠ j → c l = 0 := by
      intro l hl
      have h := E1 j l
      rw [if_neg (Ne.symm hl), mul_zero] at h
      exact (mul_eq_zero.mp h).resolve_left hj
    have hcj : c j ≠ 0 := by
      intro h0
      apply hc0
      funext l
      by_cases hl : l = j
      · rw [hl]
        exact h0
      · exact hcl l hl
    have hsj : s j = -1 := by
      have h := E1 j j
      rw [if_pos rfl, mul_one] at h
      have hne : 1 - s j ≠ 0 := by
        rw [← h]
        exact mul_ne_zero hj hcj
      rcases hs j with h1 | h1
      · exact absurd (by rw [h1]; ring) hne
      · exact h1
    have hsk : ∀ k, k ≠ j → s k = 1 := by
      intro k hk
      have h := E1 k k
      rw [if_pos rfl, mul_one, hcl k hk, mul_zero] at h
      exact (sub_eq_zero.mp h.symm).symm
    have hp : ∏ k, s k = s j :=
      Finset.prod_eq_single j (fun k _ hk => hsk k hk) (fun h => absurd (Finset.mem_univ j) h)
    rw [hp, hsj] at hprod
    revert hprod
    decide

end RootNorm

section Conjugate

variable {m : ℕ}

theorem qtwoD_not_conj_neg (hm : 4 ≤ m) {H : Subgroup (DVec m ≃ₗ[ZMod 3] DVec m)}
    (hW : dEven m ≤ H)
    (hTF : ∀ g ∈ H, g ≠ 1 →
      ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ggLinMove g ≤ ggLinFix {g}))
    (hgen : H = Subgroup.closure {t | t ∈ H ∧ GGLinRefl t})
    {g : DVec m ≃ₗ[ZMod 3] DVec m} (hg : g ∈ H) {r : DVec m ≃ₗ[ZMod 3] DVec m}
    (hr : r ∈ dEven m) (hrefl : GGLinRefl r) (i : Fin m) : g * r * g⁻¹ ≠ dNeg m i := by
  intro heq
  have hiso := qtwoD_isometry_of_reflGen hm hW hTF hgen hg
  obtain ⟨c, φ, hφ, hrv⟩ := (ggDepA_linRefl_iff (p := 3) (by norm_num) r).mp hrefl
  have hN := dEven_reflection_norm hr hφ hrv
  have hrc : r c = -c := by
    rw [hrv c, hφ, two_smul]
    abel
  have h1 : g (r c) = dNeg m i (g c) := by
    have h := congrArg (fun T : DVec m ≃ₗ[ZMod 3] DVec m => T (g c)) heq
    simpa [LinearEquiv.mul_apply] using h
  rw [hrc, map_neg] at h1
  have h2 : ∀ k, k ≠ i → g c k = 0 := by
    intro k hk
    have h := congrFun h1 k
    rw [dNeg_apply_coord, if_neg hk, Pi.neg_apply] at h
    have h3 : ∀ x : ZMod 3, -x = x → x = 0 := by decide
    exact h3 _ h
  have h3 : dDot m (g c) (g c) = g c i * g c i := by
    rw [dDot_apply]
    change ∑ k, g c k * g c k = _
    rw [Finset.sum_eq_single i]
    · intro k _ hk
      rw [h2 k hk, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have h4 := hiso c c
  rw [h3, hN] at h4
  revert h4
  generalize g c i = x
  revert x
  decide

end Conjugate

end CFSG.StandardType.QTwo

end
