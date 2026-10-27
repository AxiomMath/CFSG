module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDCoxEven

public section

namespace CFSG.StandardType.QTwo

private lemma qtwoDB34_smul_basis_inj {m : ℕ} {c c' : ZMod 3} {i j : Fin m}
    (hc : c ≠ 0) (h : c • dBasis m i = c' • dBasis m j) : i = j := by
  by_contra hne
  have hval := congrFun h i
  rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul] at hval
  simp only [dBasis, Pi.basisFun_apply] at hval
  rw [Pi.single_eq_same, Pi.single_eq_of_ne hne, mul_zero, mul_one] at hval
  exact hc hval

private lemma qtwoDB34_smul_basis_eq {m : ℕ} {c c' : ZMod 3} {i j : Fin m} (hc : c ≠ 0)
    (h : c • dBasis m i = c' • dBasis m j) : i = j ∧ c = c' := by
  have hij : i = j := qtwoDB34_smul_basis_inj hc h
  refine ⟨hij, ?_⟩
  rw [← hij] at h
  have hval := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul, dBasis, Pi.basisFun_apply, Pi.single_eq_same,
    mul_one] at hval
  exact hval

theorem ggQTwoDUnit_dEven_fix_decomp {m : ℕ} {c : Fin m} {w : DVec m ≃ₗ[ZMod 3] DVec m}
    (hw : w ∈ dEven m) (hwc : w (Pi.single c 1) = Pi.single c 1) :
    ∃ (σ : Equiv.Perm (Fin m)) (T : Finset (Fin m)), σ c = c ∧ c ∉ T ∧ Even T.card ∧
      ∀ k : Fin m, w (dBasis m k) = (if σ k ∈ T then (-1 : ZMod 3) else 1) • dBasis m (σ k) := by
  obtain ⟨σ, c', hc', hprod, hact⟩ := hw
  have hwc' : w (dBasis m c) = dBasis m c := by
    simpa only [dBasis, Pi.basisFun_apply] using hwc
  have hkey : c' c • dBasis m (σ c) = (1 : ZMod 3) • dBasis m c := by
    rw [← hact c, hwc']
    simp
  have hcc_ne : c' c ≠ 0 := by
    rcases hc' c with h | h <;> rw [h] <;> decide
  obtain ⟨hσc, hcc1⟩ := qtwoDB34_smul_basis_eq hcc_ne hkey
  refine ⟨σ, Finset.univ.filter (fun j => c' (σ.symm j) = -1), hσc, ?_, ?_, ?_⟩
  · intro hmem
    obtain ⟨-, hneg⟩ := Finset.mem_filter.mp hmem
    have hsymm : σ.symm c = c := by simpa [hσc] using Equiv.symm_apply_apply σ c
    rw [hsymm, hcc1] at hneg
    exact absurd hneg (by decide)
  · rw [← neg_one_pow_eq_one_iff_even (show (-1 : ZMod 3) ≠ 1 by decide)]
    have hprod_symm : ∏ i, c' (σ.symm i) = 1 := by
      rw [Equiv.prod_comp σ.symm c', hprod]
    have hcongr : ∏ i, c' (σ.symm i)
        = ∏ i, (if c' (σ.symm i) = -1 then (-1 : ZMod 3) else 1) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      have hval : (if c' (σ.symm i) = -1 then (-1 : ZMod 3) else 1) = c' (σ.symm i) := by
        split_ifs with hc
        · rw [hc]
        · rcases hc' (σ.symm i) with h | h
          · exact h.symm
          · exact absurd h hc
      exact hval.symm
    have hfilter : (∏ i, (if c' (σ.symm i) = -1 then (-1 : ZMod 3) else 1))
        = (-1 : ZMod 3) ^ (Finset.univ.filter (fun j => c' (σ.symm j) = -1)).card := by
      rw [← Finset.prod_filter]
      rw [Finset.prod_const]
    calc (-1 : ZMod 3) ^ (Finset.univ.filter (fun j => c' (σ.symm j) = -1)).card
        = ∏ i, (if c' (σ.symm i) = -1 then (-1 : ZMod 3) else 1) := hfilter.symm
      _ = ∏ i, c' (σ.symm i) := hcongr.symm
      _ = 1 := hprod_symm
  · intro k
    rw [hact k]
    have hscalar : c' k
        = if σ k ∈ Finset.univ.filter (fun j => c' (σ.symm j) = -1) then (-1 : ZMod 3)
          else 1 := by
      by_cases hk : σ k ∈ Finset.univ.filter (fun j => c' (σ.symm j) = -1)
      · rw [if_pos hk]
        have hmem := (Finset.mem_filter.mp hk).2
        rwa [Equiv.symm_apply_apply] at hmem
      · rw [if_neg hk]
        have hmem : c' k ≠ -1 := by
          intro h
          exact hk (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using h⟩)
        rcases hc' k with h | h
        · exact h
        · exact absurd h hmem
    rw [hscalar]

theorem ggQTwoDUnit_dSign_eq_comm {m : ℕ} {a b k : Fin m} (hab : a ≠ b) (hka : k ≠ a)
    (hkb : k ≠ b) :
    dSign m a k = dPerm m (Equiv.swap a k) *
      (dSign m a b * dPerm m (Equiv.swap a k) * dSign m a b) := by
  refine (dBasis m).ext' fun j => ?_
  simp only [LinearEquiv.mul_apply, dSign_apply, map_smul, dPerm_apply, smul_smul,
    Equiv.swap_apply_self]
  have hcoeff : (if j = a ∨ j = k then (-1 : ZMod 3) else 1)
      = (if j = a ∨ j = b then (-1 : ZMod 3) else 1)
        * (if Equiv.swap a k j = a ∨ Equiv.swap a k j = b then (-1 : ZMod 3) else 1) := by
    by_cases hja : j = a
    · subst hja
      simp [Equiv.swap_apply_left, hka, hkb, hab, Ne.symm hka]
    · by_cases hjk : j = k
      · subst hjk
        simp [Equiv.swap_apply_right, hka, hkb, hab]
      · by_cases hjb : j = b
        · subst hjb
          have hsw : Equiv.swap a k j = j :=
            Equiv.swap_apply_of_ne_of_ne (Ne.symm hab) (Ne.symm hkb)
          simp [hsw, Ne.symm hab, Ne.symm hkb] <;> decide
        · have hsw : Equiv.swap a k j = j := Equiv.swap_apply_of_ne_of_ne hja hjk
          simp [hsw, hja, hjk, hjb]
  exact congrArg (fun s : ZMod 3 => s • dBasis m j) hcoeff

end CFSG.StandardType.QTwo

end
