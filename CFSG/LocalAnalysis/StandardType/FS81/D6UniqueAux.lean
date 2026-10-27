module

public import CFSG.LocalAnalysis.StandardType.FS81.Defs
public import CFSG.LocalAnalysis.StandardType.FS81.Realized
public import CFSG.LocalAnalysis.StandardType.FS81.SpMatAlg
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenDihedral
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.ClassicalInvolution.Asc77.HypOmegaBasic
public import CFSG.ClassicalInvolution.Asc77.Lemma310
public import CFSG.ClassicalInvolution.Asc77.ThmEStatement
public import CFSG.ClassicalInvolution.Asc77.WP1Defs
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearDescentFixedBasis
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

private theorem spMat_apply_eq_of_vanish {σ : Equiv.Perm (Fin 7)} {s : Fin 7 → ZMod 3}
    {v : Coords 7} (him : ∀ w : Coords 7, ∃ c : ZMod 3, spMat σ s *ᵥ w - w = c • v)
    {k : Fin 7} (hk : v k = 0) : σ k = k ∧ s k = 1 := by
  have hcol := Matrix.mulVec_single_one (spMat σ s) k
  obtain ⟨c, hc⟩ := him (Pi.single k 1)
  have hkk : spMat σ s k k = 1 := by
    have h := congrFun hc k
    rw [Pi.sub_apply, hcol, Matrix.col_apply, Pi.single_eq_same, Pi.smul_apply, smul_eq_mul,
      hk, mul_zero] at h
    exact sub_eq_zero.mp h
  by_cases h : k = σ k
  · refine ⟨h.symm, ?_⟩
    rwa [spMat_apply, if_pos h] at hkk
  · rw [spMat_apply, if_neg h] at hkk
    exact absurd hkk (by decide)

private theorem spMat_eq_swap_of_refl {σ : Equiv.Perm (Fin 7)} {s : Fin 7 → ZMod 3}
    {v : Coords 7} {i j : Fin 7} (hij : i ≠ j) (hvi : v i ≠ 0) (hvj : v j ≠ 0)
    (hzero : ∀ k, k ≠ i → k ≠ j → v k = 0)
    (hAv : spMat σ s *ᵥ v = -v)
    (him : ∀ w : Coords 7, ∃ c : ZMod 3, spMat σ s *ᵥ w - w = c • v) :
    (∀ k, k ≠ i → k ≠ j → σ k = k ∧ s k = 1) ∧ σ i = j ∧ σ j = i ∧
      s i * v i = -v j ∧ s j * v j = -v i := by
  have hout : ∀ k, k ≠ i → k ≠ j → σ k = k ∧ s k = 1 :=
    fun k hki hkj => spMat_apply_eq_of_vanish him (hzero k hki hkj)
  have hσi : σ i = i ∨ σ i = j := by
    by_contra h
    push Not at h
    have h0 : σ (σ i) = σ i := (spMat_apply_eq_of_vanish him (hzero (σ i) h.1 h.2)).1
    exact h.1 (σ.injective h0)
  have hσj : σ j = i ∨ σ j = j := by
    by_contra h
    push Not at h
    have h0 : σ (σ j) = σ j := (spMat_apply_eq_of_vanish him (hzero (σ j) h.1 h.2)).1
    exact h.2 (σ.injective h0)
  have hσi_ne : σ i ≠ i := by
    intro hσii
    let e : Coords 7 := Pi.single i 1
    have he : e = Pi.single i 1 := rfl
    obtain ⟨c, hc⟩ := him e
    have hcol_e : spMat σ s *ᵥ e = (spMat σ s).col i := by
      rw [he]
      exact Matrix.mulVec_single_one (spMat σ s) i
    have hej : e j = 0 := by simp [e, Ne.symm hij]
    have hei : e i = 1 := by simp [e]
    have hleft_j : (spMat σ s *ᵥ e) j - e j = 0 := by
      have hji : ¬ (j = σ i) := by rw [hσii]; exact Ne.symm hij
      have hcolj : (spMat σ s *ᵥ e) j = 0 := by
        rw [hcol_e, Matrix.col_apply, spMat_apply, if_neg hji]
      rw [hcolj, hej]
      rfl
    have hc0 : c = 0 := by
      have h := congrFun hc j
      rw [Pi.sub_apply, hleft_j, Pi.smul_apply, smul_eq_mul] at h
      exact (mul_eq_zero.mp h.symm).resolve_right hvj
    have hsi : s i = 1 := by
      have h := congrFun hc i
      rw [Pi.sub_apply, hcol_e, Matrix.col_apply, spMat_apply, if_pos hσii.symm, hei,
        Pi.smul_apply, smul_eq_mul, hc0, zero_mul, sub_eq_zero] at h
      exact h
    have hsymm : σ.symm i = i := by simpa [hσii] using σ.symm_apply_apply i
    have hAv_i : s i * v i = -v i := by
      have h := congrFun hAv i
      simp only [spMat_mulVec, Pi.neg_apply, hsymm] at h
      exact h
    rw [hsi, one_mul] at hAv_i
    have h2 : v i + v i = 0 := by
      have h := congrArg (fun x => x + v i) hAv_i
      rw [h]
      exact neg_add_cancel (v i)
    have h2' : (2 : ZMod 3) * v i = 0 := by
      rw [two_mul]
      exact h2
    exact hvi ((mul_eq_zero.mp h2').resolve_left (by decide))
  have hσij : σ i = j := by
    rcases hσi with h | h
    · exact absurd h hσi_ne
    · exact h
  have hσji : σ j = i := by
    rcases hσj with h | h
    · exact h
    · exact absurd (σ.injective (hσij.trans h.symm)) hij
  have hsi : s i * v i = -v j := by
    have hsymm : σ.symm j = i := by simpa [hσij] using σ.symm_apply_apply i
    have h := congrFun hAv j
    simpa only [spMat_mulVec, Pi.neg_apply, hsymm] using h
  have hsj : s j * v j = -v i := by
    have hsymm : σ.symm i = j := by simpa [hσji] using σ.symm_apply_apply j
    have h := congrFun hAv i
    simpa only [spMat_mulVec, Pi.neg_apply, hsymm] using h
  exact ⟨hout, hσij, hσji, hsi, hsj⟩

theorem eq_of_spMat_refl {A A' : Matrix (Fin 7) (Fin 7) (ZMod 3)} (hA : A ∈ evenFix0 6)
    (hA' : A' ∈ evenFix0 6) {v : Coords 7} (hv0 : v 0 = 0) (hv : wt v = 2)
    (hAv : A *ᵥ v = -v) (hA'v : A' *ᵥ v = -v)
    (himA : ∀ w, ∃ c : ZMod 3, A *ᵥ w - w = c • v)
    (himA' : ∀ w, ∃ c : ZMod 3, A' *ᵥ w - w = c • v) :
    A = A' := by
  classical
  obtain ⟨σ, s, -, -, rfl⟩ := hA
  obtain ⟨σ', s', -, -, rfl⟩ := hA'
  have hwt : (Finset.univ.filter fun k : Fin 7 => v k ≠ 0).card = 2 := hv
  obtain ⟨i, j, hij, hsupp⟩ := Finset.card_eq_two.mp hwt
  have hvi : v i ≠ 0 := by
    have h : i ∈ Finset.univ.filter fun k : Fin 7 => v k ≠ 0 := by rw [hsupp]; simp
    exact (Finset.mem_filter.mp h).2
  have hvj : v j ≠ 0 := by
    have h : j ∈ Finset.univ.filter fun k : Fin 7 => v k ≠ 0 := by rw [hsupp]; simp
    exact (Finset.mem_filter.mp h).2
  have hzero : ∀ k : Fin 7, k ≠ i → k ≠ j → v k = 0 := by
    intro k hki hkj
    by_contra hk
    have h : k ∈ Finset.univ.filter fun x : Fin 7 => v x ≠ 0 :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩
    rw [hsupp] at h
    rcases Finset.mem_insert.mp h with h' | h'
    · exact hki h'
    · exact hkj (Finset.mem_singleton.mp h')
  obtain ⟨hout, hσij, hσji, hsi, hsj⟩ :=
    spMat_eq_swap_of_refl hij hvi hvj hzero hAv himA
  obtain ⟨hout', hσij', hσji', hsi', hsj'⟩ :=
    spMat_eq_swap_of_refl hij hvi hvj hzero hA'v himA'
  have hsi_eq : s i = s' i := mul_right_cancel₀ hvi (hsi.trans hsi'.symm)
  have hsj_eq : s j = s' j := mul_right_cancel₀ hvj (hsj.trans hsj'.symm)
  ext r c
  by_cases hci : c = i
  · subst hci
    rw [spMat_apply, spMat_apply, hσij, hσij', hsi_eq]
  · by_cases hcj : c = j
    · subst hcj
      rw [spMat_apply, spMat_apply, hσji, hσji', hsj_eq]
    · have hc := hout c hci hcj
      have hc' := hout' c hci hcj
      rw [spMat_apply, spMat_apply, hc.1, hc'.1, hc.2, hc'.2]

theorem closure_pair_form {G : Type} [Group G] {h s : G} (hs2 : s * s = 1)
    (hsh : s * h * s⁻¹ = h⁻¹) :
    ∀ x ∈ Subgroup.closure ({h, s} : Set G), ∃ i : ℤ, x = h ^ i ∨ x = h ^ i * s := by
  have hs_inv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hsh' : s * h * s = h⁻¹ := by rwa [hs_inv] at hsh
  have hsh2 : (s * h) * (s * h) = 1 := by
    calc s * h * (s * h) = (s * h * s) * h := by group
      _ = h⁻¹ * h := by rw [hsh']
      _ = 1 := inv_mul_cancel h
  have hsh_eq : s * (s * h) = h := by rw [← mul_assoc, hs2, one_mul]
  have hgen : Subgroup.closure ({s, s * h} : Set G) = Subgroup.closure ({h, s} : Set G) := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro x (hx | hx)
      · rw [hx]
        exact Subgroup.subset_closure (by simp)
      · rw [hx]
        exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
    · rw [Subgroup.closure_le]
      rintro x (hx | hx)
      · rw [hx]
        have hmem : s * (s * h) ∈ Subgroup.closure ({s, s * h} : Set G) :=
          Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
            (Subgroup.subset_closure (by simp))
        rw [hsh_eq] at hmem
        exact hmem
      · rw [hx]
        exact Subgroup.subset_closure (by simp)
  intro x hx
  rw [← hgen] at hx
  obtain ⟨i, hi | hi⟩ :=
    CFSG.ClassicalInvolution.Asc77.Thompson.dihedral_mem_closure (a := s) (b := s * h)
      hs2 hsh2 hx
  · exact ⟨i, Or.inl (by rw [hi, hsh_eq])⟩
  · exact ⟨i, Or.inr (by rw [hi, hsh_eq])⟩

theorem involution_mem_closure_pair {G : Type} [Group G] {h s : G}
    (h3 : h ^ 3 = 1) (hs2 : s * s = 1) (hsh : s * h * s⁻¹ = h⁻¹) {x : G}
    (hx : x ∈ Subgroup.closure ({h, s} : Set G)) (hx2 : x * x = 1) :
    x = 1 ∨ ∃ i : ℤ, x = h ^ i * s := by
  obtain ⟨i, hi | hi⟩ := closure_pair_form hs2 hsh x hx
  · left
    have hx3 : x ^ 3 = 1 := by
      rw [hi]
      have h3z : h ^ (3 : ℤ) = 1 := by
        rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, h3]
      calc (h ^ i) ^ 3 = (h ^ i) ^ (3 : ℤ) := (zpow_natCast (h ^ i) 3).symm
        _ = h ^ (i * 3) := (zpow_mul h i 3).symm
        _ = h ^ (3 * i) := by rw [mul_comm i 3]
        _ = (h ^ 3) ^ i := zpow_mul h 3 i
        _ = 1 := by rw [h3z, one_zpow]
    calc x = x ^ 3 := by rw [pow_succ, pow_two, hx2, one_mul]
      _ = 1 := hx3
  · exact Or.inr ⟨i, hi⟩

theorem conj_eq_zpow_mul_of_conj_eq {G : Type} [Group G] {h s t : G}
    (hs2 : s * s = 1) {i : ℤ} (hi : t * s * t⁻¹ = h ^ i * s) :
    s * t * s⁻¹ = h ^ (-i) * t := by
  have hs_inv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have h2 : s * t⁻¹ * s = t⁻¹ * h ^ i := by
    calc s * t⁻¹ * s = t⁻¹ * (t * s * t⁻¹) * s := by group
      _ = t⁻¹ * (h ^ i * s) * s := by rw [hi]
      _ = t⁻¹ * h ^ i := by rw [mul_assoc, mul_assoc, hs2, mul_one]
  calc s * t * s⁻¹ = (s * t⁻¹ * s)⁻¹ := by
        simp only [mul_inv_rev, inv_inv, hs_inv]
        group
    _ = (t⁻¹ * h ^ i)⁻¹ := by rw [h2]
    _ = h ^ (-i) * t := by rw [mul_inv_rev, inv_inv, ← zpow_neg]

theorem exists_smul_of_mem_zpowers_vec {G : Type} [Group G] [Finite G] {k : ℕ}
    (B : Basis3 G k) {v : Coords k} (hord : orderOf (B.vec v) = 3) {y : G}
    (hy : y ∈ Subgroup.zpowers (B.vec v)) :
    ∃ c : ZMod 3, y = B.vec (c • v) := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hord] at hy
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hy
  rw [Finset.mem_range] at hn
  interval_cases n
  · exact ⟨0, by rw [pow_zero, zero_smul, B.vec_zero]⟩
  · exact ⟨1, by rw [pow_one, one_smul]⟩
  · exact ⟨2, by rw [pow_two, ← B.vec_add, ← two_smul (ZMod 3) v]⟩


end CFSG.StandardType.FrameRoute.FS81

end
