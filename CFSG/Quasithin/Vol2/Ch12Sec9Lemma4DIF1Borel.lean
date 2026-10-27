module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIBN

public section

namespace CFSG.Quasithin.H13.C1294

@[expose] def upperSub : Subgroup (Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2)) where
  carrier := {g | ∀ i j : Fin (3 + 1), j < i → (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)) i j = 0}
  mul_mem' := by
    intro g h hg hh i j hji
    have hg' : ∀ i j : Fin (3 + 1), j < i →
        (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)) i j = 0 := hg
    have hh' : ∀ i j : Fin (3 + 1), j < i →
        (h : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)) i j = 0 := hh
    show ((g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)) *
      (h : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2))) i j = 0
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k < i
    · rw [hg' i k hk, zero_mul]
    · rw [hh' k j (lt_of_lt_of_le hji (not_lt.mp hk)), mul_zero]
  one_mem' := by
    intro i j hji
    exact Matrix.one_apply_ne hji.ne'
  inv_mem' := by
    intro g hg i j hji
    have hg' : ∀ i j : Fin (3 + 1), j < i →
        (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)) i j = 0 := hg
    have hut : (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)).IsUpperTriangular :=
      fun ⦃i j⦄ h => hg' i j h
    have h1 : ((g⁻¹ : Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2)) :
        Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)) *
        (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    have h2 : (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)) *
        ((g⁻¹ : Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2)) :
          Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    letI : Invertible (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)) :=
      ⟨((g⁻¹ : Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2)) :
        Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)), h1, h2⟩
    have hinv := Matrix.blockTriangular_inv_of_blockTriangular (b := id) hut
    rw [Matrix.inv_eq_left_inv h1] at hinv
    exact hinv (show id j < id i from hji)

theorem ub_mem_iff {g : Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2)} :
    g ∈ upperSub ↔
      ∀ i j : Fin (3 + 1), j < i → (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)) i j = 0 :=
  Iff.rfl

private theorem sl4B_def :
    sl4B = (⨆ k, sl4H k) ⊔ CFSG.LieType.Steinberg.posUnipotent sl4D :=
  rfl

private def ubElem (i j : Fin (3 + 1)) (hlt : i < j) (c : ZMod 2) :
    Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2) :=
  Matrix.SpecialLinearGroup.transvection (ne_of_lt hlt) c

private theorem coe_ubElem (i j : Fin (3 + 1)) (hlt : i < j) (c : ZMod 2) :
    (ubElem i j hlt c : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)) =
      1 + Matrix.single i j c :=
  rfl

private def ubGamma (i j : Fin (3 + 1)) : Fin 3 → ℤ :=
  fun k => if (i : ℕ) ≤ (k : ℕ) ∧ (k : ℕ) < (j : ℕ) then 1 else 0

private theorem toStd_ubGamma (i j : Fin (3 + 1)) (hlt : i < j) :
    CFSG.LieType.Universal.SpecialLinear.toStd 3 (ubGamma i j) =
      Pi.single i 1 - Pi.single j 1 := by
  have hlt' : (i : ℕ) < (j : ℕ) := hlt
  funext a
  simp only [CFSG.LieType.Universal.SpecialLinear.toStd, ubGamma, Pi.sub_apply, Pi.single_apply,
    Fin.ext_iff]
  split_ifs <;> omega

private theorem ub_rootSubgroup_le_sl4B {i j : Fin (3 + 1)} (hij : i ≠ j) (hlt : i < j) :
    CFSG.LieType.Universal.SpecialLinear.rootSubgroup 3 (ZMod 2) hij ≤ sl4B := by
  have hγ := toStd_ubGamma i j hlt
  have hroot : ubGamma i j ∈
      CFSG.LieType.RootSystem.roots (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 3) ∅ := by
    rw [CFSG.LieType.Universal.SpecialLinear.roots_eq]
    exact ⟨i, j, hij, hγ⟩
  have hpos : 0 < CFSG.LieType.Steinberg.ht (ubGamma i j) := by
    rw [CFSG.LieType.Universal.SpecialLinear.ht_eq 3 hγ]
    have hlt' : (i : ℕ) < (j : ℕ) := hlt
    omega
  have hmem : ubGamma i j ∈ {γ | γ ∈ sl4D.roots ∧ 0 < CFSG.LieType.Steinberg.ht γ} :=
    ⟨hroot, hpos⟩
  have hle : sl4D.rootGroup (ubGamma i j) ≤ CFSG.LieType.Steinberg.posUnipotent sl4D := by
    unfold CFSG.LieType.Steinberg.posUnipotent
    exact le_iSup₂_of_le (f := fun γ _ => sl4D.rootGroup γ) (ubGamma i j) hmem le_rfl
  have heq : sl4D.rootGroup (ubGamma i j) =
      CFSG.LieType.Universal.SpecialLinear.rootSubgroup 3 (ZMod 2) hij :=
    CFSG.LieType.Universal.SpecialLinear.rootGroup_eq 3 (ZMod 2) hij hγ
  rw [← heq, sl4B_def]
  exact hle.trans le_sup_right

private theorem ub_elem_mem {i j : Fin (3 + 1)} (hlt : i < j) (c : ZMod 2) :
    ubElem i j hlt c ∈ sl4B :=
  ub_rootSubgroup_le_sl4B (ne_of_lt hlt) hlt
    (CFSG.LieType.Universal.SpecialLinear.transvection_mem_rootSubgroup (ne_of_lt hlt) c)

private theorem ub_rootSubgroup_le_upperSub {i j : Fin (3 + 1)} (hij : i ≠ j) (hlt : i < j) :
    CFSG.LieType.Universal.SpecialLinear.rootSubgroup 3 (ZMod 2) hij ≤ upperSub := by
  rintro g hg
  obtain ⟨c, rfl⟩ := (CFSG.LieType.Universal.SpecialLinear.mem_rootSubgroup hij g).mp hg
  rw [ub_mem_iff]
  intro r s hsr
  have hrs : r ≠ s := hsr.ne'
  have hne : ¬ (i = r ∧ j = s) := by
    rintro ⟨rfl, rfl⟩
    exact lt_asymm hlt hsr
  rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.one_apply_ne hrs,
    Matrix.single_apply_of_ne i j c r s hne, zero_add]

private theorem ub_torus_le (k : Fin 3) :
    CFSG.LieType.Universal.SpecialLinear.torus 3 (ZMod 2) k ≤ upperSub := by
  unfold CFSG.LieType.Universal.SpecialLinear.torus
  rw [Subgroup.closure_le]
  rintro h ⟨t, ht⟩
  rw [SetLike.mem_coe, ub_mem_iff]
  intro i j hji
  rw [ht, Matrix.diagonal_apply_ne _ hji.ne']

private theorem ub_posUnipotent_le :
    CFSG.LieType.Steinberg.posUnipotent sl4D ≤ upperSub := by
  unfold CFSG.LieType.Steinberg.posUnipotent
  refine iSup₂_le fun γ hγ => ?_
  obtain ⟨hroot0, hpos0⟩ := hγ
  have hroot : γ ∈ CFSG.LieType.RootSystem.roots
      (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 3) ∅ := hroot0
  rw [CFSG.LieType.Universal.SpecialLinear.roots_eq] at hroot
  obtain ⟨i, j, hij, hγ'⟩ := hroot
  have hlt : i < j := by
    have hht := CFSG.LieType.Universal.SpecialLinear.ht_eq 3 hγ'
    have h2 : (0 : ℤ) < ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) := lt_of_lt_of_eq hpos0 hht
    have h1 : (i : ℕ) < (j : ℕ) := by omega
    exact h1
  have heq : sl4D.rootGroup γ =
      CFSG.LieType.Universal.SpecialLinear.rootSubgroup 3 (ZMod 2) hij :=
    CFSG.LieType.Universal.SpecialLinear.rootGroup_eq 3 (ZMod 2) hij hγ'
  rw [heq]
  exact ub_rootSubgroup_le_upperSub hij hlt

private theorem ub_coe_X (a b c : ZMod 2) :
    ((ubElem 0 1 (by decide) a * ubElem 0 2 (by decide) b * ubElem 0 3 (by decide) c :
        Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2)) :
      Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)) =
      !![1, a, b, c; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_ubElem]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.one_apply] <;> ring

private theorem ub_coe_Y (d e f : ZMod 2) :
    ((ubElem 1 2 (by decide) d * ubElem 1 3 (by decide) e * ubElem 2 3 (by decide) f :
        Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2)) :
      Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)) =
      !![1, 0, 0, 0; 0, 1, d, e + d * f; 0, 0, 1, f; 0, 0, 0, 1] := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_ubElem]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply, Matrix.one_apply] <;> ring

private theorem ub_RN (a b c d e f : ZMod 2) :
    (!![1, a, b, c; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] :
        Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)) *
      !![1, 0, 0, 0; 0, 1, d, e + d * f; 0, 0, 1, f; 0, 0, 0, 1] =
      !![1, a, a * d + b, a * (e + d * f) + b * f + c; 0, 1, d, e + d * f; 0, 0, 1, f;
        0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;> ring

private theorem ub_coe_XY (a b c d e f : ZMod 2) :
    (((ubElem 0 1 (by decide) a * ubElem 0 2 (by decide) b * ubElem 0 3 (by decide) c) *
        (ubElem 1 2 (by decide) d * ubElem 1 3 (by decide) e * ubElem 2 3 (by decide) f) :
        Matrix.SpecialLinearGroup (Fin (3 + 1)) (ZMod 2)) :
      Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)) =
      !![1, a, a * d + b, a * (e + d * f) + b * f + c; 0, 1, d, e + d * f; 0, 0, 1, f;
        0, 0, 0, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, ub_coe_X, ub_coe_Y, ub_RN]

private theorem ub_exists_param (U : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2))
    (h00 : U 0 0 = 1) (h11 : U 1 1 = 1) (h22 : U 2 2 = 1) (h33 : U 3 3 = 1)
    (h10 : U 1 0 = 0) (h20 : U 2 0 = 0) (h30 : U 3 0 = 0)
    (h21 : U 2 1 = 0) (h31 : U 3 1 = 0) (h32 : U 3 2 = 0) :
    ∃ a b c d e f : ZMod 2, U =
      !![1, a, a * d + b, a * (e + d * f) + b * f + c; 0, 1, d, e + d * f; 0, 0, 1, f;
        0, 0, 0, 1] := by
  refine ⟨U 0 1, U 0 2 - U 0 1 * U 1 2,
    U 0 3 - U 0 1 * U 1 3 - (U 0 2 - U 0 1 * U 1 2) * U 2 3,
    U 1 2, U 1 3 - U 1 2 * U 2 3, U 2 3, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [h00, h11, h22, h33, h10, h20, h30, h21, h31, h32] <;> ring

private theorem ub_unit_eq_one : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by
  decide

theorem sl4B_eq_upperSub : sl4B = upperSub := by
  refine le_antisymm ?_ ?_
  · rw [sl4B_def]
    exact sup_le (iSup_le fun k => ub_torus_le k) ub_posUnipotent_le
  · intro g hg
    rw [ub_mem_iff] at hg
    have hut : (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)).IsUpperTriangular :=
      fun ⦃i j⦄ h => hg i j h
    have hdet := Matrix.SpecialLinearGroup.det_coe g
    rw [Matrix.det_of_isUpperTriangular hut] at hdet
    have hdvd : ∀ i : Fin (3 + 1), (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)) i i ∣ 1 := by
      intro i
      have h : (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)) i i ∣
          ∏ k : Fin (3 + 1), (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)) k k :=
        Finset.dvd_prod_of_mem
          (fun k : Fin (3 + 1) => (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)) k k)
          (Finset.mem_univ i)
      rw [hdet] at h
      exact h
    have hdiag : ∀ i : Fin (3 + 1), (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2)) i i = 1 :=
      fun i => ub_unit_eq_one _ (isUnit_of_dvd_one (hdvd i)).ne_zero
    obtain ⟨a, b, c, d, e, f, hU⟩ := ub_exists_param
      (g : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (ZMod 2))
      (hdiag 0) (hdiag 1) (hdiag 2) (hdiag 3) (hg 1 0 (by decide)) (hg 2 0 (by decide))
      (hg 3 0 (by decide)) (hg 2 1 (by decide)) (hg 3 1 (by decide)) (hg 3 2 (by decide))
    have hX : ubElem 0 1 (by decide) a * ubElem 0 2 (by decide) b * ubElem 0 3 (by decide) c ∈
        sl4B :=
      mul_mem (mul_mem (ub_elem_mem _ a) (ub_elem_mem _ b)) (ub_elem_mem _ c)
    have hY : ubElem 1 2 (by decide) d * ubElem 1 3 (by decide) e * ubElem 2 3 (by decide) f ∈
        sl4B :=
      mul_mem (mul_mem (ub_elem_mem _ d) (ub_elem_mem _ e)) (ub_elem_mem _ f)
    have hgXY : g = (ubElem 0 1 (by decide) a * ubElem 0 2 (by decide) b *
        ubElem 0 3 (by decide) c) * (ubElem 1 2 (by decide) d * ubElem 1 3 (by decide) e *
        ubElem 2 3 (by decide) f) := by
      apply Matrix.SpecialLinearGroup.ext
      intro r s
      rw [hU, ub_coe_XY]
    rw [hgXY]
    exact mul_mem hX hY

end CFSG.Quasithin.H13.C1294
