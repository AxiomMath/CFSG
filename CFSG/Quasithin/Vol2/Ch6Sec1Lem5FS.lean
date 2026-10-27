module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFlag5
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherMaximalParabolics

public section

namespace CFSG.Quasithin.H13

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.QuasithinUnique.Vol2Native.A312L
open scoped MatrixGroups

section Flag

variable {K : Type*} [Field K] {k : ℕ}

theorem cut_or_cut_of_isSolvable_ch615 [Finite K] (hK : Nat.card K = 2) {I : Set ℕ}
    (hI : Group.IsSolvable ↥(flagStabilizer k K I)) {i : ℕ} (hi : 1 ≤ i) (hik : i + 1 < k) :
    i ∈ I ∨ i + 1 ∈ I := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hiI, hi1I⟩ := hcon
  obtain ⟨a, b, hai, hib, hbk, ha, hb, hno⟩ := exists_maxBlock (I := I) i (by omega : i < k)
  have ha' : a < i := by
    rcases Nat.lt_or_ge a i with h | h
    · exact h
    · have hai' : a = i := le_antisymm hai h
      subst hai'
      rcases ha with h0 | haI
      · omega
      · exact absurd haI hiI
  have hb' : i + 1 < b := by
    rcases Nat.lt_or_ge (i + 1) b with h | h
    · exact h
    · have hbi : b = i + 1 := le_antisymm h hib
      subst hbi
      rcases hb with hbk' | hbI
      · omega
      · exact absurd hbI hi1I
  have hm3 : 3 ≤ b - a := by omega
  have hab : a + (b - a) = b := by omega
  have hsurj := bigBlockHom_surjective (n := k) (K := K) hK (I := I) (a := a) (m := b - a)
    (by omega) hm3 ha (by rw [hab]; exact hb) (by rw [hab]; exact hno)
  have hbot := (isSolvable_iff_perfectCore_eq_bot (flagStabilizer k K I)).mp hI
  obtain ⟨x, y, hxy⟩ := sl_nonabelian_of_card_two hK hm3
  apply hxy
  obtain ⟨x', rfl⟩ := hsurj x
  obtain ⟨y', rfl⟩ := hsurj y
  have hx1 : x' = 1 := Subtype.ext ((Subgroup.eq_bot_iff_forall _).mp hbot _ x'.2)
  have hy1 : y' = 1 := Subtype.ext ((Subgroup.eq_bot_iff_forall _).mp hbot _ y'.2)
  rw [hx1, hy1]

theorem not_cut_and_cut_of_sup_eq_top_ch615 {I J : Set ℕ}
    (h : flagStabilizer k K I ⊔ flagStabilizer k K J = ⊤) {d : ℕ} (hd : 1 ≤ d) (hdk : d < k) :
    ¬ (d ∈ I ∧ d ∈ J) := by
  rintro ⟨hdI, hdJ⟩
  apply stabilizer_flagSpace_ne_top (K := K) hd hdk
  rw [eq_top_iff, ← h]
  exact sup_le (fun x hx => mem_flagStabilizer.mp hx d hdI)
    (fun x hx => mem_flagStabilizer.mp hx d hdJ)

theorem col_eq_single_of_mem_stabilizer_ch615 [Finite K] (hK : Nat.card K = 2) (hk : 0 < k)
    {x : SpecialLinearGroup (Fin k) K} (hx : x ∈ stabilizer (flagSpace k K 1)) :
    (x : Matrix (Fin k) (Fin k) K) *ᵥ Pi.single ⟨0, hk⟩ 1 = Pi.single ⟨0, hk⟩ 1 := by
  classical
  set z : Fin k := ⟨0, hk⟩ with hz
  have hle : ∀ j : Fin k, j ≠ z → 1 ≤ (j : ℕ) := fun j hj => by
    have : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h)
    omega
  have hez : (Pi.single z 1 : Fin k → K) ∈ flagSpace k K 1 := by
    rw [mem_flagSpace]
    intro j hj
    have : j ≠ z := fun h => by rw [h] at hj; simp [hz] at hj
    simp [this]
  have hxe : (x : Matrix (Fin k) (Fin k) K) *ᵥ Pi.single z 1 ∈ flagSpace k K 1 := by
    rw [← mem_stabilizer.mp hx]
    exact ⟨_, hez, rfl⟩
  have hcol : ∀ i : Fin k, i ≠ z → (x : Matrix (Fin k) (Fin k) K) i z = 0 := by
    intro i hi
    have := (mem_flagSpace.mp hxe) i (hle i hi)
    simpa [mulVec_single_one] using this
  have hzz : (x : Matrix (Fin k) (Fin k) K) z z = 1 := by
    rcases eq_zero_or_eq_one_of_card_two hK ((x : Matrix (Fin k) (Fin k) K) z z) with h0 | h1
    · exfalso
      have hdet := x.2
      rw [Matrix.det_eq_zero_of_column_eq_zero z fun i => by
        by_cases hi : i = z
        · rw [hi, h0]
        · exact hcol i hi] at hdet
      exact zero_ne_one hdet
    · exact h1
  ext i
  rw [mulVec_single_one]
  by_cases hi : i = z
  · subst hi
    simp [hzz]
  · simp [Matrix.col_apply, hcol i hi, hi]

theorem row_eq_single_of_mem_stabilizer_ch615 [Finite K] (hK : Nat.card K = 2) (hk : 0 < k)
    {x : SpecialLinearGroup (Fin k) K} (hx : x ∈ stabilizer (flagSpace k K (k - 1))) :
    Pi.single ⟨k - 1, by omega⟩ 1 ᵥ* (x : Matrix (Fin k) (Fin k) K) =
      Pi.single ⟨k - 1, by omega⟩ 1 := by
  classical
  set w : Fin k := ⟨k - 1, by omega⟩ with hw
  have hlt : ∀ j : Fin k, j ≠ w → (j : ℕ) < k - 1 := fun j hj => by
    have : (j : ℕ) ≠ k - 1 := fun h => hj (Fin.ext h)
    have := j.2
    omega
  have hrow : ∀ j : Fin k, j ≠ w → (x : Matrix (Fin k) (Fin k) K) w j = 0 := by
    intro j hj
    have hej : (Pi.single j 1 : Fin k → K) ∈ flagSpace k K (k - 1) := by
      rw [mem_flagSpace]
      intro i hi
      have : i ≠ j := fun h => by have := hlt j hj; rw [h] at hi; omega
      simp [this]
    have hxe : (x : Matrix (Fin k) (Fin k) K) *ᵥ Pi.single j 1 ∈ flagSpace k K (k - 1) := by
      rw [← mem_stabilizer.mp hx]
      exact ⟨_, hej, rfl⟩
    have := (mem_flagSpace.mp hxe) w (by simp [hw])
    simpa [mulVec_single_one] using this
  have hww : (x : Matrix (Fin k) (Fin k) K) w w = 1 := by
    rcases eq_zero_or_eq_one_of_card_two hK ((x : Matrix (Fin k) (Fin k) K) w w) with h0 | h1
    · exfalso
      have hdet := x.2
      rw [Matrix.det_eq_zero_of_row_eq_zero w fun j => by
        by_cases hj : j = w
        · rw [hj, h0]
        · exact hrow j hj] at hdet
      exact zero_ne_one hdet
    · exact h1
  ext j
  rw [single_one_vecMul]
  by_cases hj : j = w
  · subst hj
    simp [hww]
  · simp [Matrix.row_apply, hrow j hj, hj]

theorem natFix_ch615 [Finite K] (hK : Nat.card K = 2) {I : Set ℕ} (h1 : 1 ∈ I)
    {v : Fin k → K} (hv : ∀ u ∈ unitriangular k K, (u : Matrix (Fin k) (Fin k) K) *ᵥ v = v)
    {x : SpecialLinearGroup (Fin k) K} (hx : x ∈ flagStabilizer k K I) :
    (x : Matrix (Fin k) (Fin k) K) *ᵥ v = v := by
  classical
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    ext i
    exact i.elim0
  set z : Fin k := ⟨0, hkpos⟩ with hz
  have hne : ∀ j : Fin k, j ≠ z → z < j := by
    intro j hj
    rw [Fin.lt_def]
    have : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h)
    simp only [hz]
    omega
  have hvj : ∀ j : Fin k, j ≠ z → v j = 0 := by
    intro j hj
    have h1' := hv _ (transvection_mem_unitriangular (hne j hj) 1)
    rw [SpecialLinearGroup.transvection_coe, add_mulVec, one_mulVec, single_mulVec_eq] at h1'
    have h2 := congrFun h1' z
    simpa using h2
  have hve : v = v z • (Pi.single z 1 : Fin k → K) := by
    ext j
    by_cases hj : j = z
    · subst hj
      simp
    · simp [hvj j hj, hj]
  rw [hve, mulVec_smul, col_eq_single_of_mem_stabilizer_ch615 hK hkpos
    (mem_flagStabilizer.mp hx 1 h1)]

theorem dualFix_ch615 [Finite K] (hK : Nat.card K = 2) {I : Set ℕ} (h1 : k - 1 ∈ I)
    {v : Fin k → K}
    (hv : ∀ u ∈ unitriangular k K,
      ((u⁻¹ : SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K)ᵀ *ᵥ v = v)
    {x : SpecialLinearGroup (Fin k) K} (hx : x ∈ flagStabilizer k K I) :
    ((x⁻¹ : SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K)ᵀ *ᵥ v = v := by
  classical
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    ext i
    exact i.elim0
  set w : Fin k := ⟨k - 1, by omega⟩ with hw
  have hv' : ∀ u ∈ unitriangular k K, v ᵥ* (u : Matrix (Fin k) (Fin k) K) = v := by
    intro u hu
    have := hv _ ((unitriangular k K).inv_mem hu)
    rwa [inv_inv, mulVec_transpose] at this
  have hne : ∀ j : Fin k, j ≠ w → j < w := by
    intro j hj
    rw [Fin.lt_def]
    have : (j : ℕ) ≠ k - 1 := fun h => hj (Fin.ext h)
    have := j.2
    simp only [hw]
    omega
  have hvj : ∀ j : Fin k, j ≠ w → v j = 0 := by
    intro j hj
    have h1' := hv' _ (transvection_mem_unitriangular (hne j hj) 1)
    rw [SpecialLinearGroup.transvection_coe, vecMul_add, vecMul_one] at h1'
    have h2 := congrFun h1' w
    simpa [vecMul, dotProduct, Matrix.single_apply, (hne j hj).ne] using h2
  have hve : v = v w • (Pi.single w 1 : Fin k → K) := by
    ext j
    by_cases hj : j = w
    · subst hj
      simp
    · simp [hvj j hj, hj]
  have hxs : x⁻¹ ∈ stabilizer (flagSpace k K (k - 1)) :=
    (stabilizer (flagSpace k K (k - 1))).inv_mem (mem_flagStabilizer.mp hx (k - 1) h1)
  rw [mulVec_transpose, hve, smul_vecMul, row_eq_single_of_mem_stabilizer_ch615 hK hkpos hxs]

end Flag

section E9

open Equiv

@[expose] def m01_ch615 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![0, 1, 0, 0, 0; 1, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

@[expose] def m12_ch615 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 1, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

@[expose] def m23_ch615 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 1, 0; 0, 0, 0, 0, 1]

@[expose] def m34_ch615 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 1; 0, 0, 0, 1, 1]

theorem m01_cube_ch615 : m01_ch615 * m01_ch615 * m01_ch615 = 1 := by decide
theorem m12_cube_ch615 : m12_ch615 * m12_ch615 * m12_ch615 = 1 := by decide
theorem m23_cube_ch615 : m23_ch615 * m23_ch615 * m23_ch615 = 1 := by decide
theorem m34_cube_ch615 : m34_ch615 * m34_ch615 * m34_ch615 = 1 := by decide

theorem det_eq_one_of_cube_ch615 {A : Matrix (Fin 5) (Fin 5) (ZMod 2)} (h : A * A * A = 1) :
    A.det = 1 := by
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_one] at this
  revert this
  generalize A.det = d
  revert d
  decide

theorem eq_of_mem_zpowers_three_ch615 {Γ : Type*} [Group Γ] {x y : Γ} (hx : x ^ 3 = 1)
    (hy : y ∈ Subgroup.zpowers x) : y = 1 ∨ y = x ∨ y = x * x := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hj : x ^ j = x ^ (j % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv j 3]
    rw [_root_.zpow_add, _root_.zpow_mul, show ((3 : ℤ)) = ((3 : ℕ) : ℤ) from rfl,
      _root_.zpow_natCast, hx, _root_.one_zpow, mul_one]
  rw [hj]
  have h0 := Int.emod_nonneg j (by norm_num : (3 : ℤ) ≠ 0)
  have h3 := Int.emod_lt_of_pos j (by norm_num : (0 : ℤ) < 3)
  generalize j % 3 = r at h0 h3 ⊢
  interval_cases r
  · exact Or.inl (zpow_zero x)
  · exact Or.inr (Or.inl (zpow_one x))
  · exact Or.inr (Or.inr (zpow_two x))

@[expose] def slOfCube_ch615 (m : Matrix (Fin 5) (Fin 5) (ZMod 2)) (h : m * m * m = 1) :
    SpecialLinearGroup (Fin 5) (ZMod 2) :=
  ⟨m, det_eq_one_of_cube_ch615 h⟩

theorem slOfCube_pow_three_ch615 (m : Matrix (Fin 5) (Fin 5) (ZMod 2)) (h : m * m * m = 1) :
    slOfCube_ch615 m h ^ 3 = 1 := by
  apply Subtype.ext
  show m ^ 3 = 1
  rw [pow_succ, pow_two]
  exact h

theorem m01_m23_comm_ch615 : m01_ch615 * m23_ch615 = m23_ch615 * m01_ch615 := by decide

theorem m12_m34_comm_ch615 : m12_ch615 * m34_ch615 = m34_ch615 * m12_ch615 := by decide

theorem m23_ne_ch615 : m23_ch615 ≠ 1 ∧ m23_ch615 ≠ m01_ch615 ∧
    m23_ch615 ≠ m01_ch615 * m01_ch615 := by decide

theorem m34_ne_ch615 : m34_ch615 ≠ 1 ∧ m34_ch615 ≠ m12_ch615 ∧
    m34_ch615 ≠ m12_ch615 * m12_ch615 := by decide

theorem m01_ne_one_ch615 : m01_ch615 ≠ 1 := by decide
theorem m12_ne_one_ch615 : m12_ch615 ≠ 1 := by decide

theorem m01_low_ch615 : ∀ a b : Fin 5, b < a → m01_ch615 a b ≠ 0 → (a : ℕ) = 1 ∧ (b : ℕ) = 0 := by
  intro a b
  fin_cases a <;> fin_cases b <;> decide
theorem m12_low_ch615 : ∀ a b : Fin 5, b < a → m12_ch615 a b ≠ 0 → (a : ℕ) = 2 ∧ (b : ℕ) = 1 := by
  intro a b
  fin_cases a <;> fin_cases b <;> decide
theorem m23_low_ch615 : ∀ a b : Fin 5, b < a → m23_ch615 a b ≠ 0 → (a : ℕ) = 3 ∧ (b : ℕ) = 2 := by
  intro a b
  fin_cases a <;> fin_cases b <;> decide
theorem m34_low_ch615 : ∀ a b : Fin 5, b < a → m34_ch615 a b ≠ 0 → (a : ℕ) = 4 ∧ (b : ℕ) = 3 := by
  intro a b
  fin_cases a <;> fin_cases b <;> decide

theorem mem_flagStabilizer_of_low_ch615 {I : Set ℕ} {c : ℕ} (hc : c ∉ I)
    {x : SpecialLinearGroup (Fin 5) (ZMod 2)}
    (hlow : ∀ a b : Fin 5, b < a → (x : Matrix (Fin 5) (Fin 5) (ZMod 2)) a b ≠ 0 →
      (a : ℕ) = c ∧ (b : ℕ) = c - 1) : x ∈ flagStabilizer 5 (ZMod 2) I := by
  refine mem_flagStabilizer_of_entries fun a b d hd hbd hda => ?_
  by_contra hne
  have hba : b < a := by rw [Fin.lt_def]; omega
  obtain ⟨ha, hb⟩ := hlow a b hba hne
  have : d = c := by omega
  exact hc (this ▸ hd)

theorem exists_e9_ch615 {I : Set ℕ} (h : (1 ∉ I ∧ 3 ∉ I) ∨ (2 ∉ I ∧ 4 ∉ I)) :
    ∃ x ∈ flagStabilizer 5 (ZMod 2) I, ∃ y ∈ flagStabilizer 5 (ZMod 2) I,
      x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y = y * x ∧ x ≠ 1 ∧ y ∉ Subgroup.zpowers x := by
  have key : ∀ (mx my : Matrix (Fin 5) (Fin 5) (ZMod 2)) (hx : mx * mx * mx = 1)
      (hy : my * my * my = 1), mx * my = my * mx → mx ≠ 1 →
      (my ≠ 1 ∧ my ≠ mx ∧ my ≠ mx * mx) →
      slOfCube_ch615 mx hx ^ 3 = 1 ∧ slOfCube_ch615 my hy ^ 3 = 1 ∧
        slOfCube_ch615 mx hx * slOfCube_ch615 my hy =
          slOfCube_ch615 my hy * slOfCube_ch615 mx hx ∧
        slOfCube_ch615 mx hx ≠ 1 ∧
        slOfCube_ch615 my hy ∉ Subgroup.zpowers (slOfCube_ch615 mx hx) := by
    intro mx my hx hy hc hx1 hne
    refine ⟨slOfCube_pow_three_ch615 mx hx, slOfCube_pow_three_ch615 my hy,
      Subtype.ext hc, fun h1 => hx1 ?_, fun hmem => ?_⟩
    · exact congrArg Subtype.val h1
    · rcases eq_of_mem_zpowers_three_ch615 (slOfCube_pow_three_ch615 mx hx) hmem with
        h1 | h1 | h1
      · exact hne.1 (congrArg Subtype.val h1)
      · exact hne.2.1 (congrArg Subtype.val h1)
      · exact hne.2.2 (congrArg Subtype.val h1)
  rcases h with ⟨h1, h3⟩ | ⟨h2, h4⟩
  · obtain ⟨a, b, c, d, e⟩ := key m01_ch615 m23_ch615 m01_cube_ch615 m23_cube_ch615
      m01_m23_comm_ch615 m01_ne_one_ch615 m23_ne_ch615
    exact ⟨_, mem_flagStabilizer_of_low_ch615 h1 m01_low_ch615, _,
      mem_flagStabilizer_of_low_ch615 h3 m23_low_ch615, a, b, c, d, e⟩
  · obtain ⟨a, b, c, d, e⟩ := key m12_ch615 m34_ch615 m12_cube_ch615 m34_cube_ch615
      m12_m34_comm_ch615 m12_ne_one_ch615 m34_ne_ch615
    exact ⟨_, mem_flagStabilizer_of_low_ch615 h2 m12_low_ch615, _,
      mem_flagStabilizer_of_low_ch615 h4 m34_low_ch615, a, b, c, d, e⟩

end E9

end CFSG.Quasithin.H13
