module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallBasic
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallModelsBDAux
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallModelsBDAuxB

public section

namespace CFSG.StandardType.HdRo7D.Small

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU CFSG.StandardType.HdRo7SU.Small

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma hdRo7DSmModBDAux_dB_one_sum {n : ℕ} (u v : DV n) :
    dB 1 u v = ∑ i : Fin (n + 1), u i * v i := by
  rw [dB, one_mul, Fin.sum_univ_succ]

private lemma hdRo7DSmModBDAux_dB_smul_right {n : ℕ} (c : ZMod 3) (h v : DV n) :
    dB 1 h (c • v) = c * dB 1 h v := by
  rw [hdRo7DSmModBDAux_dB_one_sum, hdRo7DSmModBDAux_dB_one_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private lemma hdRo7DSmModBDAux_dB_dE_self {n : ℕ} (i : Fin (n + 1)) :
    dB 1 (dE n i) (dE n i) = 1 := by
  rw [hdRo7DSmModBDAux_dB_one_sum]
  simp [dE, Pi.single_apply]

private lemma hdRo7DSmModBDAux_sum_single_mul {n : ℕ} (i : Fin (n + 1)) (v : DV n) :
    ∑ x : Fin (n + 1), (if x = i then (1 : ZMod 3) else 0) * v x = v i := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [hb]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private lemma hdRo7DSmModBDAux_dB_dE_sub {n : ℕ} (i j : Fin (n + 1)) (v : DV n) :
    dB 1 (dE n i - dE n j) v = v i - v j := by
  rw [hdRo7DSmModBDAux_dB_one_sum]
  have hsplit : (∑ x : Fin (n + 1), (dE n i - dE n j) x * v x) =
      ∑ x : Fin (n + 1),
        ((if x = i then (1 : ZMod 3) else 0) * v x -
          (if x = j then (1 : ZMod 3) else 0) * v x) := by
    apply Finset.sum_congr rfl
    intro x _
    simp [dE, Pi.single_apply, sub_mul]
  rw [hsplit, Finset.sum_sub_distrib, hdRo7DSmModBDAux_sum_single_mul,
    hdRo7DSmModBDAux_sum_single_mul]

private lemma hdRo7DSmModBDAux_dB_dE_add {n : ℕ} (i j : Fin (n + 1)) (v : DV n) :
    dB 1 (dE n i + dE n j) v = v i + v j := by
  rw [hdRo7DSmModBDAux_dB_one_sum]
  have hsplit : (∑ x : Fin (n + 1), (dE n i + dE n j) x * v x) =
      ∑ x : Fin (n + 1),
        ((if x = i then (1 : ZMod 3) else 0) * v x +
          (if x = j then (1 : ZMod 3) else 0) * v x) := by
    apply Finset.sum_congr rfl
    intro x _
    simp [dE, Pi.single_apply, add_mul]
  rw [hsplit, Finset.sum_add_distrib, hdRo7DSmModBDAux_sum_single_mul,
    hdRo7DSmModBDAux_sum_single_mul]

private lemma hdRo7DSmModBDAux_dB_sub_self {n : ℕ} {i j : Fin (n + 1)} (hij : i ≠ j) :
    dB 1 (dE n i - dE n j) (dE n i - dE n j) = 2 := by
  rw [hdRo7DSmModBDAux_dB_dE_sub]
  simp [dE, hij]
  decide

private lemma hdRo7DSmModBDAux_dB_add_self {n : ℕ} {i j : Fin (n + 1)} (hij : i ≠ j) :
    dB 1 (dE n i + dE n j) (dE n i + dE n j) = 2 := by
  rw [hdRo7DSmModBDAux_dB_dE_add]
  simp [dE, hij]
  decide

private lemma hdRo7DSmModBDAux_smDual_eq_dB {n : ℕ} (u v : DV n) :
    smDual u v = dB 1 u v := by
  rw [hdRo7SmBDAux_smDual_apply, smDot, hdRo7DSmModBDAux_dB_one_sum]

private lemma hdRo7DSmModBDAux_dRef_one_of_self_two {n : ℕ} {h : DV n} (hh : dB 1 h h = 2)
    (v : DV n) : dRef 1 h v = v - dB 1 h v • h := by
  rw [dRef, hh]
  have h22 : (2 : ZMod 3) * 2 = 1 := by decide
  rw [h22, one_mul]

private lemma hdRo7DSmModBDAux_eq_pm_one {a : ZMod 3} (ha : a ≠ 0) : a = 1 ∨ a = -1 := by
  have h : ∀ a : ZMod 3, a ≠ 0 → a = 1 ∨ a = -1 := by decide
  exact h a ha

private lemma hdRo7DSmModBDAux_sq_eq_one {c : ZMod 3} (hc : c = 1 ∨ c = -1) : c * c = 1 := by
  rcases hc with rfl | rfl <;> decide

private lemma hdRo7DSmModBDAux_isD_decomp {n : ℕ} {h : DV n} (hd : dIsD h) :
    ∃ (i j : Fin (n + 1)) (a b : ZMod 3), i ≠ j ∧ a ≠ 0 ∧ b ≠ 0 ∧
      h = a • dE n i + b • dE n j := by
  obtain ⟨i, j, hij, hi, hj, hrest⟩ := hd
  refine ⟨i, j, h i, h j, hij, hi, hj, ?_⟩
  funext k
  by_cases hki : k = i
  · subst hki
    simp [dE, hij]
  · by_cases hkj : k = j
    · subst hkj
      simp [dE, hki]
    · rw [hrest k hki hkj]
      simp [dE, hki, hkj]

private lemma hdRo7DSmModBDAux_isD_cases {n : ℕ} {h : DV n} (hd : dIsD h) :
    ∃ (i j : Fin (n + 1)) (c : ZMod 3), i ≠ j ∧ (c = 1 ∨ c = -1) ∧
      (h = c • (dE n i - dE n j) ∨ h = c • (dE n i + dE n j)) := by
  obtain ⟨i, j, a, b, hij, ha, hb, hdec⟩ := hdRo7DSmModBDAux_isD_decomp hd
  rcases hdRo7DSmModBDAux_eq_pm_one ha with rfl | rfl
  · rcases hdRo7DSmModBDAux_eq_pm_one hb with rfl | rfl
    · exact ⟨i, j, 1, hij, Or.inl rfl, Or.inr (by rw [hdec]; module)⟩
    · exact ⟨i, j, 1, hij, Or.inl rfl, Or.inl (by rw [hdec]; module)⟩
  · rcases hdRo7DSmModBDAux_eq_pm_one hb with rfl | rfl
    · exact ⟨i, j, -1, hij, Or.inr rfl, Or.inl (by rw [hdec]; module)⟩
    · exact ⟨i, j, -1, hij, Or.inr rfl, Or.inr (by rw [hdec]; module)⟩

private lemma hdRo7DSmModBDAux_isO_decomp {n : ℕ} {h : DV n} (hd : dIsO h) :
    ∃ (i : Fin (n + 1)) (a : ZMod 3), a ≠ 0 ∧ h = a • dE n i := by
  obtain ⟨i, hi, hrest⟩ := hd
  refine ⟨i, h i, hi, ?_⟩
  funext k
  by_cases hki : k = i
  · subst hki
    simp [dE]
  · rw [hrest k hki]
    simp [dE, hki]

private lemma hdRo7DSmModBDAux_isO_cases {n : ℕ} {h : DV n} (hd : dIsO h) :
    ∃ (i : Fin (n + 1)) (c : ZMod 3), (c = 1 ∨ c = -1) ∧ h = c • dE n i := by
  obtain ⟨i, a, ha, hdec⟩ := hdRo7DSmModBDAux_isO_decomp hd
  rcases hdRo7DSmModBDAux_eq_pm_one ha with rfl | rfl
  · exact ⟨i, 1, Or.inl rfl, hdec⟩
  · exact ⟨i, -1, Or.inr rfl, hdec⟩

private lemma hdRo7DSmModBDAux_dRefl_of_smRefl_smul {n : ℕ} {r : DGL n} {h u w : DV n}
    (hh : dB 1 h h ≠ 0) {a b : ZMod 3} (hu : u = a • h) (hw : w = b • h)
    (hab : a * b = 2 * dB 1 h h) (hr : SMRefl r u (smDual w)) : DRefl 1 r h := by
  refine ⟨hh, fun v => ?_⟩
  have hs : b * dB 1 h v * a = 2 * dB 1 h h * dB 1 h v := by
    calc b * dB 1 h v * a = (a * b) * dB 1 h v := by ring
      _ = 2 * dB 1 h h * dB 1 h v := by rw [hab]
  rw [hr.2 v, hu, hw, hdRo7SmBDAux_smDual_smul, hdRo7DSmModBDAux_smDual_eq_dB,
    smul_smul, hs, dRef]

private noncomputable def hdRo7DSmModBDAux_perm {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) : DGL n where
  toFun v := fun j => v (σ.symm j)
  invFun v := fun j => v (σ j)
  map_add' x y := by funext j; rfl
  map_smul' c x := by funext j; rfl
  left_inv x := by funext j; simp
  right_inv x := by funext j; simp

private lemma hdRo7DSmModBDAux_perm_isPerm {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    SMIsPerm (hdRo7DSmModBDAux_perm σ) :=
  ⟨σ, fun _ _ => rfl⟩

private lemma hdRo7DSmModBDAux_perm_one {n : ℕ} :
    hdRo7DSmModBDAux_perm (1 : Equiv.Perm (Fin (n + 1))) = 1 := by
  apply LinearEquiv.ext
  intro v
  funext j
  rfl

private lemma hdRo7DSmModBDAux_perm_mul {n : ℕ} (σ τ : Equiv.Perm (Fin (n + 1))) :
    hdRo7DSmModBDAux_perm (σ * τ) =
      hdRo7DSmModBDAux_perm σ * hdRo7DSmModBDAux_perm τ := by
  have hsymm : (σ * τ).symm = τ.symm * σ.symm := by
    apply Equiv.ext
    intro x
    rw [Equiv.symm_apply_eq]
    simp [Equiv.Perm.mul_apply]
  apply LinearEquiv.ext
  intro v
  funext j
  change v ((σ * τ).symm j) = v (τ.symm (σ.symm j))
  rw [hsymm]
  rfl

private noncomputable def hdRo7DSmModBDAux_permHom {n : ℕ} :
    Equiv.Perm (Fin (n + 1)) →* DGL n where
  toFun := hdRo7DSmModBDAux_perm
  map_one' := hdRo7DSmModBDAux_perm_one
  map_mul' := hdRo7DSmModBDAux_perm_mul

private lemma hdRo7DSmModBDAux_perm_inv {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    (hdRo7DSmModBDAux_perm σ)⁻¹ = hdRo7DSmModBDAux_perm σ.symm := by
  apply LinearEquiv.ext
  intro v
  funext j
  rfl

private lemma hdRo7DSmModBDAux_perm_dE {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (i : Fin (n + 1)) :
    hdRo7DSmModBDAux_perm σ (dE n i) = dE n (σ i) := by
  funext j
  simp [hdRo7DSmModBDAux_perm, dE, Pi.single_apply, Equiv.symm_apply_eq]

private lemma hdRo7DSmModBDAux_dot_perm {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (x y : DV n) :
    dB 1 (hdRo7DSmModBDAux_perm σ x) (hdRo7DSmModBDAux_perm σ y) = dB 1 x y := by
  rw [hdRo7DSmModBDAux_dB_one_sum, hdRo7DSmModBDAux_dB_one_sum]
  exact Equiv.sum_comp σ.symm (fun i => x i * y i)

private lemma hdRo7DSmModBDAux_conj_perm_dRefl {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    {r : DGL n} {h : DV n} (hr : DRefl 1 r h) :
    DRefl 1 (hdRo7DSmModBDAux_perm σ * r * (hdRo7DSmModBDAux_perm σ)⁻¹)
      (hdRo7DSmModBDAux_perm σ h) := by
  have hd : dB 1 (hdRo7DSmModBDAux_perm σ h) (hdRo7DSmModBDAux_perm σ h) ≠ 0 := by
    rw [hdRo7DSmModBDAux_dot_perm]
    exact hr.1
  refine ⟨hd, fun v => ?_⟩
  have hform : (hdRo7DSmModBDAux_perm σ * r * (hdRo7DSmModBDAux_perm σ)⁻¹) v
      = hdRo7DSmModBDAux_perm σ (r (hdRo7DSmModBDAux_perm σ.symm v)) := by
    rw [hdRo7DSmModBDAux_perm_inv]
    rfl
  have hvv : hdRo7DSmModBDAux_perm σ (hdRo7DSmModBDAux_perm σ.symm v) = v := by
    funext j
    simp [hdRo7DSmModBDAux_perm]
  rw [hform, hr.2 (hdRo7DSmModBDAux_perm σ.symm v), dRef, map_sub, map_smul,
    ← hdRo7DSmModBDAux_dot_perm σ h h,
    ← hdRo7DSmModBDAux_dot_perm σ h (hdRo7DSmModBDAux_perm σ.symm v), hvv]
  rw [dRef]

private lemma hdRo7DSmModBDAux_isD_sub {n : ℕ} {i j : Fin (n + 1)} (hij : i ≠ j) :
    dIsD (dE n i - dE n j) := by
  refine ⟨i, j, hij, ?_, ?_, ?_⟩
  · have h : (dE n i - dE n j) i = 1 := by
      rw [Pi.sub_apply, dE, dE, Pi.single_eq_same, Pi.single_eq_of_ne hij]
      decide
    rw [h]
    decide
  · have h : (dE n i - dE n j) j = -1 := by
      rw [Pi.sub_apply, dE, dE, Pi.single_eq_of_ne (Ne.symm hij), Pi.single_eq_same]
      decide
    rw [h]
    decide
  · intro k hki hkj
    rw [Pi.sub_apply, dE, dE, Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj, sub_zero]

private lemma hdRo7DSmModBDAux_dRefl_swap {n : ℕ} {i j : Fin (n + 1)} (hij : i ≠ j) :
    DRefl 1 (hdRo7DSmModBDAux_perm (Equiv.swap i j)) (dE n i - dE n j) := by
  refine ⟨?_, fun v => ?_⟩
  · rw [hdRo7DSmModBDAux_dB_sub_self hij]
    decide
  · rw [hdRo7DSmModBDAux_dRef_one_of_self_two (hdRo7DSmModBDAux_dB_sub_self hij),
      hdRo7DSmModBDAux_dB_dE_sub]
    funext k
    by_cases hki : k = i
    · subst hki
      simp [hdRo7DSmModBDAux_perm, dE, hij]
    · by_cases hkj : k = j
      · subst hkj
        simp [hdRo7DSmModBDAux_perm, dE, hki]
      · simp [hdRo7DSmModBDAux_perm, dE, hki, hkj,
          Equiv.swap_apply_of_ne_of_ne hki hkj]

private lemma hdRo7DSmModBDAux_perm_mem_dGroup {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    hdRo7DSmModBDAux_perm σ ∈ dGroup 1 (dPhiD n) := by
  have hle : Subgroup.closure {τ : Equiv.Perm (Fin (n + 1)) | τ.IsSwap} ≤
      (dGroup 1 (dPhiD n)).comap hdRo7DSmModBDAux_permHom := by
    rw [Subgroup.closure_le]
    rintro τ hτ
    obtain ⟨i, j, hij, rfl⟩ := hτ
    refine Subgroup.mem_comap.mpr (Subgroup.subset_closure
      ⟨dE n i - dE n j, hdRo7DSmModBDAux_isD_sub hij, hdRo7DSmModBDAux_dRefl_swap hij⟩)
  have htop : σ ∈ Subgroup.closure {τ : Equiv.Perm (Fin (n + 1)) | τ.IsSwap} := by
    rw [Equiv.Perm.closure_isSwap]
    exact Subgroup.mem_top σ
  have hmem := Subgroup.mem_comap.mp (hle htop)
  exact hmem

private lemma hdRo7DSmModBDAux_isPerm_mem_dGroup {n : ℕ} {g : DGL n} (hg : SMIsPerm g) :
    g ∈ dGroup 1 (dPhiD n) := by
  obtain ⟨σ, hσ⟩ := hg
  have hg' : g = hdRo7DSmModBDAux_perm σ := by
    apply LinearEquiv.ext
    intro v
    funext j
    exact hσ v j
  rw [hg']
  exact hdRo7DSmModBDAux_perm_mem_dGroup σ

private lemma hdRo7DSmModBDAux_smRefl_of_dRefl_smul {n : ℕ} {s : DGL n} {h : DV n}
    (hh : dB 1 h h ≠ 0) {a b : ZMod 3} (hab : a * b = 2 * dB 1 h h)
    (hs : DRefl 1 s h) : SMRefl s (a • h) (smDual (b • h)) := by
  constructor
  · calc smDual (b • h) (a • h) = b * (a * dB 1 h h) := by
          rw [hdRo7SmBDAux_smDual_smul, hdRo7DSmModBDAux_smDual_eq_dB,
            hdRo7DSmModBDAux_dB_smul_right]
      _ = (a * b) * dB 1 h h := by ring
      _ = (2 * dB 1 h h) * dB 1 h h := by rw [hab]
      _ = 2 * (dB 1 h h * dB 1 h h) := by ring
      _ = 2 := by
          rw [hdRo7DSmModBDAux_sq_eq_one (hdRo7DSmModBDAux_eq_pm_one hh), mul_one]
  · intro v
    rw [hs.2 v, dRef, hdRo7SmBDAux_smDual_smul, hdRo7DSmModBDAux_smDual_eq_dB, smul_smul]
    have hs' : b * dB 1 h v * a = 2 * dB 1 h h * dB 1 h v := by
      calc b * dB 1 h v * a = (a * b) * dB 1 h v := by ring
        _ = 2 * dB 1 h h * dB 1 h v := by rw [hab]
    rw [hs']

private lemma hdRo7DSmModBDAux_exists_perm_pair {n : ℕ} {p q i j : Fin (n + 1)}
    (hpq : p ≠ q) (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin (n + 1)), σ p = i ∧ σ q = j := by
  have hf : Function.Injective ![p, q] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  have hg : Function.Injective ![i, j] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair ![p, q] ![i, j] hf hg
  exact ⟨σ, by simpa using hσ 0, by simpa using hσ 1⟩

private lemma hdRo7DSmModBDAux_smRefl_mem_dGroup {n : ℕ} {Φ : Set (DV n)}
    {q : DV n × DV n} {h : DV n} {a b : ZMod 3} (hmem : h ∈ Φ)
    (hq1 : q.1 = a • h) (hq2 : q.2 = b • h)
    (hab : a * b = 2 * dB 1 h h) (hne : dB 1 h h ≠ 0)
    {r : DGL n} (hr : SMRefl r q.1 (smDual q.2)) : r ∈ dGroup 1 Φ := by
  have hd : DRefl 1 r h :=
    hdRo7DSmModBDAux_dRefl_of_smRefl_smul hne hq1 hq2 hab hr
  exact Subgroup.subset_closure ⟨h, hmem, hd⟩

private lemma hdRo7DSmModBDAux_smGroup_le_dGroup {n : ℕ} {X : List (DV n × DV n)}
    {Φ : Set (DV n)} (hΦ : dPhiD n ⊆ Φ)
    (hX : ∀ q ∈ X, ∃ (h : DV n) (a b : ZMod 3), h ∈ Φ ∧ q.1 = a • h ∧ q.2 = b • h ∧
      a * b = 2 * dB 1 h h ∧ dB 1 h h ≠ 0) :
    smGroup (n + 1) X ≤ dGroup 1 Φ := by
  rw [smGroup, Subgroup.closure_le]
  rintro r (hperm | ⟨q, hq, hrefl⟩)
  · have hmem : r ∈ dGroup 1 (dPhiD n) := hdRo7DSmModBDAux_isPerm_mem_dGroup hperm
    exact Subgroup.closure_mono (fun x hx => by
      obtain ⟨h, hh, hd⟩ := hx
      exact ⟨h, hΦ hh, hd⟩) hmem
  · obtain ⟨h, a, b, hmem, hq1, hq2, hab, hne⟩ := hX q hq
    exact hdRo7DSmModBDAux_smRefl_mem_dGroup hmem hq1 hq2 hab hne hrefl

private lemma hdRo7DSmModBDAux_dRefl_isD_mem_smGroup {n : ℕ} {p q : Fin (n + 1)}
    (hpq : p ≠ q) {X : List (DV n × DV n)} {data : DV n × DV n} {a b : ZMod 3}
    (hdata1 : data.1 = a • (dE n p + dE n q))
    (hdata2 : data.2 = b • (dE n p + dE n q))
    (hab : a * b = 2 * dB 1 (dE n p + dE n q) (dE n p + dE n q))
    (hDmem : data ∈ X) {r : DGL n} {h : DV n} (hd : dIsD h) (hr : DRefl 1 r h) :
    r ∈ smGroup (n + 1) X := by
  obtain ⟨i, j, c, hij, hc, hcases⟩ := hdRo7DSmModBDAux_isD_cases hd
  rcases hcases with hEq | hEq
  · have hu : DRefl 1 r (dE n i - dE n j) := by
      rw [hEq] at hr
      rcases hc with hc | hc
      · simpa [hc] using hr
      · rw [hc, neg_one_smul] at hr
        exact (dRefl_neg_iff (r := r) (h := dE n i - dE n j)).mp hr
    have ht : DRefl 1 (hdRo7DSmModBDAux_perm (Equiv.swap i j)) (dE n i - dE n j) :=
      hdRo7DSmModBDAux_dRefl_swap hij
    have heq : r = hdRo7DSmModBDAux_perm (Equiv.swap i j) := dRefl_unique hu ht
    rw [heq]
    exact Subgroup.subset_closure (Or.inl (hdRo7DSmModBDAux_perm_isPerm (Equiv.swap i j)))
  · obtain ⟨σ, hσp, hσq⟩ := hdRo7DSmModBDAux_exists_perm_pair hpq hij
    let g : DGL n := hdRo7DSmModBDAux_perm σ
    obtain ⟨s, hs⟩ := exists_dRefl (ρ := 1) (h := dE n p + dE n q)
      (by rw [hdRo7DSmModBDAux_dB_add_self hpq]; decide)
    have hsSM : SMRefl s data.1 (smDual data.2) := by
      rw [hdata1, hdata2]
      exact hdRo7DSmModBDAux_smRefl_of_dRefl_smul
        (by rw [hdRo7DSmModBDAux_dB_add_self hpq]; decide) hab hs
    have hs_mem : s ∈ smGroup (n + 1) X :=
      Subgroup.subset_closure (Or.inr ⟨data, hDmem, hsSM⟩)
    have hg_mem : g ∈ smGroup (n + 1) X :=
      Subgroup.subset_closure (Or.inl (hdRo7DSmModBDAux_perm_isPerm σ))
    have ht_mem : g * s * g⁻¹ ∈ smGroup (n + 1) X :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hg_mem hs_mem) (Subgroup.inv_mem _ hg_mem)
    have himg : g (dE n p + dE n q) = dE n i + dE n j := by
      dsimp [g]
      rw [map_add, hdRo7DSmModBDAux_perm_dE, hdRo7DSmModBDAux_perm_dE, hσp, hσq]
    have ht : DRefl 1 (g * s * g⁻¹) (dE n i + dE n j) := by
      have hconj := hdRo7DSmModBDAux_conj_perm_dRefl σ hs
      simpa [g, himg] using hconj
    have hu : DRefl 1 r (dE n i + dE n j) := by
      rw [hEq] at hr
      rcases hc with hc | hc
      · simpa [hc] using hr
      · rw [hc, neg_one_smul] at hr
        exact (dRefl_neg_iff (r := r) (h := dE n i + dE n j)).mp hr
    have heq : r = g * s * g⁻¹ := dRefl_unique hu ht
    rw [heq]
    exact ht_mem

private lemma hdRo7DSmModBDAux_dRefl_isO_mem_smGroup {n : ℕ} {q : Fin (n + 1)}
    {X : List (DV n × DV n)} {data : DV n × DV n} {a b : ZMod 3}
    (hdata1 : data.1 = a • dE n q) (hdata2 : data.2 = b • dE n q)
    (hab : a * b = 2 * dB 1 (dE n q) (dE n q))
    (hBmem : data ∈ X) {r : DGL n} {h : DV n} (hd : dIsO h) (hr : DRefl 1 r h) :
    r ∈ smGroup (n + 1) X := by
  obtain ⟨i, c, hc, hEq⟩ := hdRo7DSmModBDAux_isO_cases hd
  let g : DGL n := hdRo7DSmModBDAux_perm (Equiv.swap q i)
  obtain ⟨s, hs⟩ := exists_dRefl (ρ := 1) (h := dE n q)
    (by rw [hdRo7DSmModBDAux_dB_dE_self]; decide)
  have hsSM : SMRefl s data.1 (smDual data.2) := by
    rw [hdata1, hdata2]
    exact hdRo7DSmModBDAux_smRefl_of_dRefl_smul
      (by rw [hdRo7DSmModBDAux_dB_dE_self]; decide) hab hs
  have hs_mem : s ∈ smGroup (n + 1) X :=
    Subgroup.subset_closure (Or.inr ⟨data, hBmem, hsSM⟩)
  have hg_mem : g ∈ smGroup (n + 1) X :=
    Subgroup.subset_closure (Or.inl (hdRo7DSmModBDAux_perm_isPerm (Equiv.swap q i)))
  have ht_mem : g * s * g⁻¹ ∈ smGroup (n + 1) X :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hg_mem hs_mem) (Subgroup.inv_mem _ hg_mem)
  have himg : g (dE n q) = dE n i := by
    dsimp [g]
    rw [hdRo7DSmModBDAux_perm_dE, Equiv.swap_apply_left]
  have ht : DRefl 1 (g * s * g⁻¹) (dE n i) := by
    have hconj := hdRo7DSmModBDAux_conj_perm_dRefl (Equiv.swap q i) hs
    simpa [g, himg] using hconj
  have hu : DRefl 1 r (dE n i) := by
    rw [hEq] at hr
    rcases hc with hc | hc
    · simpa [hc] using hr
    · rw [hc, neg_one_smul] at hr
      exact (dRefl_neg_iff (r := r) (h := dE n i)).mp hr
  have heq : r = g * s * g⁻¹ := dRefl_unique hu ht
  rw [heq]
  exact ht_mem

private lemma hdRo7DSmModBDAux_isD_add {n : ℕ} {i j : Fin (n + 1)} (hij : i ≠ j) :
    dIsD (dE n i + dE n j) := by
  refine ⟨i, j, hij, ?_, ?_, ?_⟩
  · have h : (dE n i + dE n j) i = 1 := by
      rw [Pi.add_apply, dE, dE, Pi.single_eq_same, Pi.single_eq_of_ne hij]
      decide
    rw [h]
    decide
  · have h : (dE n i + dE n j) j = 1 := by
      rw [Pi.add_apply, dE, dE, Pi.single_eq_of_ne (Ne.symm hij), Pi.single_eq_same]
      decide
    rw [h]
    decide
  · intro k hki hkj
    rw [Pi.add_apply, dE, dE, Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj, add_zero]

private lemma hdRo7DSmModBDAux_isO_single {n : ℕ} (i : Fin (n + 1)) :
    dIsO (dE n i) := by
  refine ⟨i, ?_, ?_⟩
  · rw [dE, Pi.single_eq_same]
    decide
  · intro k hki
    rw [dE, Pi.single_eq_of_ne hki]

private abbrev hdRo7DSmModBDAux_p7 : Fin 7 := ⟨5, by norm_num⟩
private abbrev hdRo7DSmModBDAux_q7 : Fin 7 := ⟨6, by norm_num⟩
private abbrev hdRo7DSmModBDAux_p8 : Fin 8 := ⟨6, by norm_num⟩
private abbrev hdRo7DSmModBDAux_q8 : Fin 8 := ⟨7, by norm_num⟩

private lemma hdRo7DSmModBDAux_p7_ne_q7 : hdRo7DSmModBDAux_p7 ≠ hdRo7DSmModBDAux_q7 := by
  decide

private lemma hdRo7DSmModBDAux_p8_ne_q8 : hdRo7DSmModBDAux_p8 ≠ hdRo7DSmModBDAux_q8 := by
  decide

private lemma hdRo7DSmModBDAux_dataD7_1 :
    sm7D7b.1 = (2 : ZMod 3) •
      (dE 6 hdRo7DSmModBDAux_p7 + dE 6 hdRo7DSmModBDAux_q7) := by
  decide

private lemma hdRo7DSmModBDAux_dataD7_2 :
    sm7D7b.2 = (2 : ZMod 3) •
      (dE 6 hdRo7DSmModBDAux_p7 + dE 6 hdRo7DSmModBDAux_q7) := by
  decide

private lemma hdRo7DSmModBDAux_dataB7_1 :
    sm7B7b.1 = (2 : ZMod 3) • dE 6 hdRo7DSmModBDAux_q7 := by
  decide

private lemma hdRo7DSmModBDAux_dataB7_2 :
    sm7B7b.2 = (1 : ZMod 3) • dE 6 hdRo7DSmModBDAux_q7 := by
  decide

private lemma hdRo7DSmModBDAux_dataD8_1 :
    sm8D8b.1 = (1 : ZMod 3) •
      (dE 7 hdRo7DSmModBDAux_p8 + dE 7 hdRo7DSmModBDAux_q8) := by
  decide

private lemma hdRo7DSmModBDAux_dataD8_2 :
    sm8D8b.2 = (1 : ZMod 3) •
      (dE 7 hdRo7DSmModBDAux_p8 + dE 7 hdRo7DSmModBDAux_q8) := by
  decide

private lemma hdRo7DSmModBDAux_dataB8_1 :
    sm8B8b.1 = (1 : ZMod 3) • dE 7 hdRo7DSmModBDAux_q8 := by
  decide

private lemma hdRo7DSmModBDAux_dataB8_2 :
    sm8B8b.2 = (2 : ZMod 3) • dE 7 hdRo7DSmModBDAux_q8 := by
  decide

private lemma hdRo7DSmModBDAux_dGroupD_le_smGroup {n : ℕ} {p q : Fin (n + 1)}
    (hpq : p ≠ q) {X : List (DV n × DV n)} {data : DV n × DV n} {a b : ZMod 3}
    (hdata1 : data.1 = a • (dE n p + dE n q))
    (hdata2 : data.2 = b • (dE n p + dE n q))
    (hab : a * b = 2 * dB 1 (dE n p + dE n q) (dE n p + dE n q))
    (hDmem : data ∈ X) :
    dGroup 1 (dPhiD n) ≤ smGroup (n + 1) X := by
  rw [dGroup, Subgroup.closure_le]
  rintro r ⟨h, hmem, hr⟩
  exact hdRo7DSmModBDAux_dRefl_isD_mem_smGroup hpq hdata1 hdata2 hab hDmem hmem hr

private lemma hdRo7DSmModBDAux_dGroupB_le_smGroup {n : ℕ} {p q : Fin (n + 1)}
    (hpq : p ≠ q) {X : List (DV n × DV n)} {dataD dataB : DV n × DV n}
    {aD bD aB bB : ZMod 3}
    (hD1 : dataD.1 = aD • (dE n p + dE n q))
    (hD2 : dataD.2 = bD • (dE n p + dE n q))
    (habD : aD * bD = 2 * dB 1 (dE n p + dE n q) (dE n p + dE n q))
    (hDmem : dataD ∈ X)
    (hB1 : dataB.1 = aB • dE n q) (hB2 : dataB.2 = bB • dE n q)
    (habB : aB * bB = 2 * dB 1 (dE n q) (dE n q))
    (hBmem : dataB ∈ X) :
    dGroup 1 (dPhiB n) ≤ smGroup (n + 1) X := by
  rw [dGroup, Subgroup.closure_le]
  rintro r ⟨h, hmem, hr⟩
  rcases hmem with hd | ho
  · exact hdRo7DSmModBDAux_dRefl_isD_mem_smGroup hpq hD1 hD2 habD hDmem hd hr
  · exact hdRo7DSmModBDAux_dRefl_isO_mem_smGroup hB1 hB2 habB hBmem ho hr

private lemma hdRo7DSmModBDAux_dGroupD6_le :
    dGroup 1 (dPhiD 6) ≤ smGroup 7 [sm7D7b] := by
  apply hdRo7DSmModBDAux_dGroupD_le_smGroup (p := hdRo7DSmModBDAux_p7)
    (q := hdRo7DSmModBDAux_q7) hdRo7DSmModBDAux_p7_ne_q7
    (data := sm7D7b) (a := 2) (b := 2)
    hdRo7DSmModBDAux_dataD7_1 hdRo7DSmModBDAux_dataD7_2 ?_ (by simp)
  rw [hdRo7DSmModBDAux_dB_add_self hdRo7DSmModBDAux_p7_ne_q7]

private lemma hdRo7DSmModBDAux_dGroupB6_le :
    dGroup 1 (dPhiB 6) ≤ smGroup 7 [sm7B7b, sm7D7b] := by
  apply hdRo7DSmModBDAux_dGroupB_le_smGroup (p := hdRo7DSmModBDAux_p7)
    (q := hdRo7DSmModBDAux_q7) hdRo7DSmModBDAux_p7_ne_q7
    (dataD := sm7D7b) (dataB := sm7B7b) (aD := 2) (bD := 2) (aB := 2) (bB := 1)
    hdRo7DSmModBDAux_dataD7_1 hdRo7DSmModBDAux_dataD7_2 ?_ (by simp)
    hdRo7DSmModBDAux_dataB7_1 hdRo7DSmModBDAux_dataB7_2 ?_ (by simp)
  · rw [hdRo7DSmModBDAux_dB_add_self hdRo7DSmModBDAux_p7_ne_q7]
  · rw [hdRo7DSmModBDAux_dB_dE_self]

private lemma hdRo7DSmModBDAux_dGroupD7_le :
    dGroup 1 (dPhiD 7) ≤ smGroup 8 [sm8D8b] := by
  apply hdRo7DSmModBDAux_dGroupD_le_smGroup (p := hdRo7DSmModBDAux_p8)
    (q := hdRo7DSmModBDAux_q8) hdRo7DSmModBDAux_p8_ne_q8
    (data := sm8D8b) (a := 1) (b := 1)
    hdRo7DSmModBDAux_dataD8_1 hdRo7DSmModBDAux_dataD8_2 ?_ (by simp)
  rw [hdRo7DSmModBDAux_dB_add_self hdRo7DSmModBDAux_p8_ne_q8]
  decide

private lemma hdRo7DSmModBDAux_dGroupB7_le :
    dGroup 1 (dPhiB 7) ≤ smGroup 8 [sm8B8b, sm8D8b] := by
  apply hdRo7DSmModBDAux_dGroupB_le_smGroup (p := hdRo7DSmModBDAux_p8)
    (q := hdRo7DSmModBDAux_q8) hdRo7DSmModBDAux_p8_ne_q8
    (dataD := sm8D8b) (dataB := sm8B8b) (aD := 1) (bD := 1) (aB := 1) (bB := 2)
    hdRo7DSmModBDAux_dataD8_1 hdRo7DSmModBDAux_dataD8_2 ?_ (by simp)
    hdRo7DSmModBDAux_dataB8_1 hdRo7DSmModBDAux_dataB8_2 ?_ (by simp)
  · rw [hdRo7DSmModBDAux_dB_add_self hdRo7DSmModBDAux_p8_ne_q8]
    decide
  · rw [hdRo7DSmModBDAux_dB_dE_self]
    decide

private lemma hdRo7DSmModBDAux_sm7D_le_dGroupD6 :
    smGroup 7 [sm7D7b] ≤ dGroup 1 (dPhiD 6) := by
  apply hdRo7DSmModBDAux_smGroup_le_dGroup (Φ := dPhiD 6) (fun _ hh => hh)
  intro q hq
  simp only [List.mem_singleton] at hq
  subst hq
  refine ⟨dE 6 hdRo7DSmModBDAux_p7 + dE 6 hdRo7DSmModBDAux_q7, 2, 2, ?_,
    hdRo7DSmModBDAux_dataD7_1, hdRo7DSmModBDAux_dataD7_2, ?_, ?_⟩
  · exact hdRo7DSmModBDAux_isD_add hdRo7DSmModBDAux_p7_ne_q7
  · rw [hdRo7DSmModBDAux_dB_add_self hdRo7DSmModBDAux_p7_ne_q7]
  · rw [hdRo7DSmModBDAux_dB_add_self hdRo7DSmModBDAux_p7_ne_q7]
    decide

private lemma hdRo7DSmModBDAux_sm7BD_le_dGroupB6 :
    smGroup 7 [sm7B7b, sm7D7b] ≤ dGroup 1 (dPhiB 6) := by
  apply hdRo7DSmModBDAux_smGroup_le_dGroup (Φ := dPhiB 6)
    (fun _ hh => Or.inl hh)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · refine ⟨dE 6 hdRo7DSmModBDAux_q7, 2, 1, Or.inr (hdRo7DSmModBDAux_isO_single _),
      hdRo7DSmModBDAux_dataB7_1, hdRo7DSmModBDAux_dataB7_2, ?_, ?_⟩
    · rw [hdRo7DSmModBDAux_dB_dE_self]
    · rw [hdRo7DSmModBDAux_dB_dE_self]
      decide
  · refine ⟨dE 6 hdRo7DSmModBDAux_p7 + dE 6 hdRo7DSmModBDAux_q7, 2, 2,
      Or.inl (hdRo7DSmModBDAux_isD_add hdRo7DSmModBDAux_p7_ne_q7),
      hdRo7DSmModBDAux_dataD7_1, hdRo7DSmModBDAux_dataD7_2, ?_, ?_⟩
    · rw [hdRo7DSmModBDAux_dB_add_self hdRo7DSmModBDAux_p7_ne_q7]
    · rw [hdRo7DSmModBDAux_dB_add_self hdRo7DSmModBDAux_p7_ne_q7]
      decide

private lemma hdRo7DSmModBDAux_sm8D_le_dGroupD7 :
    smGroup 8 [sm8D8b] ≤ dGroup 1 (dPhiD 7) := by
  apply hdRo7DSmModBDAux_smGroup_le_dGroup (Φ := dPhiD 7) (fun _ hh => hh)
  intro q hq
  simp only [List.mem_singleton] at hq
  subst hq
  refine ⟨dE 7 hdRo7DSmModBDAux_p8 + dE 7 hdRo7DSmModBDAux_q8, 1, 1, ?_,
    hdRo7DSmModBDAux_dataD8_1, hdRo7DSmModBDAux_dataD8_2, ?_, ?_⟩
  · exact hdRo7DSmModBDAux_isD_add hdRo7DSmModBDAux_p8_ne_q8
  · rw [hdRo7DSmModBDAux_dB_add_self hdRo7DSmModBDAux_p8_ne_q8]
    decide
  · rw [hdRo7DSmModBDAux_dB_add_self hdRo7DSmModBDAux_p8_ne_q8]
    decide

private lemma hdRo7DSmModBDAux_sm8BD_le_dGroupB7 :
    smGroup 8 [sm8B8b, sm8D8b] ≤ dGroup 1 (dPhiB 7) := by
  apply hdRo7DSmModBDAux_smGroup_le_dGroup (Φ := dPhiB 7)
    (fun _ hh => Or.inl hh)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · refine ⟨dE 7 hdRo7DSmModBDAux_q8, 1, 2, Or.inr (hdRo7DSmModBDAux_isO_single _),
      hdRo7DSmModBDAux_dataB8_1, hdRo7DSmModBDAux_dataB8_2, ?_, ?_⟩
    · rw [hdRo7DSmModBDAux_dB_dE_self]
      decide
    · rw [hdRo7DSmModBDAux_dB_dE_self]
      decide
  · refine ⟨dE 7 hdRo7DSmModBDAux_p8 + dE 7 hdRo7DSmModBDAux_q8, 1, 1,
      Or.inl (hdRo7DSmModBDAux_isD_add hdRo7DSmModBDAux_p8_ne_q8),
      hdRo7DSmModBDAux_dataD8_1, hdRo7DSmModBDAux_dataD8_2, ?_, ?_⟩
    · rw [hdRo7DSmModBDAux_dB_add_self hdRo7DSmModBDAux_p8_ne_q8]
      decide
    · rw [hdRo7DSmModBDAux_dB_add_self hdRo7DSmModBDAux_p8_ne_q8]
      decide

private lemma hdRo7DSmModBDAux_dGroupD6_eq :
    dGroup 1 (dPhiD 6) = smGroup 7 [sm7D7b] :=
  le_antisymm hdRo7DSmModBDAux_dGroupD6_le hdRo7DSmModBDAux_sm7D_le_dGroupD6

private lemma hdRo7DSmModBDAux_dGroupB6_eq :
    dGroup 1 (dPhiB 6) = smGroup 7 [sm7B7b, sm7D7b] :=
  le_antisymm hdRo7DSmModBDAux_dGroupB6_le hdRo7DSmModBDAux_sm7BD_le_dGroupB6

private lemma hdRo7DSmModBDAux_dGroupD7_eq :
    dGroup 1 (dPhiD 7) = smGroup 8 [sm8D8b] :=
  le_antisymm hdRo7DSmModBDAux_dGroupD7_le hdRo7DSmModBDAux_sm8D_le_dGroupD7

private lemma hdRo7DSmModBDAux_dGroupB7_eq :
    dGroup 1 (dPhiB 7) = smGroup 8 [sm8B8b, sm8D8b] :=
  le_antisymm hdRo7DSmModBDAux_dGroupB7_le hdRo7DSmModBDAux_sm8BD_le_dGroupB7

theorem dSmModelsBD_holds : DSmModelsBDLeaf := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hdRo7DSmModBDAux_dGroupD6_eq]
    exact hdRo7SmBDAux_weyl_D7
  · rw [hdRo7DSmModBDAux_dGroupB6_eq]
    exact hdRo7SmBDAux_weyl_B7
  · rw [hdRo7DSmModBDAux_dGroupD7_eq]
    exact hdRo7SmBDAux_weyl_D8
  · rw [hdRo7DSmModBDAux_dGroupB7_eq]
    exact hdRo7SmBDAux_weyl_B8

end CFSG.StandardType.HdRo7D.Small
