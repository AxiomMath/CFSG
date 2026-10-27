module

public import CFSG.Milestones.ASVolI.F48.L3
public import CFSG.Milestones.ASVolI.F4Native

public section

namespace CFSG.ASVolI

open CFSG.Open

section UnCore

variable {p f : ℕ} {K : Type} [Field K] {ε : ℕ}

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.SpecialLinear Matrix in
theorem burnsideF48_swapSet_mem (r : ℕ) (M : Finset (Fin r)) : swapSet M ∈ hypWeyl r := by
  rw [mem_hypWeyl]
  intro x
  rcases x with j | j <;> by_cases hj : j ∈ M <;> simp [swapSet, hj]

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.SpecialLinear Matrix in
theorem burnsideF48_un_n_apply (h : UnitaryFieldData p f K) (c : K) (a b : HypIndex 2 ε) :
    weylMat h c (swapSet ({1} : Finset (Fin 2))) a b =
      if a = weylPerm (swapSet ({1} : Finset (Fin 2))) b then
        weylCoeff h c (swapSet ({1} : Finset (Fin 2))) b else 0 :=
  signedPerm_apply _ _ _ _

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.SpecialLinear Matrix in
theorem burnsideF48_mul_signedPerm_apply {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (π : Equiv.Perm ι) (κ : ι → K) (a b : ι) :
    (M * signedPerm π κ) a b = M a (π b) * κ b := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (π b)]
  · simp [signedPerm_apply]
  · intro k _ hk
    simp [signedPerm_apply, hk]
  · simp

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.SpecialLinear Matrix in
theorem burnsideF48_signedPerm_mul_apply {ι : Type} [Fintype ι] [DecidableEq ι]
    (R : Matrix ι ι K) (π : Equiv.Perm ι) (κ : ι → K) (a b : ι) :
    (signedPerm π κ * R) a b = κ (π.symm a) * R (π.symm a) b := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (π.symm a)]
  · simp [signedPerm_apply]
  · intro k _ hk
    have : a ≠ π k := fun e => hk (by rw [e, Equiv.symm_apply_apply])
    simp [signedPerm_apply, this]
  · simp

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.SpecialLinear Matrix in
theorem burnsideF48_un_perm_e1 :
    weylPerm (ε := ε) (swapSet ({1} : Finset (Fin 2))) (.inl 1) = .inr (.inr 1) := by
  simp [swapSet, lineCoord]

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.SpecialLinear Matrix in
theorem burnsideF48_un_perm_f1 :
    weylPerm (ε := ε) (swapSet ({1} : Finset (Fin 2))) (.inr (.inr 1)) = .inl 1 := by
  simp [swapSet, lineCoord]

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.SpecialLinear Matrix in
theorem burnsideF48_un_perm_z (k : Fin ε) :
    weylPerm (ε := ε) (swapSet ({1} : Finset (Fin 2))) (.inr (.inl k)) = .inr (.inl k) := rfl

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.SpecialLinear Matrix in
theorem burnsideF48_un_perm_e0 :
    weylPerm (ε := ε) (swapSet ({1} : Finset (Fin 2))) (.inl 0) = .inl 0 := by
  simp [swapSet, lineCoord]

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.SpecialLinear Matrix in
theorem burnsideF48_un_perm_f0 :
    weylPerm (ε := ε) (swapSet ({1} : Finset (Fin 2))) (.inr (.inr 0)) = .inr (.inr 0) := by
  simp [swapSet, lineCoord]

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.SpecialLinear Matrix in
theorem burnsideF48_un_coeff_e1 (h : UnitaryFieldData p f K) (c : K) :
    weylCoeff (ε := ε) h c (swapSet ({1} : Finset (Fin 2))) (.inl 1) = c := by
  simp [weylCoeff, swapSet]

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.SpecialLinear Matrix in
theorem burnsideF48_un_coeff_z (h : UnitaryFieldData p f K) (c : K) (k : Fin ε) :
    weylCoeff (ε := ε) h c (swapSet ({1} : Finset (Fin 2))) (.inr (.inl k)) = 1 := rfl

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.SpecialLinear Matrix in
theorem burnsideF48_un_coeff_f1 (h : UnitaryFieldData p f K) (c : K) :
    weylCoeff (ε := ε) h c (swapSet ({1} : Finset (Fin 2))) (.inr (.inr 1)) = (h.bar c)⁻¹ := by
  simp [weylCoeff, swapSet]

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.SpecialLinear Matrix in
theorem burnsideF48_un_normalize (h : UnitaryFieldData p f K) {c : K} (hc0 : c ≠ 0)
    {M R' : Matrix (HypIndex 2 ε) (HypIndex 2 ε) K} (hR' : R'.BlockTriangular fullPos)
    (hMR : M * weylMat h c (swapSet ({1} : Finset (Fin 2))) =
      weylMat h c (swapSet ({1} : Finset (Fin 2))) * R') :
    M (.inl 1) (.inr (.inr 1)) = 0 ∧ (∀ k, M (.inl 1) (.inr (.inl k)) = 0) ∧
      ∀ k, M (.inr (.inl k)) (.inr (.inr 1)) = 0 := by
  have hsymm : ∀ a, (weylPerm (ε := ε) (swapSet ({1} : Finset (Fin 2)))).symm a =
      weylPerm (swapSet ({1} : Finset (Fin 2))) a := by
    intro a
    rw [Equiv.symm_apply_eq]
    rcases a with i | k | i
    · fin_cases i <;> simp [swapSet, lineCoord]
    · rfl
    · fin_cases i <;> simp [swapSet, lineCoord]
  refine ⟨?_, fun k => ?_, fun k => ?_⟩
  · have e := congrFun (congrFun hMR (.inl 1)) (.inl 1)
    rw [weylMat, burnsideF48_mul_signedPerm_apply, burnsideF48_signedPerm_mul_apply, hsymm,
      burnsideF48_un_perm_e1, burnsideF48_un_coeff_e1] at e
    have h0 : R' (.inr (.inr 1)) (.inl 1) = 0 := hR' (by simp <;> omega)
    rw [h0, mul_zero] at e
    exact (mul_eq_zero.1 e).resolve_right hc0
  · have e := congrFun (congrFun hMR (.inl 1)) (.inr (.inl k))
    rw [weylMat, burnsideF48_mul_signedPerm_apply, burnsideF48_signedPerm_mul_apply, hsymm,
      burnsideF48_un_perm_e1, burnsideF48_un_perm_z, burnsideF48_un_coeff_z] at e
    have h0 : R' (.inr (.inr 1)) (.inr (.inl k)) = 0 := hR' (by simp <;> omega)
    rw [h0, mul_zero, mul_one] at e
    exact e
  · have e := congrFun (congrFun hMR (.inr (.inl k))) (.inl 1)
    rw [weylMat, burnsideF48_mul_signedPerm_apply, burnsideF48_signedPerm_mul_apply, hsymm,
      burnsideF48_un_perm_e1, burnsideF48_un_perm_z, burnsideF48_un_coeff_e1] at e
    have h0 : R' (.inr (.inl k)) (.inl 1) = 0 := hR' (by simp <;> omega)
    rw [h0, mul_zero] at e
    exact (mul_eq_zero.1 e).resolve_right hc0

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.SpecialLinear Matrix in
theorem burnsideF48_un_eq_one (hε : ε ≤ 1) {D : HypIndex 2 ε → K} (hD0 : D (.inl 0) ≠ 0)
    (h01 : D (.inl 0) ≠ D (.inl 1)) (h0z : ∀ k : Fin ε, D (.inl 0) ≠ D (.inr (.inl k)))
    (h0f0 : D (.inl 0) ≠ D (.inr (.inr 0))) (h0f1 : D (.inl 0) ≠ D (.inr (.inr 1)))
    (h1f0 : D (.inl 1) ≠ D (.inr (.inr 0)))
    (hzf0 : ∀ k : Fin ε, D (.inr (.inl k)) ≠ D (.inr (.inr 0)))
    (hf1f0 : D (.inr (.inr 1)) ≠ D (.inr (.inr 0)))
    {M : Matrix (HypIndex 2 ε) (HypIndex 2 ε) K} (hM : M.BlockTriangular fullPos)
    (hdiag : ∀ a, M a a = 1) (h1f : M (.inl 1) (.inr (.inr 1)) = 0)
    (h1z : ∀ k, M (.inl 1) (.inr (.inl k)) = 0) (hzf : ∀ k, M (.inr (.inl k)) (.inr (.inr 1)) = 0)
    {c : K}
    (hcomm : M * diagonal D = diagonal D * M * Matrix.scalar (HypIndex 2 ε) c) : M = 1 := by
  have hentry : ∀ a b, M a b * D b = D a * M a b * c := by
    intro a b
    have := congrFun (congrFun hcomm a) b
    simpa [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply] using this
  have hcc : c = 1 := by
    have := hentry (.inl 0) (.inl 0)
    rw [hdiag] at this
    have h' : D (.inl 0) * (1 - c) = 0 := by linear_combination this
    exact (sub_eq_zero.1 ((mul_eq_zero.1 h').resolve_left hD0)).symm
  subst hcc
  have hne : ∀ a b, D a ≠ D b → M a b = 0 := by
    intro a b hab
    have := hentry a b
    rw [mul_one] at this
    have h' : M a b * (D b - D a) = 0 := by linear_combination this
    exact (mul_eq_zero.1 h').resolve_right (sub_ne_zero.2 (Ne.symm hab))
  have n01 : M (.inl 0) (.inl 1) = 0 := hne _ _ h01
  have n0z : ∀ l : Fin ε, M (.inl 0) (.inr (.inl l)) = 0 := fun l => hne _ _ (h0z l)
  have n0f0 : M (.inl 0) (.inr (.inr 0)) = 0 := hne _ _ h0f0
  have n0f1 : M (.inl 0) (.inr (.inr 1)) = 0 := hne _ _ h0f1
  have n1f0 : M (.inl 1) (.inr (.inr 0)) = 0 := hne _ _ h1f0
  have nzf0 : ∀ k : Fin ε, M (.inr (.inl k)) (.inr (.inr 0)) = 0 := fun k => hne _ _ (hzf0 k)
  have nf1f0 : M (.inr (.inr 1)) (.inr (.inr 0)) = 0 := hne _ _ hf1f0
  ext a b
  by_cases hab : a = b
  · subst hab
    rw [hdiag, one_apply_eq]
  rw [one_apply_ne hab]
  by_cases htri : fullPos b < fullPos a
  · exact hM htri
  have hlt : fullPos a < fullPos b :=
    lt_of_le_of_ne (not_lt.1 htri) fun e => hab (fullPos_injective e)
  rcases a with i | k | i <;> rcases b with j | l | j
  · fin_cases i <;> fin_cases j
    · exact absurd rfl hab
    · exact n01
    · simp [fullPos] at hlt
    · exact absurd rfl hab
  · fin_cases i
    · exact n0z l
    · exact h1z l
  · fin_cases i <;> fin_cases j
    · exact n0f0
    · exact n0f1
    · exact n1f0
    · exact h1f
  · simp [fullPos] at hlt
    omega
  · have hk : (k : ℕ) = 0 := by have := k.isLt; omega
    have hl : (l : ℕ) = 0 := by have := l.isLt; omega
    exact absurd (congrArg (fun x => (.inr (.inl x) : HypIndex 2 ε)) (Fin.ext (hk.trans hl.symm)))
      hab
  · fin_cases j
    · exact nzf0 k
    · exact hzf k
  · simp [fullPos] at hlt
    omega
  · simp [fullPos] at hlt
    omega
  · fin_cases i <;> fin_cases j
    · exact absurd rfl hab
    · simp [fullPos] at hlt
    · exact nf1f0
    · exact absurd rfl hab

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.SpecialLinear Matrix in
theorem burnsideF48_un_exists_gen (h : UnitaryFieldData p f K) (hq : 3 ≤ p ^ f) :
    ∃ g : Kˣ, (g : K) ≠ 1 ∧ (g : K) ≠ h.bar (g : K) ∧ (g : K) ^ 2 ≠ 1 ∧
      h.norm (g : K) ≠ 1 := by
  classical
  haveI := h.finite
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = (p ^ f) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, h.card, ← pow_mul, mul_comm]
  have hne : ∀ n : ℕ, 0 < n → n < (p ^ f) ^ 2 - 1 → g ^ n ≠ 1 := by
    intro n hn hlt h1
    have := orderOf_le_of_pow_eq_one hn h1
    omega
  set q := p ^ f with hqdef
  have hq9 : 9 ≤ q ^ 2 := by nlinarith
  have hq3 : 3 * q ≤ q ^ 2 := by nlinarith
  have hunit : ∀ n : ℕ, (g : K) ^ n = 1 → g ^ n = 1 := fun n hn =>
    Units.ext (by simpa using hn)
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · intro h1
    have := hne 1 (by norm_num) (by omega)
    exact this (by simpa using Units.ext (by simpa using h1 : (g : K) = ((1 : Kˣ) : K)))
  · intro e
    rw [h.bar_apply] at e
    have hg0 : (g : K) ≠ 0 := g.ne_zero
    have e1 : (g : K) ^ (q - 1) = 1 := by
      have hq1 : q = (q - 1) + 1 := by omega
      have e2 : (g : K) ^ (q - 1) * (g : K) = 1 * (g : K) := by
        rw [one_mul, ← pow_succ, ← hq1]
        exact e.symm
      exact mul_right_cancel₀ hg0 e2
    exact hne (q - 1) (by omega) (by omega) (hunit _ e1)
  · intro e
    exact hne 2 (by norm_num) (by omega) (hunit _ e)
  · intro e
    simp only [UnitaryFieldData.norm, h.bar_apply] at e
    have e1 : (g : K) ^ (q + 1) = 1 := by
      rw [pow_succ, mul_comm]
      exact e
    exact hne (q + 1) (by omega) (by omega) (hunit _ e1)

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.SpecialLinear Matrix in
theorem burnsideF48_un_proj_eq_mat {h : UnitaryFieldData p f K} {r : ℕ} {x y : hypSU h r ε}
    (hxy : hypProj h r ε x = hypProj h r ε y) :
    ∃ c : K, ((y : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      ((x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
        (c • (1 : Matrix (HypIndex r ε) (HypIndex r ε) K)) := by
  have hmem : x⁻¹ * y ∈ hypScalars h r ε := QuotientGroup.eq.1 hxy
  obtain ⟨c, -, -, hc⟩ := mem_normOneScalars.1 hmem
  refine ⟨(c : K), ?_⟩
  have hy : (y : GL (HypIndex r ε) K) =
      (x : GL (HypIndex r ε) K) * ((x⁻¹ * y : hypSU h r ε) : GL (HypIndex r ε) K) := by simp
  rw [hc] at hy
  have h2 := congrArg (fun g : GL (HypIndex r ε) K => (g : Matrix (HypIndex r ε) (HypIndex r ε) K)) hy
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at h2
  rw [h2, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.SpecialLinear Matrix in
theorem burnsideF48_un_posFlag_one {v : HypIndex 2 ε → K} (hv : v ∈ posFlag 2 ε K 1) :
    v = v (.inl 0) • (Pi.single (.inl 0) 1 : HypIndex 2 ε → K) := by
  funext a
  by_cases ha : a = .inl 0
  · subst ha
    simp
  · have : 1 ≤ fullPos a := by
      by_contra hlt
      apply ha
      apply fullPos_injective
      simp [fullPos] at hlt ⊢
      omega
    rw [hv a this]
    simp [Pi.single_apply, ha]

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.SpecialLinear Matrix in
theorem burnsideF48_un_posFlag_two_f {v : HypIndex 2 ε → K} (hv : v ∈ posFlag 2 ε K 2) (j : Fin 2) :
    v (.inr (.inr j)) = 0 :=
  hv _ (by simp [fullPos]; omega)

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.SpecialLinear Matrix in
theorem burnsideF48_un_f0_row {h : UnitaryFieldData p f K} {g : hypSU h 2 ε} {c : K}
    (hg : ((g : GL (HypIndex 2 ε) K) : Matrix (HypIndex 2 ε) (HypIndex 2 ε) K) *ᵥ
      (Pi.single (.inl 0) 1 : HypIndex 2 ε → K) = c • (Pi.single (.inl 0) 1 : HypIndex 2 ε → K))
    (b : HypIndex 2 ε) (hb : b ≠ .inr (.inr 0)) :
    ((g : GL (HypIndex 2 ε) K) : Matrix (HypIndex 2 ε) (HypIndex 2 ε) K) (.inr (.inr 0)) b = 0 := by
  set G := ((g : GL (HypIndex 2 ε) K) : Matrix (HypIndex 2 ε) (HypIndex 2 ε) K) with hG
  have hgram := (mem_hypSU.1 g.2).1
  have e := congrFun (congrFun hgram (.inl 0)) b
  rw [conjTranspose_hypGram_mul_apply h G, hypGram_apply] at e
  have hcol : ∀ x : HypIndex 2 ε, G x (.inl 0) = if x = .inl 0 then c else 0 := by
    intro x
    have := congrFun hg x
    rw [mulVec_single_one, col_apply] at this
    rw [this]
    simp [Pi.single_apply]
  rw [Finset.sum_eq_single (.inl 0)] at e
  · rw [hcol, if_pos rfl] at e
    simp only [hypPartner_inl] at e
    have e' : h.bar c * G (.inr (.inr 0)) b = 0 := e.trans (if_neg hb)
    have hc0 : h.bar c ≠ 0 := by
      intro h0
      have := congrFun (congrFun hgram (.inl 0)) (.inr (.inr 0))
      rw [conjTranspose_hypGram_mul_apply h G, hypGram_apply, Finset.sum_eq_single (.inl 0)] at this
      · rw [hcol, if_pos rfl, h0, zero_mul] at this
        simp at this
      · intro x _ hx
        rw [hcol, if_neg hx, map_zero, zero_mul]
      · simp
    exact (mul_eq_zero.1 e').resolve_left hc0
  · intro x _ hx
    rw [hcol, if_neg hx, map_zero, zero_mul]
  · simp

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.SpecialLinear Matrix in
theorem burnsideF48_signedPerm_mulVec_apply {ι : Type} [Fintype ι] [DecidableEq ι]
    (π : Equiv.Perm ι) (κ : ι → K) (v : ι → K) (a : ι) :
    (signedPerm π κ *ᵥ v) a = κ (π.symm a) * v (π.symm a) := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (π.symm a)]
  · simp [signedPerm_apply]
  · intro k _ hk
    have : a ≠ π k := fun e => hk (by rw [e, Equiv.symm_apply_apply])
    simp [signedPerm_apply, this]
  · simp

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.SpecialLinear Matrix in
theorem burnsideF48_un_coeff_ne_zero (h : UnitaryFieldData p f K) {c : K} (hc0 : c ≠ 0)
    (w : Equiv.Perm (Fin 2 ⊕ Fin 2)) (a : HypIndex 2 ε) : weylCoeff h c w a ≠ 0 := by
  have hbc : (h.bar c)⁻¹ ≠ 0 := inv_ne_zero ((map_ne_zero h.bar).2 hc0)
  rcases a with i | k | i
  · rcases hwi : w (.inl i) with j | j <;> simp [weylCoeff, hwi, hc0]
  · simp [weylCoeff]
  · rcases hwi : w (.inl i) with j | j <;> simp [weylCoeff, hwi, hbc]

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.SpecialLinear Matrix in
theorem burnsideF48_un_perm_symm (a : HypIndex 2 ε) :
    (weylPerm (ε := ε) (swapSet ({1} : Finset (Fin 2)))).symm a =
      weylPerm (swapSet ({1} : Finset (Fin 2))) a := by
  rw [Equiv.symm_apply_eq]
  rcases a with i | k | i
  · fin_cases i <;> simp [swapSet, lineCoord]
  · rfl
  · fin_cases i <;> simp [swapSet, lineCoord]

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.SpecialLinear Matrix in
theorem burnsideF48_un_mem_posFlag_one_iff {v : HypIndex 2 ε → K} :
    v ∈ posFlag 2 ε K 1 ↔ ∀ a, a ≠ .inl 0 → v a = 0 := by
  rw [mem_posFlag]
  constructor
  · intro hv a ha
    apply hv
    by_contra hlt
    apply ha
    apply fullPos_injective
    simp [fullPos] at hlt ⊢
    omega
  · intro hv a ha
    apply hv
    rintro rfl
    simp [fullPos] at ha

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.SpecialLinear Matrix in
theorem burnsideF48_un_n_stab_one (h : UnitaryFieldData p f K) {c : K} (hc0 : c ≠ 0)
    (v : HypIndex 2 ε → K) :
    weylMat h c (swapSet ({1} : Finset (Fin 2))) *ᵥ v ∈ posFlag 2 ε K 1 ↔ v ∈ posFlag 2 ε K 1 := by
  rw [burnsideF48_un_mem_posFlag_one_iff, burnsideF48_un_mem_posFlag_one_iff]
  simp only [weylMat, burnsideF48_signedPerm_mulVec_apply, burnsideF48_un_perm_symm]
  constructor
  · intro hv b hb
    have := hv (weylPerm (swapSet ({1} : Finset (Fin 2))) b) (by
      intro e
      apply hb
      have := congrArg (weylPerm (ε := ε) (swapSet ({1} : Finset (Fin 2)))) e
      rwa [show weylPerm (ε := ε) (swapSet ({1} : Finset (Fin 2))) (weylPerm (swapSet ({1} : Finset (Fin 2))) b) = b from by
        rw [← burnsideF48_un_perm_symm, Equiv.symm_apply_apply], burnsideF48_un_perm_e0] at this)
    rw [← burnsideF48_un_perm_symm, Equiv.symm_apply_apply] at this
    exact (mul_eq_zero.1 this).resolve_left (burnsideF48_un_coeff_ne_zero h hc0 _ b)
  · intro hv a ha
    rw [hv _ (by
      intro e
      apply ha
      have := congrArg (weylPerm (ε := ε) (swapSet ({1} : Finset (Fin 2)))) e
      rwa [show weylPerm (ε := ε) (swapSet ({1} : Finset (Fin 2))) (weylPerm (swapSet ({1} : Finset (Fin 2))) a) = a from by
        rw [← burnsideF48_un_perm_symm, Equiv.symm_apply_apply], burnsideF48_un_perm_e0] at this),
      mul_zero]

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.SpecialLinear Matrix in
@[expose] noncomputable def burnsideF48_unN (h : UnitaryFieldData p f K) {c : K} (hc : c ∈ h.traceZero)
    (hc0 : c ≠ 0) : hypSU h 2 ε :=
  weylElt h hc hc0 (burnsideF48_swapSet_mem 2 ({1} : Finset (Fin 2)))

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.SpecialLinear Matrix in
@[expose] noncomputable def burnsideF48_unW (h : UnitaryFieldData p f K) {c : K} (hc : c ∈ h.traceZero)
    (hc0 : c ≠ 0) : hypSU h 2 ε :=
  weylElt h hc hc0 (burnsideF48_swapSet_mem 2 (Finset.univ : Finset (Fin 2)))

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.SpecialLinear Matrix in
theorem burnsideF48_unN_coe (h : UnitaryFieldData p f K) {c : K} (hc : c ∈ h.traceZero)
    (hc0 : c ≠ 0) :
    (((burnsideF48_unN (ε := ε) h hc hc0 : hypSU h 2 ε) : GL (HypIndex 2 ε) K) :
      Matrix (HypIndex 2 ε) (HypIndex 2 ε) K) =
      weylMat h c (swapSet ({1} : Finset (Fin 2))) := rfl

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.SpecialLinear Matrix in
theorem burnsideF48_unW_coe (h : UnitaryFieldData p f K) {c : K} (hc : c ∈ h.traceZero)
    (hc0 : c ≠ 0) :
    (((burnsideF48_unW (ε := ε) h hc hc0 : hypSU h 2 ε) : GL (HypIndex 2 ε) K) :
      Matrix (HypIndex 2 ε) (HypIndex 2 ε) K) =
      weylMat h c (swapSet (Finset.univ : Finset (Fin 2))) := rfl

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.SpecialLinear Matrix in
open scoped Pointwise in
theorem burnsideF48_unN_mem_stab_one (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {c : K}
    (hc : c ∈ h.traceZero) (hc0 : c ≠ 0) :
    burnsideF48_unN (ε := ε) h hc hc0 ∈
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.isoStabilizer h 2 ε (hypFlag h 2 ε 1) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_isoStabilizer,
    hypFlag_eq_posFlag h hε (by omega), Subgroup.smul_def, burnsideF4h_clu_smul_eq_iff]
  exact fun v => burnsideF48_un_n_stab_one h hc0 v

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.SpecialLinear Matrix in
open scoped Pointwise in
theorem burnsideF48_unN_not_mem_stab_two (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {c : K}
    (hc : c ∈ h.traceZero) (hc0 : c ≠ 0) :
    burnsideF48_unN (ε := ε) h hc hc0 ∉
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.isoStabilizer h 2 ε (hypFlag h 2 ε 2) := by
  intro hmem
  rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_isoStabilizer,
    hypFlag_eq_posFlag h hε (by omega), Subgroup.smul_def, burnsideF4h_clu_smul_eq_iff] at hmem
  have he1 : (Pi.single (.inl 1) 1 : HypIndex 2 ε → K) ∈ posFlag 2 ε K 2 := by
    rw [mem_posFlag]
    intro a ha
    have : a ≠ .inl 1 := by
      rintro rfl
      simp [fullPos] at ha
    simp [Pi.single_apply, this]
  have h1 := (hmem _).2 he1
  rw [burnsideF48_unN_coe] at h1
  have hn := (weylMat_mulVec_of_inr (ε := ε) h c (burnsideF48_swapSet_mem 2
    ({1} : Finset (Fin 2))) (i := 1) (j := 1) (by simp [swapSet])).1
  rw [hn, mem_posFlag] at h1
  have h2 := h1 (.inr (.inr 1)) (by simp [fullPos] <;> omega)
  simp at h2
  exact hc0 h2

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.SpecialLinear Matrix in
@[expose] noncomputable def burnsideF48_unD (h : UnitaryFieldData p f K) (g : Kˣ) :
    HypIndex 2 ε → K :=
  torusEntries h ![g, Units.mk0 (h.bar (g : K)) ((map_ne_zero h.bar).2 g.ne_zero)]
    (fun _ : Fin ε => (1 : Kˣ))

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.SpecialLinear Matrix in
theorem burnsideF48_un_torus (h : UnitaryFieldData p f K) (g : Kˣ) :
    ∃ H : hypSU h 2 ε, H ∈ hypTorus h 2 ε ∧
      ((H : GL (HypIndex 2 ε) K) : Matrix (HypIndex 2 ε) (HypIndex 2 ε) K) =
        diagonal (burnsideF48_unD (ε := ε) h g) := by
  have hd : ∀ k : Fin ε, h.norm (((fun _ : Fin ε => (1 : Kˣ)) k : Kˣ) : K) = 1 := by
    intro k
    simp [UnitaryFieldData.norm]
  have hg0 : (g : K) ≠ 0 := g.ne_zero
  have hb0 : h.bar (g : K) ≠ 0 := (map_ne_zero h.bar).2 hg0
  have hp : torusRatio h
      ![g, Units.mk0 (h.bar (g : K)) ((map_ne_zero h.bar).2 g.ne_zero)]
      (fun _ : Fin ε => (1 : Kˣ)) = 1 := by
    simp only [torusRatio, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Units.val_mk0, h.bar_bar, Units.val_one, Finset.prod_const_one, mul_one]
    field_simp
  exact torusMat_mem_hypSU h _ hd hp

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.SpecialLinear Matrix in
theorem burnsideF48_un_conj_diag_mem_borel (h : UnitaryFieldData p f K) {c : K}
    (hc : c ∈ h.traceZero) (hc0 : c ≠ 0) (M : Finset (Fin 2)) (D : HypIndex 2 ε → K)
    (H : hypSU h 2 ε)
    (hH : ((H : GL (HypIndex 2 ε) K) : Matrix (HypIndex 2 ε) (HypIndex 2 ε) K) = diagonal D) :
    (weylElt h hc hc0 (burnsideF48_swapSet_mem 2 M))⁻¹ * H *
      weylElt h hc hc0 (burnsideF48_swapSet_mem 2 M) ∈ hypBorel h 2 ε := by
  set W := weylElt h hc hc0 (burnsideF48_swapSet_mem 2 M) with hW
  set π := weylPerm (ε := ε) (swapSet M) with hπ
  have hWc : ((W : GL (HypIndex 2 ε) K) : Matrix (HypIndex 2 ε) (HypIndex 2 ε) K) =
      weylMat h c (swapSet M) := rfl
  have hkey : ((W : GL (HypIndex 2 ε) K) : Matrix (HypIndex 2 ε) (HypIndex 2 ε) K) *
      diagonal (fun a => D (π a)) =
      ((H : GL (HypIndex 2 ε) K) : Matrix (HypIndex 2 ε) (HypIndex 2 ε) K) *
        ((W : GL (HypIndex 2 ε) K) : Matrix (HypIndex 2 ε) (HypIndex 2 ε) K) := by
    rw [hH, hWc, weylMat, signedPerm_mul_diagonal]
    congr 2
    funext r
    simp [hπ]
  have hx : (((W⁻¹ * H * W : hypSU h 2 ε) : GL (HypIndex 2 ε) K) :
      Matrix (HypIndex 2 ε) (HypIndex 2 ε) K) = diagonal (fun a => D (π a)) := by
    have h1 : diagonal (fun a => D (π a)) =
        (((W : GL (HypIndex 2 ε) K)⁻¹ : GL (HypIndex 2 ε) K) :
          Matrix (HypIndex 2 ε) (HypIndex 2 ε) K) *
        (((W : GL (HypIndex 2 ε) K) : Matrix (HypIndex 2 ε) (HypIndex 2 ε) K) *
          diagonal (fun a => D (π a))) := by
      rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    rw [hkey] at h1
    simp only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_inv]
    rw [h1, Matrix.mul_assoc]
  exact mem_hypBorel_of_blockTriangular h (by rw [hx]; exact blockTriangular_diagonal _)

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.SpecialLinear Matrix in
theorem burnsideF48_un_stab_iff (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {g : hypSU h 2 ε}
    {i : ℕ} (hi : i ≤ 2) :
    g ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.isoStabilizer h 2 ε (hypFlag h 2 ε i) ↔
      ∀ v, ((g : GL (HypIndex 2 ε) K) : Matrix (HypIndex 2 ε) (HypIndex 2 ε) K) *ᵥ v ∈
        posFlag 2 ε K i ↔ v ∈ posFlag 2 ε K i := by
  open scoped Pointwise in
  rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_isoStabilizer,
    hypFlag_eq_posFlag h hε (by omega), Subgroup.smul_def, burnsideF4h_clu_smul_eq_iff]

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.SpecialLinear Matrix in
theorem burnsideF48_unW_ne_mul (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {c : K}
    (hc : c ∈ h.traceZero) (hc0 : c ≠ 0) {k l k' : hypSU h 2 ε}
    (hk : k ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.isoStabilizer h 2 ε
      (hypFlag h 2 ε 1))
    (hl : l ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.isoStabilizer h 2 ε
      (hypFlag h 2 ε 2))
    (hk' : k' ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.isoStabilizer h 2 ε
      (hypFlag h 2 ε 1)) :
    burnsideF48_unW (ε := ε) h hc hc0 ≠ k * l * k' := by
  intro hw
  set e₀ : HypIndex 2 ε → K := Pi.single (.inl 0) 1 with he₀
  have he0 : e₀ ∈ posFlag 2 ε K 1 := by
    rw [burnsideF48_un_mem_posFlag_one_iff]
    intro a ha
    simp [he₀, Pi.single_apply, ha]
  have he0' : e₀ ∈ posFlag 2 ε K 2 := by
    rw [mem_posFlag]
    intro a ha
    have : a ≠ .inl 0 := by
      rintro rfl
      simp [fullPos] at ha
    simp [he₀, Pi.single_apply, this]
  have hk'e : ((k' : GL (HypIndex 2 ε) K) : Matrix (HypIndex 2 ε) (HypIndex 2 ε) K) *ᵥ e₀ ∈
      posFlag 2 ε K 1 := ((burnsideF48_un_stab_iff h hε (by norm_num)).1 hk' e₀).2 he0
  have h2 : ((k' : GL (HypIndex 2 ε) K) : Matrix (HypIndex 2 ε) (HypIndex 2 ε) K) *ᵥ e₀ ∈
      posFlag 2 ε K 2 := by
    rw [burnsideF48_un_posFlag_one hk'e]
    exact Submodule.smul_mem _ _ he0'
  have h3 := ((burnsideF48_un_stab_iff h hε le_rfl).1 hl _).2 h2
  have hu0 := burnsideF48_un_posFlag_two_f h3 0
  have hke : ((k : GL (HypIndex 2 ε) K) : Matrix (HypIndex 2 ε) (HypIndex 2 ε) K) *ᵥ e₀ ∈
      posFlag 2 ε K 1 := ((burnsideF48_un_stab_iff h hε (by norm_num)).1 hk e₀).2 he0
  set Gk := ((k : GL (HypIndex 2 ε) K) : Matrix (HypIndex 2 ε) (HypIndex 2 ε) K) with hGk
  have hrow := burnsideF48_un_f0_row (g := k) (c := (Gk *ᵥ e₀) (.inl 0))
    (burnsideF48_un_posFlag_one hke)
  have hfin : (Gk *ᵥ (((l : GL (HypIndex 2 ε) K) : Matrix (HypIndex 2 ε) (HypIndex 2 ε) K) *ᵥ
      (((k' : GL (HypIndex 2 ε) K) : Matrix (HypIndex 2 ε) (HypIndex 2 ε) K) *ᵥ e₀)))
        (.inr (.inr 0)) = 0 := by
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (.inr (.inr 0))]
    · exact (congrArg (fun x => Gk (.inr (.inr 0)) (.inr (.inr 0)) * x) hu0).trans (mul_zero _)
    · intro b _ hb
      exact mul_eq_zero_of_left (hrow b hb) _
    · simp
  have hWe := (weylMat_mulVec_of_inr (ε := ε) h c
    (burnsideF48_swapSet_mem 2 (Finset.univ : Finset (Fin 2))) (i := 0) (j := 0)
    (by simp [swapSet])).1
  have hmat : ((burnsideF48_unW (ε := ε) h hc hc0 : GL (HypIndex 2 ε) K) :
      Matrix (HypIndex 2 ε) (HypIndex 2 ε) K) = Gk *
      ((l : GL (HypIndex 2 ε) K) : Matrix (HypIndex 2 ε) (HypIndex 2 ε) K) *
        ((k' : GL (HypIndex 2 ε) K) : Matrix (HypIndex 2 ε) (HypIndex 2 ε) K) := by
    have := congrArg (fun g : hypSU h 2 ε => ((g : GL (HypIndex 2 ε) K) :
      Matrix (HypIndex 2 ε) (HypIndex 2 ε) K)) hw
    simpa only [Subgroup.coe_mul, Units.val_mul] using this
  rw [burnsideF48_unW_coe] at hmat
  have h5 : (weylMat h c (swapSet (Finset.univ : Finset (Fin 2))) *ᵥ e₀) =
      Gk *ᵥ (((l : GL (HypIndex 2 ε) K) : Matrix (HypIndex 2 ε) (HypIndex 2 ε) K) *ᵥ
        (((k' : GL (HypIndex 2 ε) K) : Matrix (HypIndex 2 ε) (HypIndex 2 ε) K) *ᵥ e₀)) := by
    rw [hmat, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [hWe] at h5
  have h6 : (c • (Pi.single (.inr (.inr 0)) 1 : HypIndex 2 ε → K)) (.inr (.inr 0)) = 0 :=
    (congrFun h5 (.inr (.inr 0))).trans hfin
  simp at h6
  exact hc0 h6

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.SpecialLinear Matrix in
theorem burnsideF48_un_cent (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {g : Kˣ}
    (hg1 : (g : K) ≠ 1) (hgb : (g : K) ≠ h.bar (g : K)) (hg2 : (g : K) ^ 2 ≠ 1)
    (hgn : h.norm (g : K) ≠ 1) {c : K}
    (hc : c ∈ h.traceZero) (hc0 : c ≠ 0) (H : hypSU h 2 ε)
    (hH : ((H : GL (HypIndex 2 ε) K) : Matrix (HypIndex 2 ε) (HypIndex 2 ε) K) =
      diagonal (burnsideF48_unD (ε := ε) h g))
    {q : hypPSU h 2 ε} (hq : q ∈ hypProjUnitriangular h 2 ε)
    (hnq : (hypProj h 2 ε (burnsideF48_unN (ε := ε) h hc hc0))⁻¹ * q *
      hypProj h 2 ε (burnsideF48_unN (ε := ε) h hc hc0) ∈ hypProjUnitriangular h 2 ε)
    (hcomm : hypProj h 2 ε H * q * (hypProj h 2 ε H)⁻¹ = q) : q = 1 := by
  obtain ⟨Q, hQ, rfl⟩ := hq
  obtain ⟨R, hR, hRQ⟩ := hnq
  set n := burnsideF48_unN (ε := ε) h hc hc0 with hn
  have hQ' := mem_hypUnitriangular.1 hQ
  have hR'' := mem_hypUnitriangular.1 hR
  have hnorm : ((Q : GL (HypIndex 2 ε) K) : Matrix (HypIndex 2 ε) (HypIndex 2 ε) K) (.inl 1)
        (.inr (.inr 1)) = 0 ∧
      (∀ k, ((Q : GL (HypIndex 2 ε) K) : Matrix (HypIndex 2 ε) (HypIndex 2 ε) K) (.inl 1)
        (.inr (.inl k)) = 0) ∧
      ∀ k, ((Q : GL (HypIndex 2 ε) K) : Matrix (HypIndex 2 ε) (HypIndex 2 ε) K) (.inr (.inl k))
        (.inr (.inr 1)) = 0 := by
    have hRQ' : hypProj h 2 ε R = hypProj h 2 ε (n⁻¹ * Q * n) := by
      rw [hRQ]
      simp [map_mul, map_inv]
    obtain ⟨c', hc'⟩ := burnsideF48_un_proj_eq_mat hRQ'
    have hmat : ((Q : GL (HypIndex 2 ε) K) : Matrix (HypIndex 2 ε) (HypIndex 2 ε) K) *
        weylMat h c (swapSet ({1} : Finset (Fin 2))) =
        weylMat h c (swapSet ({1} : Finset (Fin 2))) *
          (((R : GL (HypIndex 2 ε) K) : Matrix (HypIndex 2 ε) (HypIndex 2 ε) K) *
            (c' • (1 : Matrix (HypIndex 2 ε) (HypIndex 2 ε) K))) := by
      have h1 : Q * n = n * (n⁻¹ * Q * n) := by group
      have h2 := congrArg (fun X : hypSU h 2 ε => ((X : GL (HypIndex 2 ε) K) :
        Matrix (HypIndex 2 ε) (HypIndex 2 ε) K)) h1
      simp only [Subgroup.coe_mul, Units.val_mul] at h2 hc'
      rw [← burnsideF48_unN_coe h hc hc0, h2, hc']
    refine burnsideF48_un_normalize h hc0 ?_ hmat
    rw [Matrix.mul_smul, Matrix.mul_one]
    intro a b hab
    simp [Matrix.smul_apply, hR''.1 hab]
  have hc1 : hypProj h 2 ε (H * Q) = hypProj h 2 ε (Q * H) := by
    rw [map_mul, map_mul]
    exact mul_inv_eq_iff_eq_mul.1 hcomm
  obtain ⟨c₂, hc₂⟩ := burnsideF48_un_proj_eq_mat hc1
  simp only [Subgroup.coe_mul, Units.val_mul] at hc₂
  have hs : (c₂ • (1 : Matrix (HypIndex 2 ε) (HypIndex 2 ε) K)) =
      Matrix.scalar (HypIndex 2 ε) c₂ := by
    rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  rw [hH, hs] at hc₂
  have hg0 : (g : K) ≠ 0 := g.ne_zero
  have hbg0 : h.bar (g : K) ≠ 0 := (map_ne_zero h.bar).2 hg0
  have hQ1 : Q = 1 := by
    apply Subtype.ext
    apply Units.ext
    refine burnsideF48_un_eq_one hε (D := burnsideF48_unD (ε := ε) h g) hg0 ?_ ?_ ?_ ?_ ?_ ?_ ?_
      hQ'.1 hQ'.2 hnorm.1 hnorm.2.1 hnorm.2.2 hc₂
    · exact hgb
    · exact fun k => hg1
    · intro e
      apply hgn
      have e0 : (g : K) = (h.bar (g : K))⁻¹ := e
      have e' := congrArg (fun x => x * h.bar (g : K)) e0
      simpa [UnitaryFieldData.norm, hbg0] using e'
    · intro e
      apply hg2
      have e0 : (g : K) = (h.bar (h.bar (g : K)))⁻¹ := e
      rw [h.bar_bar] at e0
      have e' := congrArg (fun x => x * (g : K)) e0
      simpa [pow_two, hg0] using e'
    · intro e
      apply hg2
      have e0 : h.bar (g : K) = (h.bar (g : K))⁻¹ := e
      have e' := congrArg (fun x => x * h.bar (g : K)) e0
      have e2 : h.bar ((g : K) ^ 2) = h.bar 1 := by
        rw [map_pow, map_one, pow_two]
        simpa [hbg0] using e'
      exact h.bar.injective e2
    · intro k e
      apply hg1
      have e0 : (1 : K) = (h.bar (g : K))⁻¹ := e
      have e' : h.bar (g : K) = 1 := inv_eq_one.1 e0.symm
      exact h.bar.injective (by rw [e', map_one])
    · intro e
      apply hgb
      have e0 : (h.bar (h.bar (g : K)))⁻¹ = (h.bar (g : K))⁻¹ := e
      rw [h.bar_bar] at e0
      exact inv_injective e0
  rw [hQ1, map_one]

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.SpecialLinear Matrix in
open scoped Pointwise in
theorem burnsideF48_Un_cartan_proj (h : UnitaryFieldData p f K) (hε : ε ≤ 1) (hq : 3 ≤ p ^ f) :
    ∃ n w h' : hypPSU h 2 ε,
      n ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.projIsoStabilizer h 2 ε
        (hypFlag h 2 ε 1) ∧
      n ∉ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.projIsoStabilizer h 2 ε
        (hypFlag h 2 ε 2) ∧
      h' ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.projIsoStabilizer h 2 ε
        (hypFlag h 2 ε 1) ∧
      h' ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.projIsoStabilizer h 2 ε
        (hypFlag h 2 ε 2) ∧
      n⁻¹ * h' * n ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.projIsoStabilizer h 2 ε
        (hypFlag h 2 ε 2) ∧
      w⁻¹ * h' * w ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.projIsoStabilizer h 2 ε
        (hypFlag h 2 ε 1) ∧
      (¬ ∃ k ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.projIsoStabilizer h 2 ε
          (hypFlag h 2 ε 1),
        ∃ l ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.projIsoStabilizer h 2 ε
          (hypFlag h 2 ε 2),
        ∃ k' ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.projIsoStabilizer h 2 ε
          (hypFlag h 2 ε 1), w = k * l * k') ∧
      ∀ q ∈ hypProjUnitriangular h 2 ε, n⁻¹ * q * n ∈ hypProjUnitriangular h 2 ε →
        h' * q * h'⁻¹ = q → q = 1 := by
  obtain ⟨g, hg1, hgb, hg2, hgn⟩ := burnsideF48_un_exists_gen h hq
  obtain ⟨c, hc, hc0⟩ := exists_mem_traceZero_ne_zero' h
  obtain ⟨H, hHT, hH⟩ := burnsideF48_un_torus (ε := ε) h g
  have hmem : ∀ (W : Submodule K (HypIndex 2 ε → K)) (x : hypSU h 2 ε),
      hypProj h 2 ε x ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.projIsoStabilizer h 2 ε W ↔
        x ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.isoStabilizer h 2 ε W := by
    intro W x
    rw [← CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.comap_projIsoStabilizer W]
    rfl
  have hHB : H ∈ hypBorel h 2 ε := hypTorus_le_hypBorel h hHT
  have hHstab : ∀ i : ℕ, 1 ≤ i → i ≤ 2 → H ∈
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.isoStabilizer h 2 ε (hypFlag h 2 ε i) :=
    fun i hi1 hi2 => CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_isoStabilizer.2
      (mem_hypBorel.1 hHB i hi1 hi2)
  refine ⟨hypProj h 2 ε (burnsideF48_unN (ε := ε) h hc hc0),
    hypProj h 2 ε (burnsideF48_unW (ε := ε) h hc hc0), hypProj h 2 ε H, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [hmem]
    exact burnsideF48_unN_mem_stab_one h hε hc hc0
  · rw [hmem]
    exact burnsideF48_unN_not_mem_stab_two h hε hc hc0
  · rw [hmem]
    exact hHstab 1 le_rfl (by norm_num)
  · rw [hmem]
    exact hHstab 2 (by norm_num) le_rfl
  · rw [← map_inv, ← map_mul, ← map_mul, hmem]
    exact CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_isoStabilizer.2
      (mem_hypBorel.1 (burnsideF48_un_conj_diag_mem_borel h hc hc0 {1} _ H hH) 2 (by norm_num)
        le_rfl)
  · rw [← map_inv, ← map_mul, ← map_mul, hmem]
    exact CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_isoStabilizer.2
      (mem_hypBorel.1 (burnsideF48_un_conj_diag_mem_borel h hc hc0 Finset.univ _ H hH) 1 le_rfl
        (by norm_num))
  · rintro ⟨k, ⟨k₀, hk₀, rfl⟩, l, ⟨l₀, hl₀, rfl⟩, k', ⟨k₀', hk₀', rfl⟩, hkl⟩
    have h1 : hypProj h 2 ε (k₀ * l₀ * k₀') = hypProj h 2 ε (burnsideF48_unW (ε := ε) h hc hc0) := by
      rw [map_mul, map_mul]
      exact hkl.symm
    have hz : (k₀ * l₀ * k₀')⁻¹ * burnsideF48_unW (ε := ε) h hc hc0 ∈ hypScalars h 2 ε :=
      QuotientGroup.eq.1 h1
    have hz' := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.hypScalars_le_isoStabilizer
      (hypFlag h 2 ε 1) hz
    refine burnsideF48_unW_ne_mul h hε hc hc0 hk₀ hl₀
      ((CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.isoStabilizer h 2 ε
        (hypFlag h 2 ε 1)).mul_mem hk₀' hz') ?_
    group
  · intro q hq' hnq hc'
    exact burnsideF48_un_cent h hε hg1 hgb hg2 hgn hc hc0 H hH hq' hnq hc'

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.SpecialLinear Matrix in
open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_cartanFPF_un_of_iso {κ : ChF.GLKind} {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime) (hm : 3 ≤ κ.m)
    (hκ : κ.m = 4) (hpoly : IsGenPolygon (burnsideF48_setting hyp hp hm).ι.graph 4)
    (h : UnitaryFieldData p f K) (hε : ε ≤ 1) (hq : 3 ≤ p ^ f) (Φ : hypPSU h 2 ε ≃* ↥Gp)
    (hP₁ : ∀ g : hypPSU h 2 ε, ((Φ g : ↥Gp) : E) ∈ M₁ ↔
      g ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.projIsoStabilizer h 2 ε
        (hypFlag h 2 ε 1))
    (hP₂ : ∀ g : hypPSU h 2 ε, ((Φ g : ↥Gp) : E) ∈ M₂ ↔
      g ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.projIsoStabilizer h 2 ε
        (hypFlag h 2 ε 2)) :
    (burnsideF48_setting hyp hp hm).CartanFPF := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, w, h', hn1, hn2, hh1, hh2, hh3, hh4, hw, hQ⟩ :=
    burnsideF48_Un_cartan_proj (ε := ε) h hε hq
  obtain ⟨SU, hSU⟩ := (unitary_order_and_Sylow h (r := 2) (ε := ε) (by norm_num) hε).2.2.2.2.1
  haveI := h.finite
  refine burnsideF48_cartanFPF_of_data_four hyp hp hm hκ hpoly Φ
    (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.projIsoStabilizer h 2 ε (hypFlag h 2 ε 1))
    (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.projIsoStabilizer h 2 ε (hypFlag h 2 ε 2))
    (hypProjUnitriangular h 2 ε) hP₁ hP₂ (burnsideF48_isSylowOf_of_equiv _ ⟨SU, hSU⟩) ?_
    n w h' hn1 hn2 hh1 hh2 hh3 hh4 hw hQ
  · rintro _ ⟨u, hu, rfl⟩
    refine ⟨u, ?_, rfl⟩
    exact CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_isoStabilizer.2
      (mem_hypBorel.1 (hypUnitriangular_le_hypBorel h hu) 1 le_rfl (by norm_num))

end UnCore


open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_cartanFPF_U4 {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : ChF.HypF_4_4 .U4 p f Gp M₁ M₂) (hp : p.Prime) (hm : 3 ≤ ChF.GLKind.U4.m)
    (hq : 3 ≤ p ^ f) (hpoly : IsGenPolygon (burnsideF48_setting hyp hp hm).ι.graph 4) :
    (burnsideF48_setting hyp hp hm).CartanFPF := by
  obtain ⟨marking, h1, h2⟩ := burnsideF48_marking (c := .U4) hyp.toHypF_4_4g
  refine burnsideF48_cartanFPF_un_of_iso hyp hp hm rfl hpoly
    (burnsideF4h_clu_U4_fieldData marking) (ε := 0) (by norm_num) hq
    (burnsideF4h_clu_U4_Phi marking) ?_ ?_
  · intro g
    have h3 := burnsideF4h_clu_U4_parabolic marking false
    simp only [Bool.false_eq_true, if_false] at h3
    show burnsideF4h_clu_U4_Phi marking g ∈ M₁.subgroupOf Gp ↔ _
    rw [h1, h3, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  · intro g
    have h3 := burnsideF4h_clu_U4_parabolic marking true
    simp only [if_true] at h3
    show burnsideF4h_clu_U4_Phi marking g ∈ M₂.subgroupOf Gp ↔ _
    rw [h2, h3, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_cartanFPF_U5 {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : ChF.HypF_4_4 .U5 p f Gp M₁ M₂) (hp : p.Prime) (hm : 3 ≤ ChF.GLKind.U5.m)
    (hq : 3 ≤ p ^ f) (hpoly : IsGenPolygon (burnsideF48_setting hyp hp hm).ι.graph 4) :
    (burnsideF48_setting hyp hp hm).CartanFPF := by
  obtain ⟨marking, h1, h2⟩ := burnsideF48_marking (c := .U5) hyp.toHypF_4_4g
  refine burnsideF48_cartanFPF_un_of_iso hyp hp hm rfl hpoly
    (burnsideF4h_clu_U5_fieldData marking) (ε := 1) le_rfl hq
    (burnsideF4h_clu_U5_Phi marking) ?_ ?_
  · intro g
    have h3 := burnsideF4h_clu_U5_parabolic marking false
    simp only [Bool.false_eq_true, if_false] at h3
    show burnsideF4h_clu_U5_Phi marking g ∈ M₁.subgroupOf Gp ↔ _
    rw [h1, h3, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  · intro g
    have h3 := burnsideF4h_clu_U5_parabolic marking true
    simp only [if_true] at h3
    show burnsideF4h_clu_U5_Phi marking g ∈ M₂.subgroupOf Gp ↔ _
    rw [h2, h3, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

theorem burnsideF48_simple_U4 {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : ChF.HypF_4_4 .U4 p f Gp M₁ M₂) : IsSimpleGroup ↥Gp := by
  obtain ⟨hp, -, K, hK, hKfin, hcard, ⟨e⟩⟩ := hyp.model
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K p f hcard 4
    (by norm_num) (by simp)
  exact e.isSimpleGroup

theorem burnsideF48_simple_U5 {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : ChF.HypF_4_4 .U5 p f Gp M₁ M₂) : IsSimpleGroup ↥Gp := by
  obtain ⟨hp, -, K, hK, hKfin, hcard, ⟨e⟩⟩ := hyp.model
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K p f hcard 5
    (by norm_num) (by simp)
  exact e.isSimpleGroup

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_concl_U4 (hF : F_4_5) (hcompat : ChF.NativeChartCompatibilityGoal)
    {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : ChF.HypF_4_4 .U4 p f Gp M₁ M₂) (hq : 3 ≤ p ^ f) : ChF.F48Concl .U4 p f Gp M₁ M₂ := by
  have hP := burnsideF48_parabolics_of_compat hcompat hyp
  have hp := ChF.burnsideF4a_prime_of_isGenLie hyp.model
  have hm := burnsideF48_three_le_m .U4
  have hL : ChF.GLKind.U4.IsLie :=
    show ChF.GLKind.U4 ≠ ChF.GLKind.G2d ∧ ChF.GLKind.U4 ≠ ChF.GLKind.Tits from
      ⟨by decide, by decide⟩
  refine burnsideF48_concl_of_F45_cartan hF hyp hL (burnsideF48_simple_U4 hyp) hP ?_
  exact burnsideF48_cartanFPF_U4 hyp hp hm hq
    (burnsideF48_facts45L_of_F45 hF hyp hL hp hm hP).poly

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_concl_U5 (hF : F_4_5) (hcompat : ChF.NativeChartCompatibilityGoal)
    {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : ChF.HypF_4_4 .U5 p f Gp M₁ M₂) (hq : 3 ≤ p ^ f) : ChF.F48Concl .U5 p f Gp M₁ M₂ := by
  have hP := burnsideF48_parabolics_of_compat hcompat hyp
  have hp := ChF.burnsideF4a_prime_of_isGenLie hyp.model
  have hm := burnsideF48_three_le_m .U5
  have hL : ChF.GLKind.U5.IsLie :=
    show ChF.GLKind.U5 ≠ ChF.GLKind.G2d ∧ ChF.GLKind.U5 ≠ ChF.GLKind.Tits from
      ⟨by decide, by decide⟩
  refine burnsideF48_concl_of_F45_cartan hF hyp hL (burnsideF48_simple_U5 hyp) hP ?_
  exact burnsideF48_cartanFPF_U5 hyp hp hm hq
    (burnsideF48_facts45L_of_F45 hF hyp hL hp hm hP).poly

end CFSG.ASVolI
