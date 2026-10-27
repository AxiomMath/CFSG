module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem5C

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem L_le_MV_ch625 : L ≤ ch6MV M V := fun _ hl => ⟨h.L_le hl, h.toHyp611.L_le_normalizer hl⟩

theorem T_le_MV_ch625 : T ≤ ch6MV M V := fun _ ht => ⟨h.T_le ht, h.toHyp611.T_le_normalizer ht⟩

theorem conj_eq_of_conjAct_eq {g g' : Subgroup.normalizer (V : Set G)}
    (hgg : conjAct V g = conjAct V g') (w : Fin 2 → h.data.K) :
    h.data.conj g w = h.data.conj g' w := by
  obtain ⟨v, rfl⟩ : ∃ v : ↥V, Multiplicative.toAdd (h.data.E v) = w :=
    ⟨h.data.E.symm (Multiplicative.ofAdd w), by simp⟩
  rw [h.data.conj_apply, h.data.conj_apply, hgg]

theorem conjAct_eq_of_conj_eq {g g' : Subgroup.normalizer (V : Set G)}
    (hgg : ∀ w, h.data.conj g w = h.data.conj g' w) : conjAct V g = conjAct V g' := by
  ext v
  have h1 := hgg (Multiplicative.toAdd (h.data.E v))
  rw [h.data.conj_apply, h.data.conj_apply] at h1
  exact congrArg Subtype.val (h.data.E.injective (Multiplicative.toAdd.injective h1))

theorem det625_mul_of_lin {n : Subgroup.normalizer (V : Set G)} (hn : h.IsLin625 n)
    (m : Subgroup.normalizer (V : Set G)) : h.det625 (n * m) = h.det625 m * h.det625 n := by
  unfold det625
  rw [h.data.conj_mul, h.data.conj_mul, h.det2_conj_lin_ch625 hn]
  rfl

theorem exists_L_of_det_one {m : Subgroup.normalizer (V : Set G)}
    (hmL : (m : G) ∈ Subgroup.normalizer (L : Set G)) (hm : h.IsLin625 m)
    (hdet : h.det625 m = 1) : ∃ y : Subgroup.normalizer (V : Set G), (y : G) ∈ L ∧
      ∀ w, h.data.conj m w = h.data.conj y w := by
  have hK := h.card_K_ch625
  obtain ⟨y, hyL, μ, hμ0, hμ2, hmy⟩ := h.exists_eq_smul_conj_ch625 m hmL hm
  rw [hdet] at hμ2
  have hμ1 : μ = 1 := by
    have h3 := pow_three_ch625 hK hμ0
    have e : μ ^ 3 = μ ^ 2 * μ := pow_succ μ 2
    rw [e, hμ2, one_mul] at h3
    exact h3
  exact ⟨y, hyL, fun w => by rw [hmy, hμ1, one_smul]⟩

omit [Finite G] h in
theorem conjAct_mem_autOn_MV {m : G} (hm : m ∈ ch6MV M V) :
    conjAct V ⟨m, hm.2⟩ ∈ autOn (ch6MV M V) V :=
  mem_autOn_iff.mpr ⟨⟨m, hm.2⟩, hm, rfl⟩

theorem isLin625_inv {m : Subgroup.normalizer (V : Set G)} (hm : h.IsLin625 m) :
    h.IsLin625 m⁻¹ := by
  intro c w
  apply (h.data.conj m).injective
  rw [h.conj_conj_inv_ch625, hm, h.conj_conj_inv_ch625]

theorem det625_eq_one_of_lin
    (hidx : (autOn L V).relIndex (autOn (ch6MV M V) V) = 2) {m : G} (hm : m ∈ ch6MV M V)
    (hlin : h.IsLin625 ⟨m, hm.2⟩) : h.det625 ⟨m, hm.2⟩ = 1 := by
  have hK := h.card_K_ch625
  set mm : Subgroup.normalizer (V : Set G) := ⟨m, hm.2⟩ with hmm
  have hidx' : ((autOn L V).subgroupOf (autOn (ch6MV M V) V)).index = 2 := hidx
  have hsq := Subgroup.sq_mem_of_index_two hidx'
    ⟨conjAct V mm, conjAct_mem_autOn_MV hm⟩
  rw [Subgroup.mem_subgroupOf] at hsq
  have e : (((⟨conjAct V mm, conjAct_mem_autOn_MV hm⟩ : ↥(autOn (ch6MV M V) V)) ^ 2 :
      ↥(autOn (ch6MV M V) V)) : MulAut ↥V) = conjAct V (mm * mm) := by
    simp [pow_two, map_mul]
  rw [e] at hsq
  obtain ⟨y, hyL, hy⟩ := mem_autOn_iff.mp hsq
  have hyy := h.isLin625_and_det_of_mem_L y hyL
  have hdet : h.det625 (mm * mm) = 1 := by
    have := h.conj_eq_of_conjAct_eq hy
    unfold det625
    rw [← this, ← this]
    exact hyy.2
  rw [h.det625_mul_of_lin hlin] at hdet
  have hne := h.det625_ne_zero mm (h.normal hm.1)
  have h3 := pow_three_ch625 hK hne
  have e3 : h.det625 mm ^ 3 = (h.det625 mm * h.det625 mm) * h.det625 mm := by ring
  rw [e3, hdet, one_mul] at h3
  exact h3

theorem det625_eq_of_not_lin
    (hidx : (autOn L V).relIndex (autOn (ch6MV M V) V) = 2) {m m' : G} (hm : m ∈ ch6MV M V)
    (hm' : m' ∈ ch6MV M V) (hlin : ¬ h.IsLin625 ⟨m, hm.2⟩) (hlin' : ¬ h.IsLin625 ⟨m', hm'.2⟩) :
    h.det625 ⟨m, hm.2⟩ = h.det625 ⟨m', hm'.2⟩ := by
  have hK := h.card_K_ch625
  set mm : Subgroup.normalizer (V : Set G) := ⟨m, hm.2⟩ with hmm
  set mm' : Subgroup.normalizer (V : Set G) := ⟨m', hm'.2⟩ with hmm'
  have hf := (h.semilinear_cases_ch625 mm (h.normal hm.1)).resolve_left hlin
  have hf' := (h.semilinear_cases_ch625 mm' (h.normal hm'.1)).resolve_left hlin'
  have hninM : m' * m⁻¹ ∈ ch6MV M V := (ch6MV M V).mul_mem hm' ((ch6MV M V).inv_mem hm)
  have hfinv : ∀ (c : h.data.K) w, h.data.conj mm⁻¹ (c • w) = c ^ 2 • h.data.conj mm⁻¹ w := by
    intro c w
    apply (h.data.conj mm).injective
    rw [h.conj_conj_inv_ch625, hf, h.conj_conj_inv_ch625, sq_sq_ch625 hK]
  have hnlin : h.IsLin625 ⟨m' * m⁻¹, hninM.2⟩ := by
    intro c w
    have e : (⟨m' * m⁻¹, hninM.2⟩ : Subgroup.normalizer (V : Set G)) = mm' * mm⁻¹ := rfl
    rw [e, h.data.conj_mul, h.data.conj_mul, hfinv, hf', sq_sq_ch625 hK]
  have h1 := h.det625_eq_one_of_lin hidx hninM hnlin
  have e : mm' = (⟨m' * m⁻¹, hninM.2⟩ : Subgroup.normalizer (V : Set G)) * mm := by
    apply Subtype.ext
    simp [hmm, hmm']
  rw [e, h.det625_mul_of_lin hnlin, h1, mul_one]

theorem exists_not_lin_T (h331 : Stmt3_3_1) (h615 : Stmt6_1_5) :
    ∃ t, ∃ ht : t ∈ T, ¬ h.IsLin625 ⟨t, h.toHyp611.T_le_normalizer ht⟩ := by
  obtain ⟨t, htT, htZ⟩ := h.exists_not_mem_centralizer_ZS h331 h615
  refine ⟨t, htT, fun hlin => htZ ?_⟩
  obtain ⟨v, hv, hle⟩ := h.toHyp611Nat.exists_line
  exact h.toHyp611Nat.mem_centralizer_ZS_of_linear hv hle htT hlin

theorem relIndex_le_two_of_det_eq_one (h331 : Stmt3_3_1) (h615 : Stmt6_1_5)
    (hall : ∀ m (hm : m ∈ ch6MV M V), h.IsLin625 ⟨m, hm.2⟩ → h.det625 ⟨m, hm.2⟩ = 1) :
    (autOn L V).relIndex (autOn (ch6MV M V) V) ≤ 2 := by
  have hK := h.card_K_ch625
  obtain ⟨t₀, ht₀T, ht₀⟩ := h.exists_not_lin_T h331 h615
  have ht₀M : t₀ ∈ ch6MV M V := h.T_le_MV_ch625 ht₀T
  set K' := autOn (ch6MV M V) V with hK'
  set H' := (autOn L V).subgroupOf K' with hH'
  set τ : ↥K' := ⟨conjAct V ⟨t₀, ht₀M.2⟩, conjAct_mem_autOn_MV ht₀M⟩ with hτ
  have hcases : ∀ φ : ↥K', φ ∈ H' ∨ φ⁻¹ * τ ∈ H' := by
    rintro ⟨φ, hφ⟩
    obtain ⟨m, hmM, rfl⟩ := mem_autOn_iff.mp hφ
    have hmM' : (m : G) ∈ ch6MV M V := hmM
    by_cases hlin : h.IsLin625 m
    · left
      obtain ⟨y, hyL, hy⟩ := h.exists_L_of_det_one (h.normal hmM'.1) hlin (hall m hmM' hlin)
      rw [Subgroup.mem_subgroupOf]
      exact mem_autOn_iff.mpr ⟨y, hyL, (h.conjAct_eq_of_conj_eq hy).symm⟩
    · right
      have hfm := (h.semilinear_cases_ch625 m (h.normal hmM'.1)).resolve_left hlin
      have hft := (h.semilinear_cases_ch625 ⟨t₀, ht₀M.2⟩ (h.normal ht₀M.1)).resolve_left ht₀
      set n : Subgroup.normalizer (V : Set G) := m⁻¹ * ⟨t₀, ht₀M.2⟩ with hn
      have hnM : (n : G) ∈ ch6MV M V :=
        (ch6MV M V).mul_mem ((ch6MV M V).inv_mem hmM') ht₀M
      have hfminv : ∀ (c : h.data.K) w, h.data.conj m⁻¹ (c • w) = c ^ 2 • h.data.conj m⁻¹ w := by
        intro c w
        apply (h.data.conj m).injective
        rw [h.conj_conj_inv_ch625, hfm, h.conj_conj_inv_ch625, sq_sq_ch625 hK]
      have hnlin : h.IsLin625 n := by
        intro c w
        rw [hn, h.data.conj_mul, h.data.conj_mul, hft, hfminv, sq_sq_ch625 hK]
      obtain ⟨y, hyL, hy⟩ := h.exists_L_of_det_one (h.normal hnM.1) hnlin (hall n hnM hnlin)
      rw [Subgroup.mem_subgroupOf]
      have e : ((⟨conjAct V m, hφ⟩ : ↥K')⁻¹ * τ : ↥K').1 = conjAct V n := by
        simp [hτ, hn, map_mul, map_inv]
      rw [e]
      exact mem_autOn_iff.mpr ⟨y, hyL, (h.conjAct_eq_of_conj_eq hy).symm⟩
  have hsurj : Function.Surjective (fun b : Bool =>
      if b then (QuotientGroup.mk τ : ↥K' ⧸ H') else (QuotientGroup.mk 1 : ↥K' ⧸ H')) := by
    intro q
    obtain ⟨φ, rfl⟩ := QuotientGroup.mk_surjective q
    rcases hcases φ with hφ | hφ
    · refine ⟨false, ?_⟩
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [QuotientGroup.eq]
      simpa using hφ
    · refine ⟨true, ?_⟩
      simp only [↓reduceIte]
      rw [QuotientGroup.eq]
      simpa [mul_inv_rev] using H'.inv_mem hφ
  have h2 := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h2
  exact h2

theorem exists_scalar_of_det_ne_one {m : G} (hm : m ∈ ch6MV M V) (hlin : h.IsLin625 ⟨m, hm.2⟩)
    (hdet : h.det625 ⟨m, hm.2⟩ ≠ 1) :
    ∃ s ∈ ch6MV M V, ∃ μ : h.data.K, μ ≠ 0 ∧ μ ≠ 1 ∧
      ∀ hs : s ∈ Subgroup.normalizer (V : Set G), ∀ w, h.data.conj ⟨s, hs⟩ w = μ • w := by
  obtain ⟨y, hyL, μ, hμ0, hμ2, hmy⟩ := h.exists_eq_smul_conj_ch625 ⟨m, hm.2⟩ (h.normal hm.1)
    hlin
  have hyM : (y : G) ∈ ch6MV M V := h.L_le_MV_ch625 hyL
  have hyinv : (y : G)⁻¹ ∈ ch6MV M V := (ch6MV M V).inv_mem hyM
  refine ⟨(y : G)⁻¹ * m, (ch6MV M V).mul_mem hyinv hm, μ, hμ0, fun h1 => hdet ?_, ?_⟩
  · rw [← hμ2, h1, one_pow]
  · intro hs w
    have hylin := (h.isLin625_and_det_of_mem_L y hyL).1
    have e : (⟨(y : G)⁻¹ * m, hs⟩ : Subgroup.normalizer (V : Set G)) = y⁻¹ * ⟨m, hm.2⟩ := rfl
    rw [e, h.data.conj_mul, hmy, h.isLin625_inv hylin, h.conj_inv_conj_ch625]

theorem exists_scalar_of_six (h331 : Stmt3_3_1) (h615 : Stmt6_1_5)
    (hidx : (autOn L V).relIndex (autOn (ch6MV M V) V) = 6) :
    ∃ s ∈ ch6MV M V, ∃ μ : h.data.K, μ ≠ 0 ∧ μ ≠ 1 ∧
      ∀ hs : s ∈ Subgroup.normalizer (V : Set G), ∀ w, h.data.conj ⟨s, hs⟩ w = μ • w := by
  by_contra hcon
  have hall : ∀ m (hm : m ∈ ch6MV M V), h.IsLin625 ⟨m, hm.2⟩ → h.det625 ⟨m, hm.2⟩ = 1 := by
    intro m hm hlin
    by_contra hdet
    exact hcon (h.exists_scalar_of_det_ne_one hm hlin hdet)
  have := h.relIndex_le_two_of_det_eq_one h331 h615 hall
  omega

theorem exists_L_basis_ch625 {x y x' y' : Fin 2 → h.data.K} (hxy : det2 x y ≠ 0)
    (heq : det2 x' y' = det2 x y) : ∃ l : Subgroup.normalizer (V : Set G), (l : G) ∈ L ∧
      h.data.conj l x = x' ∧ h.data.conj l y = y' := by
  obtain ⟨B, hB1, hB2⟩ := exists_sl2_basis hxy heq
  obtain ⟨l, hlL, hl⟩ := h.data.exists_mem_of_matrix B
  exact ⟨l, hlL, by rw [hl, hB1], by rw [hl, hB2]⟩

theorem exists_MV_basis_of_scalar {s : G} (hsM : s ∈ ch6MV M V) {μ : h.data.K} (hμ0 : μ ≠ 0)
    (hμ1 : μ ≠ 1)
    (hs : ∀ hs : s ∈ Subgroup.normalizer (V : Set G), ∀ w, h.data.conj ⟨s, hs⟩ w = μ • w)
    {x y x' y' : Fin 2 → h.data.K} (hxy : det2 x y ≠ 0) (hxy' : det2 x' y' ≠ 0) :
    ∃ m ∈ ch6MV M V, ∃ hm : m ∈ Subgroup.normalizer (V : Set G), h.IsLin625 ⟨m, hm⟩ ∧
      h.data.conj ⟨m, hm⟩ x = x' ∧ h.data.conj ⟨m, hm⟩ y = y' := by
  have hK := h.card_K_ch625
  set lam := det2 x' y' / det2 x y with hlam
  have hlam0 : lam ≠ 0 := div_ne_zero hxy' hxy
  have hμ2 : μ ^ 2 ≠ 1 := by
    intro h1
    apply hμ1
    have := sq_sq_ch625 hK μ
    rw [h1, one_pow] at this
    exact this.symm
  have hμ2' : μ ^ 2 ≠ μ := by
    intro h1
    apply hμ1
    have e : μ ^ 2 = μ * μ := pow_two μ
    rw [e] at h1
    exact mul_left_cancel₀ hμ0 (h1.trans (mul_one μ).symm)
  have key : ∃ k : ℕ, (μ ^ k) ^ 2 = lam := by
    rcases eq_of_three_ch625 hK one_ne_zero (pow_ne_zero 2 hμ0) hμ0 hlam0 (Ne.symm hμ2)
        (Ne.symm hμ1) hμ2' with h1 | h1 | h1
    · exact ⟨0, by rw [h1]; ring⟩
    · exact ⟨1, by rw [h1, pow_one]⟩
    · exact ⟨2, by rw [h1, ← pow_mul]; norm_num; exact pow_four_ch625 hK μ⟩
  obtain ⟨k, hk⟩ := key
  set ν := μ ^ k with hν
  have hν0 : ν ≠ 0 := pow_ne_zero k hμ0
  have hdet : det2 (ν⁻¹ • x') (ν⁻¹ • y') = det2 x y := by
    rw [det2_smul_left_ch625, det2_smul_right_ch625]
    have : det2 x' y' = ν ^ 2 * det2 x y := by
      rw [hk, hlam, div_mul_cancel₀ _ hxy]
    rw [this]
    field_simp
  obtain ⟨l, hlL, hlx, hly⟩ := h.exists_L_basis_ch625 hxy hdet
  set ss : Subgroup.normalizer (V : Set G) := ⟨s, hsM.2⟩ with hss
  have hsj : ∀ (j : ℕ) w, h.data.conj (ss ^ j) w = μ ^ j • w := by
    intro j
    induction j with
    | zero => intro w; rw [pow_zero, pow_zero, one_smul, h.conj_one_ch625]
    | succ j ih =>
      intro w
      rw [pow_succ, h.data.conj_mul, hs, ih, smul_smul, ← pow_succ]
  have hsk : ∀ w, h.data.conj (ss ^ k) w = ν • w := hsj k
  have hlM : (l : G) ∈ ch6MV M V := h.L_le_MV_ch625 hlL
  have hskM : ((ss ^ k : Subgroup.normalizer (V : Set G)) : G) ∈ ch6MV M V := by
    rw [Subgroup.coe_pow]
    exact Subgroup.pow_mem _ hsM k
  have hllin := (h.isLin625_and_det_of_mem_L l hlL).1
  refine ⟨((ss ^ k * l : Subgroup.normalizer (V : Set G)) : G),
    (ch6MV M V).mul_mem hskM hlM, (ss ^ k * l).2, ?_, ?_, ?_⟩
  · intro c w
    show h.data.conj (ss ^ k * l) (c • w) = c • h.data.conj (ss ^ k * l) w
    rw [h.data.conj_mul, h.data.conj_mul, hllin, hsk, hsk, smul_comm]
  · rw [h.data.conj_mul, hlx, hsk, smul_smul, mul_inv_cancel₀ hν0, one_smul]
  · rw [h.data.conj_mul, hly, hsk, smul_smul, mul_inv_cancel₀ hν0, one_smul]

theorem exists_MV_basis_six (h331 : Stmt3_3_1) (h615 : Stmt6_1_5)
    (hidx : (autOn L V).relIndex (autOn (ch6MV M V) V) = 6) {x y x' y' : Fin 2 → h.data.K}
    (hxy : det2 x y ≠ 0) (hxy' : det2 x' y' ≠ 0) :
    ∃ m ∈ ch6MV M V, ∃ hm : m ∈ Subgroup.normalizer (V : Set G), h.IsLin625 ⟨m, hm⟩ ∧
      h.data.conj ⟨m, hm⟩ x = x' ∧ h.data.conj ⟨m, hm⟩ y = y' := by
  obtain ⟨s, hsM, μ, hμ0, hμ1, hs⟩ := h.exists_scalar_of_six h331 h615 hidx
  exact h.exists_MV_basis_of_scalar hsM hμ0 hμ1 hs hxy hxy'

end Hyp6Sec2

end CFSG.Quasithin.H13
