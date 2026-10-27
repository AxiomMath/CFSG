module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem5E

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem isCentralType_conjSubgroup {F : Subgroup G} {g : G} (hg : g ∈ ch6MV M V)
    (hF : IsCentralType L V F 1) : IsCentralType L V (conjSubgroup F g) 1 := by
  obtain ⟨hFV, hF4, P, hP, hPC⟩ := hF
  rw [conjSubgroup_one] at hFV hP
  have hVg : conjSubgroup V g = V := conjSubgroup_eq_iff_mem_normalizer.mpr hg.2
  have hLg : conjSubgroup L g = L := conjSubgroup_eq_iff_mem_normalizer.mpr (h.normal hg.1)
  refine ⟨?_, by rw [card_conjSubgroup, hF4], conjSubgroup P g, ?_, ?_⟩
  · rw [conjSubgroup_one, ← hVg]; exact conjSubgroup_mono_left g hFV
  · rw [conjSubgroup_one, ← hLg]
    exact isSylowIn_conjSubgroup_ch625 hP g
  · intro p hp
    rw [mem_conjSubgroup_iff] at hp
    refine Subgroup.mem_centralizer_iff.mpr fun f hf => ?_
    have hf' : g * f * g⁻¹ ∈ F := mem_conjSubgroup_iff.mp hf
    have h1 := Subgroup.mem_centralizer_iff.mp (hPC hp) _ hf'
    calc f * p = g⁻¹ * ((g * f * g⁻¹) * (g * p * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * p * g⁻¹) * (g * f * g⁻¹)) * g := by rw [h1]
      _ = p * f := by group

theorem isFieldType_conjSubgroup {F : Subgroup G} {g : G} (hg : g ∈ ch6MV M V)
    (hF : IsFieldType M L V F 1) : IsFieldType M L V (conjSubgroup F g) 1 := by
  obtain ⟨hFV, hF4, t, htM, ht, htF⟩ := hF
  rw [conjSubgroup_one] at hFV htM ht
  have hVg : conjSubgroup V g = V := conjSubgroup_eq_iff_mem_normalizer.mpr hg.2
  refine ⟨?_, by rw [card_conjSubgroup, hF4], g⁻¹ * t * g, ?_, ?_, ?_⟩
  · rw [conjSubgroup_one, ← hVg]; exact conjSubgroup_mono_left g hFV
  · rw [conjSubgroup_one]
    have := (ch6MV M V).mul_mem ((ch6MV M V).mul_mem ((ch6MV M V).inv_mem hg) htM) hg
    exact this
  · rw [conjSubgroup_one]
    have := ht.conj_ch6 (x := g) (h.normal hg.1)
    exact this
  · refine Subgroup.mem_centralizer_iff.mpr fun f hf => ?_
    have hf' : g * f * g⁻¹ ∈ F := mem_conjSubgroup_iff.mp hf
    have h1 := Subgroup.mem_centralizer_iff.mp htF _ hf'
    calc f * (g⁻¹ * t * g) = g⁻¹ * ((g * f * g⁻¹) * t) * g := by group
      _ = g⁻¹ * (t * (g * f * g⁻¹)) * g := by rw [h1]
      _ = g⁻¹ * t * g * f := by group

theorem fieldType_det {F : Subgroup G} (hFV : F ≤ V) (hF4 : Nat.card F = 4)
    (hF : IsFieldType M L V F 1) {x y : Fin 2 → h.data.K} (hP : h.IsPlane625 F x y) :
    ∃ t ∈ ch6MV M V, ∃ htN : t ∈ Subgroup.normalizer (V : Set G), ¬ h.IsLin625 ⟨t, htN⟩ ∧
      h.det625 ⟨t, htN⟩ = (det2 x y)⁻¹ := by
  obtain ⟨t, htM, htF, htN, hlin⟩ := (h.isFieldType_iff_ch625 hFV hF4).mp hF
  exact ⟨t, htM, htN, hlin, h.det625_eq_inv_of_fix (h.normal htM.1) hlin hP.1
    (h.conj_fix_of_mem_centralizer htN htF ((hP.2 x).mpr (Or.inr (Or.inl rfl))))
    (h.conj_fix_of_mem_centralizer htN htF ((hP.2 y).mpr (Or.inr (Or.inr (Or.inl rfl)))))⟩

theorem isFieldType_of_det {F : Subgroup G} (hFV : F ≤ V) (hF4 : Nat.card F = 4)
    {x y : Fin 2 → h.data.K} (hP : h.IsPlane625 F x y) {t₀ : G} (ht₀M : t₀ ∈ ch6MV M V)
    (ht₀ : ¬ h.IsLin625 ⟨t₀, ht₀M.2⟩) (hdet : det2 x y = (h.det625 ⟨t₀, ht₀M.2⟩)⁻¹) :
    IsFieldType M L V F 1 := by
  have hfrob := (h.semilinear_cases_ch625 ⟨t₀, ht₀M.2⟩ (h.normal ht₀M.1)).resolve_left ht₀
  have hd0 := h.det625_ne_zero ⟨t₀, ht₀M.2⟩ (h.normal ht₀M.1)
  have heq : det2 x y = det2 (h.data.conj ⟨t₀, ht₀M.2⟩ x) (h.data.conj ⟨t₀, ht₀M.2⟩ y) := by
    rw [h.det2_conj_frob_ch625 hfrob, hdet]
    field_simp
  have hdet0 : det2 (h.data.conj ⟨t₀, ht₀M.2⟩ x) (h.data.conj ⟨t₀, ht₀M.2⟩ y) ≠ 0 := by
    rw [← heq]; exact hP.1
  obtain ⟨l, hlL, hlx, hly⟩ := h.exists_L_basis_ch625 hdet0 heq
  exact h.isFieldType_of_isPlane625 hFV hF4 hP ht₀M ht₀ (h.L_le_MV_ch625 hlL)
    (h.isLin625_and_det_of_mem_L l hlL).1 hlx hly

theorem eq_mul_sq_of_ne_ch625 {d δ δ' : h.data.K} (hd : d ≠ 0) (hδ : δ ≠ 0) (hδ' : δ' ≠ 0)
    (h1 : δ ≠ d⁻¹) (h2 : δ' ≠ d⁻¹) (h3 : δ' ≠ δ) : δ' = d * δ ^ 2 := by
  have hK := h.card_K_ch625
  have ha : d⁻¹ ≠ 0 := inv_ne_zero hd
  have hc : d * δ ^ 2 ≠ 0 := mul_ne_zero hd (pow_ne_zero 2 hδ)
  have hac : d⁻¹ ≠ d * δ ^ 2 := by
    intro hh
    apply h1
    have e1 : (d * δ) ^ 2 = 1 := by
      have := congrArg (d * ·) hh
      rw [mul_inv_cancel₀ hd] at this
      rw [mul_pow]
      linear_combination -this
    have e2 : d * δ = 1 := by
      have := sq_sq_ch625 hK (d * δ)
      rw [e1, one_pow] at this
      exact this.symm
    exact eq_inv_of_mul_eq_one_right e2
  have hbc : δ ≠ d * δ ^ 2 := fun hh => h1 (eq_inv_of_mul_sq_eq_ch625 hδ hh.symm)
  rcases eq_of_three_ch625 hK ha hδ hc hδ' (Ne.symm h1) hac hbc with e | e | e
  · exact absurd e h2
  · exact absurd e h3
  · exact e

theorem exists_conj_of_type3 (h331 : Stmt3_3_1) (h615 : Stmt6_1_5) {F F' : Subgroup G}
    (hFV : F ≤ V) (hF4 : Nat.card F = 4) (hF'V : F' ≤ V) (hF'4 : Nat.card F' = 4)
    (hFc : ¬ IsCentralType L V F 1) (hFf : ¬ IsFieldType M L V F 1)
    (hF'c : ¬ IsCentralType L V F' 1) (hF'f : ¬ IsFieldType M L V F' 1) :
    ∃ m ∈ ch6MV M V, F' = conjSubgroup F m := by
  obtain ⟨t₀, ht₀T, ht₀⟩ := h.exists_not_lin_T h331 h615
  have ht₀M : t₀ ∈ ch6MV M V := h.T_le_MV_ch625 ht₀T
  set tt : Subgroup.normalizer (V : Set G) := ⟨t₀, ht₀M.2⟩ with htt
  have hd0 : h.det625 tt ≠ 0 := h.det625_ne_zero _ (h.normal ht₀M.1)
  obtain ⟨x, y, hP⟩ := h.isPlane625_of_not_central hFV hF4 hFc
  obtain ⟨x', y', hP'⟩ := h.isPlane625_of_not_central hF'V hF'4 hF'c
  have hne : det2 x y ≠ (h.det625 tt)⁻¹ := fun he =>
    hFf (h.isFieldType_of_det hFV hF4 hP ht₀M ht₀ he)
  have hne' : det2 x' y' ≠ (h.det625 tt)⁻¹ := fun he =>
    hF'f (h.isFieldType_of_det hF'V hF'4 hP' ht₀M ht₀ he)
  by_cases heq : det2 x' y' = det2 x y
  · obtain ⟨l, hlL, hlx, hly⟩ := h.exists_L_basis_ch625 hP'.1 heq.symm
    exact ⟨l, h.L_le_MV_ch625 hlL, h.eq_conjSubgroup_of_isPlane625 hFV hF'V hP hP' l hlx hly⟩
  · have hδ' := h.eq_mul_sq_of_ne_ch625 hd0 hP.1 hP'.1 hne hne' heq
    have hfrob := (h.semilinear_cases_ch625 tt (h.normal ht₀M.1)).resolve_left ht₀
    have hdt : det2 (h.data.conj tt x) (h.data.conj tt y) = det2 x' y' := by
      rw [h.det2_conj_frob_ch625 hfrob, hδ']
      ring
    obtain ⟨l, hlL, hlx, hly⟩ := h.exists_L_basis_ch625 hP'.1 hdt
    refine ⟨((tt⁻¹ * l : Subgroup.normalizer (V : Set G)) : G),
      (ch6MV M V).mul_mem ((ch6MV M V).inv_mem ht₀M) (h.L_le_MV_ch625 hlL), ?_⟩
    exact h.eq_conjSubgroup_of_isPlane625 hFV hF'V hP hP' (tt⁻¹ * l)
      (by rw [h.data.conj_mul, hlx, h.conj_inv_conj_ch625])
      (by rw [h.data.conj_mul, hly, h.conj_inv_conj_ch625])

theorem exists_type3 (h331 : Stmt3_3_1) (h615 : Stmt6_1_5)
    (hidx : (autOn L V).relIndex (autOn (ch6MV M V) V) = 2) :
    ∃ F : Subgroup G, F ≤ V ∧ Nat.card F = 4 ∧ ¬ IsCentralType L V F 1 ∧
      ¬ IsFieldType M L V F 1 := by
  have hK := h.card_K_ch625
  obtain ⟨t₀, ht₀T, ht₀⟩ := h.exists_not_lin_T h331 h615
  have ht₀M : t₀ ∈ ch6MV M V := h.T_le_MV_ch625 ht₀T
  set d := h.det625 ⟨t₀, ht₀M.2⟩ with hd
  obtain ⟨ω, hω0, hω1⟩ := exists_ne_zero_ne_one_ch625 hK
  obtain ⟨c, hc0, hcd⟩ : ∃ c : h.data.K, c ≠ 0 ∧ c ≠ d⁻¹ := by
    by_cases h1 : (1 : h.data.K) = d⁻¹
    · exact ⟨ω, hω0, fun h2 => hω1 (h2.trans h1.symm)⟩
    · exact ⟨1, one_ne_zero, h1⟩
  set x : Fin 2 → h.data.K := ![1, 0] with hx
  set y : Fin 2 → h.data.K := c • ![0, 1] with hy
  have hxy : det2 x y = c := by rw [hy, det2_smul_right_ch625, det2_e_ch625, mul_one]
  have hxy0 : det2 x y ≠ 0 := by rw [hxy]; exact hc0
  set F := h.data.subOf (planeAddSub hK x y) with hF
  have hFV : F ≤ V := h.data.subOf_le _
  have hP : h.IsPlane625 F x y := by
    refine ⟨hxy0, fun w => ?_⟩
    rw [← mem_planeAddSub hK, ← h.data.addSub_subOf (planeAddSub hK x y)]
    exact (h.data.mem_addSub).symm
  have hF4 : Nat.card F = 4 := by
    rw [← h.data.card_addSub hFV, h.data.addSub_subOf, card_planeAddSub hK hxy0]
  refine ⟨F, hFV, hF4, h.not_central_of_isPlane625 hFV hF4 hP, fun hf => ?_⟩
  obtain ⟨t, htM, htN, hlin, hdet⟩ := h.fieldType_det hFV hF4 hf hP
  have := h.det625_eq_of_not_lin hidx htM ht₀M hlin ht₀
  rw [hdet, hxy] at this
  exact hcd (by rw [hd, ← this, inv_inv])

end Hyp6Sec2

end CFSG.Quasithin.H13
