module

public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalPointTorus

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin.H13.U4Par

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

omit [Field K] in
private theorem le_normalizer_of_conj_pt {G : Type*} [Group G] {H S : Subgroup G}
    (hS : ∀ d ∈ H, ∀ g ∈ S, d * g * d⁻¹ ∈ S) : H ≤ Subgroup.normalizer (S : Set G) := by
  intro d hd
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨hS d hd g, fun hg => ?_⟩
  have := hS d⁻¹ (H.inv_mem hd) _ hg
  simpa [mul_assoc] using this

private def ixFinPt : Ix ≃ Fin 4 where
  toFun a := if a = ie1 then 0 else if a = ie2 then 1 else if a = if1 then 2 else 3
  invFun i := ![ie1, ie2, if1, if2] i
  left_inv a := by rcases ix_cases a with rfl | rfl | rfl | rfl <;> decide
  right_inv i := by fin_cases i <;> decide

omit [Field K] in
private theorem det_fin_four_pt {R : Type*} [CommRing R] (M : Matrix (Fin 4) (Fin 4) R) :
    M.det = M 0 0 * (M 1 1 * (M 2 2 * M 3 3 - M 2 3 * M 3 2) -
        M 1 2 * (M 2 1 * M 3 3 - M 2 3 * M 3 1) + M 1 3 * (M 2 1 * M 3 2 - M 2 2 * M 3 1)) -
      M 0 1 * (M 1 0 * (M 2 2 * M 3 3 - M 2 3 * M 3 2) -
        M 1 2 * (M 2 0 * M 3 3 - M 2 3 * M 3 0) + M 1 3 * (M 2 0 * M 3 2 - M 2 2 * M 3 0)) +
      M 0 2 * (M 1 0 * (M 2 1 * M 3 3 - M 2 3 * M 3 1) -
        M 1 1 * (M 2 0 * M 3 3 - M 2 3 * M 3 0) + M 1 3 * (M 2 0 * M 3 1 - M 2 1 * M 3 0)) -
      M 0 3 * (M 1 0 * (M 2 1 * M 3 2 - M 2 2 * M 3 1) -
        M 1 1 * (M 2 0 * M 3 2 - M 2 2 * M 3 0) + M 1 2 * (M 2 0 * M 3 1 - M 2 1 * M 3 0)) := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_one]
  simp only [Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove, Fin.castSucc, Fin.succ]
  simp
  ring

private theorem det_of_col_row_pt (G : Matrix Ix Ix K) (hc : ∀ a, a ≠ ie1 → G a ie1 = 0)
    (hr : ∀ b, b ≠ if1 → G if1 b = 0) :
    G.det = G ie1 ie1 * (G ie2 ie2 * G if2 if2 - G ie2 if2 * G if2 ie2) * G if1 if1 := by
  have c2 := hc ie2 ie2_ne_ie1
  have c3 := hc if1 if1_ne_ie1
  have c4 := hc if2 if2_ne_ie1
  have r2 := hr ie2 ie2_ne_if1
  have r4 := hr if2 if2_ne_if1
  have e0 : ixFinPt.symm 0 = ie1 := rfl
  have e1 : ixFinPt.symm 1 = ie2 := rfl
  have e2 : ixFinPt.symm 2 = if1 := rfl
  have e3 : ixFinPt.symm 3 = if2 := rfl
  rw [← det_reindex_self ixFinPt G, det_fin_four_pt]
  simp only [reindex_apply, submatrix_apply, e0, e1, e2, e3, c2, c3, c4, r2, r4]
  ring

theorem chi_mul_det_rho_mul_of_mem_parP {g : hypSU h 2 0} (hg : g ∈ parP h) :
    chi h g * (rho h g).det * ((g : GL Ix K) : Matrix Ix Ix K) if1 if1 = 1 := by
  have hcol := (mem_parP_iff h g).mp hg
  rw [← (mem_gramSU.mp g.2).2, det_of_col_row_pt _ hcol (row_if1_of_col h g hcol).1, chi, rho,
    det_fin_two_of]

theorem mem_parH_of_chi_eq_one {g : hypSU h 2 0} (hg : g ∈ parP h) (hchi : chi h g = 1) :
    g ∈ parH h := by
  refine ⟨hg, hchi, ?_⟩
  have hd := chi_mul_det_rho_mul_of_mem_parP h hg
  have hff := (row_if1_of_col h g ((mem_parP_iff h g).mp hg)).2
  have hchi' : ((g : GL Ix K) : Matrix Ix Ix K) ie1 ie1 = 1 := hchi
  rw [hchi', map_one, one_mul] at hff
  rw [hchi, hff, one_mul, mul_one] at hd
  exact hd

private theorem chi_levHom (A : Matrix.SpecialLinearGroup (Fin 2) h.fixedField) :
    chi h (levHom h A) = 1 := by
  simp [chi, coe_levHom, levMat_apply]

theorem levHom_injective_u4 : Function.Injective (levHom h) := by
  intro A B hAB
  have e := congrArg (rho h) hAB
  rw [rho_levHom, rho_levHom] at e
  exact Subtype.ext (Matrix.map_injective h.fixedField.subtype_injective e)

theorem radQ_le_parH : radQ h ≤ parH h := by
  intro g hg
  obtain ⟨hchi, hrho⟩ := chi_rho_of_mem_radQ h hg
  exact ⟨radQ_le_parP h hg, hchi, by rw [hrho, det_one]⟩

theorem exists_eq_mul_levHom_of_mem_parH {g : hypSU h 2 0} (hg : g ∈ parH h) :
    ∃ r ∈ radQ h, r * levHom h (rhoF h ⟨g, hg⟩) = g := by
  have hgP : g ∈ parP h := parH_le_parP h hg
  have hlP : (levHom h (rhoF h ⟨g, hg⟩))⁻¹ ∈ parP h :=
    (parP h).inv_mem (levHom_le_parP h ⟨_, rfl⟩)
  have hρ : rho h g = slMat h (rhoF h ⟨g, hg⟩) := (map_rhoFMat h ⟨g, hg⟩).symm
  refine ⟨g * (levHom h (rhoF h ⟨g, hg⟩))⁻¹,
    mem_radQ_of_chi_rho h ((parP h).mul_mem hgP hlP) ?_ ?_, inv_mul_cancel_right g _⟩
  · rw [chi_mul h hlP, ← map_inv, chi_levHom, hg.2.1, one_mul]
  · rw [rho_mul h hgP hlP, ← map_inv, rho_levHom, hρ, ← slMat_mul, mul_inv_cancel, slMat_one]

theorem radQ_sup_levHom_range_eq_parH : radQ h ⊔ (levHom h).range = parH h := by
  refine le_antisymm (sup_le (radQ_le_parH h) (levHom_range_le_parH h)) fun g hg => ?_
  obtain ⟨r, hr, e⟩ := exists_eq_mul_levHom_of_mem_parH h hg
  rw [← e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hr) (Subgroup.mem_sup_right ⟨_, rfl⟩)

theorem levHom_range_inf_radQ : (levHom h).range ⊓ radQ h = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨⟨A, rfl⟩, hA⟩
  have h1 : slMat h A = 1 := by rw [← rho_levHom, (chi_rho_of_mem_radQ h hA).2]
  rw [Subgroup.mem_bot]
  exact hypSU_ext h (by rw [coe_levHom, h1, levMat_one]; rfl)

theorem u4PtTorus_inf_parH : u4PtTorus h ⊓ parH h = ⊥ := by
  have := h.charP
  rw [eq_bot_iff]
  rintro d ⟨⟨q, hdq, hq⟩, -, hchi, hdet⟩
  have e1 : q ie1 = 1 := by rw [← hchi, chi, hdq, diagonal_apply_eq]
  have h22 : q ie2 * q ie2 = 1 := by
    simp only [rho, det_fin_two_of, hdq] at hdet
    simpa [hq] using hdet
  have e2 : q ie2 = 1 := CharTwo.sq_inj.mp (by rw [one_pow, sq]; exact h22)
  obtain ⟨-, -, b3, -⟩ := diag_rel_u4 h hdq
  have e3 : q if1 = 1 := by
    rw [e1, map_one] at b3
    exact inv_eq_one.mp b3.symm
  have hq1 : q = fun _ => 1 := by
    funext i
    rcases ix_cases i with rfl | rfl | rfl | rfl
    · exact e1
    · exact e2
    · exact e3
    · rw [← hq, e2]
  rw [Subgroup.mem_bot]
  exact hypSU_ext h (by rw [hdq, hq1, diagonal_one]; rfl)

theorem levHom_range_inf_u4PtTorus : (levHom h).range ⊓ u4PtTorus h = ⊥ :=
  eq_bot_iff.mpr fun _ hx => (u4PtTorus_inf_parH h).le ⟨hx.2, levHom_range_le_parH h hx.1⟩

theorem exists_mem_parH_mul_of_mem_parP {g : hypSU h 2 0} (hg : g ∈ parP h) :
    ∃ d ∈ u4PtTorus h, g * d⁻¹ ∈ parH h := by
  have ha : chi h g ≠ 0 := (map_ne_zero h.bar).mp
    (left_ne_zero_of_mul_eq_one (row_if1_of_col h g ((mem_parP_iff h g).mp hg)).2)
  obtain ⟨d, hd, hdchi⟩ := exists_mem_u4PtTorus_chi_eq h ha
  have hdP := u4PtTorus_le_parP h hd
  have hdi : d⁻¹ ∈ parP h := (parP h).inv_mem hdP
  refine ⟨d, hd, mem_parH_of_chi_eq_one h ((parP h).mul_mem hg hdi) ?_⟩
  rw [chi_mul h hdi, ← hdchi, chi_mul_inv h hdP]

theorem radQ_sup_levHom_range_sup_u4PtTorus :
    radQ h ⊔ (levHom h).range ⊔ u4PtTorus h = parP h := by
  refine le_antisymm (sup_le (sup_le (radQ_le_parP h) (levHom_le_parP h)) (u4PtTorus_le_parP h))
    fun g hg => ?_
  obtain ⟨d, hd, hgd⟩ := exists_mem_parH_mul_of_mem_parP h hg
  rw [← radQ_sup_levHom_range_eq_parH] at hgd
  have e : g = g * d⁻¹ * d := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hgd) (Subgroup.mem_sup_right hd)

theorem exists_eq_mul_levHom_mul_of_mem_parP {g : hypSU h 2 0} (hg : g ∈ parP h) :
    ∃ r ∈ radQ h, ∃ A : Matrix.SpecialLinearGroup (Fin 2) h.fixedField, ∃ d ∈ u4PtTorus h,
      g = r * levHom h A * d := by
  obtain ⟨d, hd, hgd⟩ := exists_mem_parH_mul_of_mem_parP h hg
  obtain ⟨r, hr, e⟩ := exists_eq_mul_levHom_of_mem_parH h hgd
  refine ⟨r, hr, rhoF h ⟨g * d⁻¹, hgd⟩, d, hd, ?_⟩
  rw [e]
  group

theorem eq_of_mul_levHom_mul_eq {r r' d d' : hypSU h 2 0} (hr : r ∈ radQ h) (hr' : r' ∈ radQ h)
    (hd : d ∈ u4PtTorus h) (hd' : d' ∈ u4PtTorus h)
    {A A' : Matrix.SpecialLinearGroup (Fin 2) h.fixedField}
    (he : r * levHom h A * d = r' * levHom h A' * d') : r = r' ∧ A = A' ∧ d = d' := by
  have hH : ∀ {s : hypSU h 2 0}, s ∈ radQ h →
      ∀ B : Matrix.SpecialLinearGroup (Fin 2) h.fixedField, s * levHom h B ∈ parH h :=
    fun hs B => (parH h).mul_mem (radQ_le_parH h hs) (levHom_range_le_parH h ⟨B, rfl⟩)
  have hdd : (r' * levHom h A')⁻¹ * (r * levHom h A) = d' * d⁻¹ := by
    calc (r' * levHom h A')⁻¹ * (r * levHom h A)
        = (r' * levHom h A')⁻¹ * (r * levHom h A * d) * d⁻¹ := by group
      _ = (r' * levHom h A')⁻¹ * (r' * levHom h A' * d') * d⁻¹ := by rw [he]
      _ = d' * d⁻¹ := by group
  have h1 : d' * d⁻¹ ∈ u4PtTorus h ⊓ parH h := by
    refine ⟨(u4PtTorus h).mul_mem hd' ((u4PtTorus h).inv_mem hd), ?_⟩
    rw [← hdd]
    exact (parH h).mul_mem ((parH h).inv_mem (hH hr' A')) (hH hr A)
  rw [u4PtTorus_inf_parH, Subgroup.mem_bot, mul_inv_eq_one] at h1
  subst h1
  have he' : r * levHom h A = r' * levHom h A' := mul_right_cancel he
  have h2 : r'⁻¹ * r = levHom h A' * (levHom h A)⁻¹ := by
    calc r'⁻¹ * r = r'⁻¹ * (r * levHom h A) * (levHom h A)⁻¹ := by group
      _ = r'⁻¹ * (r' * levHom h A') * (levHom h A)⁻¹ := by rw [he']
      _ = levHom h A' * (levHom h A)⁻¹ := by group
  have h3 : r'⁻¹ * r ∈ (levHom h).range ⊓ radQ h := by
    refine ⟨?_, (radQ h).mul_mem ((radQ h).inv_mem hr') hr⟩
    rw [h2]
    exact ⟨A' * A⁻¹, by rw [map_mul, map_inv]⟩
  rw [levHom_range_inf_radQ, Subgroup.mem_bot, inv_mul_eq_one] at h3
  subst h3
  exact ⟨rfl, levHom_injective_u4 h (mul_left_cancel he'), rfl⟩

theorem eq_one_of_levHom_mul_mem_radQ {A : Matrix.SpecialLinearGroup (Fin 2) h.fixedField}
    {d : hypSU h 2 0} (hd : d ∈ u4PtTorus h) (hQ : levHom h A * d ∈ radQ h) : A = 1 ∧ d = 1 := by
  have e : (1 : hypSU h 2 0) * levHom h A * d = (levHom h A * d) * levHom h 1 * 1 := by
    rw [map_one]
    group
  obtain ⟨-, hA, hd1⟩ :=
    eq_of_mul_levHom_mul_eq h (radQ h).one_mem hQ hd (u4PtTorus h).one_mem e
  exact ⟨hA, hd1⟩

theorem u4PtTorus_le_normalizer_levHom_range :
    u4PtTorus h ≤ Subgroup.normalizer ((levHom h).range : Set (hypSU h 2 0)) := by
  refine le_normalizer_of_conj_pt fun d hd g hg => ?_
  obtain ⟨A, rfl⟩ := hg
  refine ⟨A, ?_⟩
  rw [comm_levHom_of_mem_u4PtTorus h hd A, mul_inv_cancel_right]

@[expose] noncomputable def u4PtLevTorusHom :
    Matrix.SpecialLinearGroup (Fin 2) h.fixedField × Kˣ →* hypSU h 2 0 :=
  (levHom h).noncommCoprod ((u4PtTorus h).subtype.comp (u4PtKappaEquiv h).symm.toMonoidHom)
    fun A κ => (comm_levHom_of_mem_u4PtTorus h ((u4PtKappaEquiv h).symm κ).2 A).symm

theorem u4PtLevTorusHom_apply (A : Matrix.SpecialLinearGroup (Fin 2) h.fixedField) (κ : Kˣ) :
    u4PtLevTorusHom h (A, κ) = levHom h A * ((u4PtKappaEquiv h).symm κ : hypSU h 2 0) :=
  rfl

theorem u4PtLevTorusHom_injective : Function.Injective (u4PtLevTorusHom h) := by
  refine (injective_iff_map_eq_one _).mpr ?_
  rintro ⟨A, κ⟩ h1
  rw [u4PtLevTorusHom_apply] at h1
  have hA : levHom h A ∈ (levHom h).range ⊓ u4PtTorus h := by
    refine ⟨⟨A, rfl⟩, ?_⟩
    rw [eq_inv_of_mul_eq_one_left h1]
    exact (u4PtTorus h).inv_mem ((u4PtKappaEquiv h).symm κ).2
  rw [levHom_range_inf_u4PtTorus, Subgroup.mem_bot] at hA
  rw [hA, one_mul] at h1
  have hd : (u4PtKappaEquiv h).symm κ = 1 := Subtype.ext h1
  exact Prod.ext (levHom_injective_u4 h (hA.trans (map_one (levHom h)).symm))
    ((u4PtKappaEquiv h).symm.injective (hd.trans (map_one (u4PtKappaEquiv h).symm).symm))

theorem u4PtLevTorusHom_range :
    (u4PtLevTorusHom h).range = (levHom h).range ⊔ u4PtTorus h := by
  refine le_antisymm ?_ fun g hg => ?_
  · rintro _ ⟨⟨A, κ⟩, rfl⟩
    rw [u4PtLevTorusHom_apply]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨A, rfl⟩)
      (Subgroup.mem_sup_right ((u4PtKappaEquiv h).symm κ).2)
  · have hmem : g ∈ (((levHom h).range ⊔ u4PtTorus h : Subgroup (hypSU h 2 0)) :
        Set (hypSU h 2 0)) := hg
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
      (u4PtTorus_le_normalizer_levHom_range h)] at hmem
    obtain ⟨_, ⟨A, rfl⟩, d, hd, rfl⟩ := Set.mem_mul.mp hmem
    refine ⟨(A, u4PtKappaEquiv h ⟨d, hd⟩), ?_⟩
    rw [u4PtLevTorusHom_apply, MulEquiv.symm_apply_apply]

@[expose] noncomputable def u4PtLevTorusEquiv :
    Matrix.SpecialLinearGroup (Fin 2) h.fixedField × Kˣ ≃* ↥((levHom h).range ⊔ u4PtTorus h) :=
  (MonoidHom.ofInjective (u4PtLevTorusHom_injective h)).trans
    (MulEquiv.subgroupCongr (u4PtLevTorusHom_range h))

theorem radQ_inf_levHom_range_sup_u4PtTorus :
    radQ h ⊓ ((levHom h).range ⊔ u4PtTorus h) = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hgQ, hgL⟩
  rw [← u4PtLevTorusHom_range] at hgL
  obtain ⟨⟨A, κ⟩, rfl⟩ := hgL
  rw [u4PtLevTorusHom_apply] at hgQ
  obtain ⟨rfl, hd⟩ := eq_one_of_levHom_mul_mem_radQ h ((u4PtKappaEquiv h).symm κ).2 hgQ
  rw [Subgroup.mem_bot, u4PtLevTorusHom_apply, hd, map_one, one_mul]

theorem radQ_semidirect_levHom_range_sup_u4PtTorus :
    (levHom h).range ⊔ u4PtTorus h ≤ Subgroup.normalizer (radQ h : Set (hypSU h 2 0)) ∧
      Disjoint (radQ h) ((levHom h).range ⊔ u4PtTorus h) ∧
      radQ h ⊔ ((levHom h).range ⊔ u4PtTorus h) = parP h :=
  ⟨(sup_le (levHom_le_parP h) (u4PtTorus_le_parP h)).trans (parP_le_normalizer_radQ h),
    disjoint_iff.mpr (radQ_inf_levHom_range_sup_u4PtTorus h),
    by rw [← sup_assoc, radQ_sup_levHom_range_sup_u4PtTorus]⟩

end CFSG.Quasithin.F112R.St84

end
