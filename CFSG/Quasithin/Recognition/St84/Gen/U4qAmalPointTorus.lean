module

public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalRoots

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin.H13.U4Par

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

omit [Field K] in
private theorem eq_one_of_mul_self_pt {F : Type} [Field F] [CharP F 2] {x : F}
    (hx : x * x = 1) : x = 1 :=
  CharTwo.sq_inj.mp (by rw [one_pow, sq]; exact hx)

private theorem prod_ix_pt (g : Ix → K) : ∏ a, g a = g ie1 * g ie2 * g if1 * g if2 := by
  simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Finset.univ_eq_empty, Finset.prod_empty,
    one_mul, ie1, ie2, if1, if2]
  ring

private theorem ne_zero_of_diag_pt {d : hypSU h 2 0} {q : Ix → K}
    (hd : ((d : GL Ix K) : Matrix Ix Ix K) = diagonal q) (i : Ix) : q i ≠ 0 :=
  CFSG.RankThree.CentralLiftU.diag_entry_ne_zero h hd i

private theorem exists_sq_eq_of_norm_eq_one {u : K} (hu : u * h.bar u = 1) :
    ∃ s : K, s * s = u ∧ s * h.bar s = 1 := by
  have := h.charP
  have := h.finite
  obtain ⟨s, hs⟩ := isSquare_of_charTwo' u
  refine ⟨s, hs.symm, eq_one_of_mul_self_pt ?_⟩
  calc s * h.bar s * (s * h.bar s) = s * s * h.bar (s * s) := by rw [map_mul]; ring
    _ = 1 := by rw [← hs, hu]

theorem mem_hypTorus_of_diag_u4 {d : hypSU h 2 0} {q : Ix → K}
    (hd : ((d : GL Ix K) : Matrix Ix Ix K) = diagonal q) : d ∈ hypTorus h 2 0 := by
  obtain ⟨-, -, b3, b4⟩ := diag_rel_u4 h hd
  have hdet := (mem_gramSU.mp d.2).2
  rw [hd, det_diagonal, prod_ix_pt] at hdet
  have hr : h.bar (q ie1 * q ie2) = q ie1 * q ie2 := by
    rw [map_mul, b3, b4, ← mul_inv]
    exact (eq_inv_of_mul_eq_one_left (by rw [← hdet]; ring)).symm
  obtain ⟨d', hd'T, q', hd', e1, e2, e3, e4⟩ :=
    exists_mem_hypTorus_u4 h (ne_zero_of_diag_pt h hd ie1) (ne_zero_of_diag_pt h hd ie2) hr
  have hdd : d = d' := by
    apply hypSU_ext h
    rw [hd, hd']
    congr 1
    funext i
    rcases ix_cases i with rfl | rfl | rfl | rfl
    · exact e1.symm
    · exact e2.symm
    · rw [e3, b3, inv_inv]
    · rw [e4, b4, inv_inv]
  rw [hdd]
  exact hd'T

@[expose] noncomputable def u4PtTorus : Subgroup (hypSU h 2 0) where
  carrier := {d | ∃ q : Ix → K, ((d : GL Ix K) : Matrix Ix Ix K) = diagonal q ∧ q ie2 = q if2}
  mul_mem' := by
    rintro d d' ⟨q, hd, hq⟩ ⟨q', hd', hq'⟩
    refine ⟨fun i => q i * q' i, ?_, ?_⟩
    · rw [coe_mul_hypSU, hd, hd', diagonal_mul_diagonal]
    · show q ie2 * q' ie2 = q if2 * q' if2
      rw [hq, hq']
  one_mem' := ⟨fun _ => 1, by rw [diagonal_one]; rfl, rfl⟩
  inv_mem' := by
    rintro d ⟨q, hd, hq⟩
    refine ⟨fun i => (q i)⁻¹, coe_inv_of_diag_u4 h hd, ?_⟩
    show (q ie2)⁻¹ = (q if2)⁻¹
    rw [hq]

theorem u4PtTorus_le_hypTorus : u4PtTorus h ≤ hypTorus h 2 0 := by
  rintro d ⟨q, hd, -⟩
  exact mem_hypTorus_of_diag_u4 h hd

theorem u4PtTorus_le_inf : u4PtTorus h ≤ parP h ⊓ parP2 h :=
  (u4PtTorus_le_hypTorus h).trans (hypTorus_le_inf_u4 h)

theorem u4PtTorus_le_parP : u4PtTorus h ≤ parP h :=
  (u4PtTorus_le_inf h).trans inf_le_left

theorem comm_levHom_of_diag {d : hypSU h 2 0} {q : Ix → K}
    (hd : ((d : GL Ix K) : Matrix Ix Ix K) = diagonal q) (hq : q ie2 = q if2)
    (A : Matrix.SpecialLinearGroup (Fin 2) h.fixedField) : d * levHom h A = levHom h A * d := by
  refine (comm_diag_iff_u4 h hd).mpr fun i j => ?_
  rw [coe_levHom, levMat_apply]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [hq, mul_comm]

theorem comm_levHom_of_mem_u4PtTorus {d : hypSU h 2 0} (hd : d ∈ u4PtTorus h)
    (A : Matrix.SpecialLinearGroup (Fin 2) h.fixedField) : d * levHom h A = levHom h A * d := by
  obtain ⟨q, hdq, hq⟩ := hd
  exact comm_levHom_of_diag h hdq hq A

@[expose] noncomputable def u4PtKappaVal (d : hypSU h 2 0) : K :=
  ((d : GL Ix K) : Matrix Ix Ix K) ie2 ie2 * h.bar (((d : GL Ix K) : Matrix Ix Ix K) ie1 ie1)

theorem u4PtKappaVal_of_diag {d : hypSU h 2 0} {q : Ix → K}
    (hd : ((d : GL Ix K) : Matrix Ix Ix K) = diagonal q) :
    u4PtKappaVal h d = q ie2 * h.bar (q ie1) := by
  rw [u4PtKappaVal, hd, diagonal_apply_eq, diagonal_apply_eq]

theorem coe_conj_sMat_of_diag {d g : hypSU h 2 0} {q : Ix → K}
    (hd : ((d : GL Ix K) : Matrix Ix Ix K) = diagonal q) {x y c : K}
    (hg : ((g : GL Ix K) : Matrix Ix Ix K) = sMat h x y c) :
    (((d * g * d⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) =
      sMat h (q ie2 * (q if1)⁻¹ * x) (q if2 * (q if1)⁻¹ * y) (q ie1 * (q if1)⁻¹ * c) := by
  obtain ⟨b1, b2, b3, b4⟩ := diag_rel_u4 h hd
  have n1 := ne_zero_of_diag_pt h hd ie1
  have n2 := ne_zero_of_diag_pt h hd ie2
  have n3 := ne_zero_of_diag_pt h hd if1
  have n4 := ne_zero_of_diag_pt h hd if2
  rw [coe_mul_hypSU, coe_mul_hypSU, hd, coe_inv_of_diag_u4 h hd, hg]
  ext i j
  rw [mul_diagonal, diagonal_mul]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [sMat_apply, one_apply, map_mul, map_inv₀, b1, b2, b3, b4, n1, n2, n3, n4] <;> ring

theorem coe_conj_sMat_of_mem_u4PtTorus {d g : hypSU h 2 0} (hd : d ∈ u4PtTorus h) {x y c : K}
    (hg : ((g : GL Ix K) : Matrix Ix Ix K) = sMat h x y c) :
    (((d * g * d⁻¹ : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) =
      sMat h (u4PtKappaVal h d * x) (u4PtKappaVal h d * y) (h.norm (u4PtKappaVal h d) * c) := by
  obtain ⟨q, hdq, hq⟩ := hd
  obtain ⟨b1, -, b3, b4⟩ := diag_rel_u4 h hdq
  have n2 := ne_zero_of_diag_pt h hdq ie2
  have n3 := ne_zero_of_diag_pt h hdq if1
  rw [coe_conj_sMat_of_diag h hdq hg, u4PtKappaVal_of_diag h hdq, UnitaryFieldData.norm, b3]
  congr 1
  · rw [hq]
  · rw [map_mul, map_inv₀, b1, b4, inv_inv, ← hq]
    field_simp

theorem u4PtKappaVal_ne_zero {d : hypSU h 2 0} (hd : d ∈ u4PtTorus h) : u4PtKappaVal h d ≠ 0 := by
  obtain ⟨q, hdq, -⟩ := hd
  rw [u4PtKappaVal_of_diag h hdq]
  exact mul_ne_zero (ne_zero_of_diag_pt h hdq ie2)
    ((map_ne_zero h.bar).mpr (ne_zero_of_diag_pt h hdq ie1))

theorem u4PtKappaVal_mul {d d' : hypSU h 2 0} (hd : d ∈ u4PtTorus h) (hd' : d' ∈ u4PtTorus h) :
    u4PtKappaVal h (d * d') = u4PtKappaVal h d * u4PtKappaVal h d' := by
  obtain ⟨q, hdq, -⟩ := hd
  obtain ⟨q', hdq', -⟩ := hd'
  have hm : (((d * d' : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) =
      diagonal fun i => q i * q' i := by
    rw [coe_mul_hypSU, hdq, hdq', diagonal_mul_diagonal]
  rw [u4PtKappaVal_of_diag h hm, u4PtKappaVal_of_diag h hdq, u4PtKappaVal_of_diag h hdq',
    map_mul]
  ring

@[expose] noncomputable def u4PtKappa : u4PtTorus h →* Kˣ where
  toFun d := Units.mk0 (u4PtKappaVal h d) (u4PtKappaVal_ne_zero h d.2)
  map_one' := Units.ext (by simp [u4PtKappaVal])
  map_mul' d d' := Units.ext (u4PtKappaVal_mul h d.2 d'.2)

theorem coe_u4PtKappa (d : u4PtTorus h) : (u4PtKappa h d : K) = u4PtKappaVal h d :=
  rfl

theorem u4PtKappa_injective : Function.Injective (u4PtKappa h) := by
  have := h.charP
  refine (injective_iff_map_eq_one _).mpr ?_
  rintro ⟨d, q, hdq, hq⟩ h1
  have hk : q ie2 * h.bar (q ie1) = 1 := by
    rw [← u4PtKappaVal_of_diag h hdq]
    exact congrArg Units.val h1
  obtain ⟨b1, b2, b3, -⟩ := diag_rel_u4 h hdq
  rw [b3] at hk
  have e2 : q ie2 = q if1 := (mul_inv_eq_one₀ (ne_zero_of_diag_pt h hdq if1)).mp hk
  have e4 : q if2 = q if1 := hq.symm.trans e2
  have e1 : q ie1 = q if1 := by
    have h1' : (q ie1)⁻¹ = (q if1)⁻¹ := by
      rw [← b1, ← e4, b2, hq]
    exact inv_injective h1'
  have hdet := (mem_gramSU.mp d.2).2
  rw [hdq, det_diagonal, prod_ix_pt, e1, e2, e4] at hdet
  have hl : q if1 = 1 := eq_one_of_mul_self_pt (eq_one_of_mul_self_pt (by rw [← hdet]; ring))
  have hq1 : q = fun _ => 1 := by
    funext i
    rcases ix_cases i with rfl | rfl | rfl | rfl
    · rw [e1, hl]
    · rw [e2, hl]
    · exact hl
    · rw [e4, hl]
  exact Subtype.ext (hypSU_ext h (by rw [hdq, hq1, diagonal_one]; rfl))

theorem u4PtKappa_surjective : Function.Surjective (u4PtKappa h) := by
  intro κ
  have hk : (κ : K) ≠ 0 := κ.ne_zero
  have hbk : h.bar (κ : K) ≠ 0 := (map_ne_zero h.bar).mpr hk
  have hu : (κ : K) * (h.bar (κ : K))⁻¹ * h.bar ((κ : K) * (h.bar (κ : K))⁻¹) = 1 := by
    rw [map_mul, map_inv₀, h.bar_bar]
    field_simp
  obtain ⟨s, hsu, hsN⟩ := exists_sq_eq_of_norm_eq_one h hu
  obtain ⟨t, hts, htN⟩ := exists_sq_eq_of_norm_eq_one h hsN
  have ht0 : t ≠ 0 := left_ne_zero_of_mul_eq_one htN
  have hbt : h.bar t = t⁻¹ := eq_inv_of_mul_eq_one_right htN
  have h4 : h.bar (κ : K) * (t * t * (t * t)) = κ := by
    rw [hts, hsu]
    field_simp
  have hr : h.bar (h.bar (κ : K) * t * t) = h.bar (κ : K) * t * t := by
    rw [map_mul, map_mul, h.bar_bar, hbt]
    calc (κ : K) * t⁻¹ * t⁻¹ = h.bar (κ : K) * (t * t * (t * t)) * t⁻¹ * t⁻¹ := by rw [h4]
      _ = h.bar (κ : K) * t * t := by field_simp
  obtain ⟨d, -, q, hdq, e1, e2, -, e4⟩ := exists_mem_hypTorus_u4 h (mul_ne_zero hbk ht0) ht0 hr
  refine ⟨⟨d, q, hdq, by rw [e2, e4, hbt, inv_inv]⟩, Units.ext ?_⟩
  show u4PtKappaVal h d = κ
  rw [u4PtKappaVal_of_diag h hdq, e2, e1, map_mul, h.bar_bar, hbt]
  field_simp

@[expose] noncomputable def u4PtKappaEquiv : u4PtTorus h ≃* Kˣ :=
  MulEquiv.ofBijective (u4PtKappa h) ⟨u4PtKappa_injective h, u4PtKappa_surjective h⟩

theorem coe_u4PtKappaEquiv (d : u4PtTorus h) : (u4PtKappaEquiv h d : K) = u4PtKappaVal h d :=
  rfl

theorem u4PtKappaVal_symm (κ : Kˣ) :
    u4PtKappaVal h (((u4PtKappaEquiv h).symm κ : u4PtTorus h) : hypSU h 2 0) = κ := by
  rw [← coe_u4PtKappaEquiv, MulEquiv.apply_symm_apply]

theorem exists_mem_u4PtTorus_chi_eq {a : K} (ha : a ≠ 0) : ∃ d ∈ u4PtTorus h, chi h d = a := by
  have hba : h.bar a ≠ 0 := (map_ne_zero h.bar).mpr ha
  have hu : h.bar a * a⁻¹ * h.bar (h.bar a * a⁻¹) = 1 := by
    rw [map_mul, map_inv₀, h.bar_bar]
    field_simp
  obtain ⟨s, hsu, hsN⟩ := exists_sq_eq_of_norm_eq_one h hu
  have hs0 : s ≠ 0 := left_ne_zero_of_mul_eq_one hsN
  have hbs : h.bar s = s⁻¹ := eq_inv_of_mul_eq_one_right hsN
  have hr : h.bar (a * s) = a * s := by
    rw [map_mul, hbs]
    calc h.bar a * s⁻¹ = h.bar a * a⁻¹ * a * s⁻¹ := by field_simp
      _ = s * s * a * s⁻¹ := by rw [hsu]
      _ = a * s := by field_simp
  obtain ⟨d, -, q, hdq, e1, e2, -, e4⟩ := exists_mem_hypTorus_u4 h ha hs0 hr
  exact ⟨d, ⟨q, hdq, by rw [e2, e4, hbs, inv_inv]⟩, by rw [chi, hdq, diagonal_apply_eq, e1]⟩

private theorem exists_fixed_ne_zero_ne_one (hm : 2 ≤ m) :
    ∃ c : K, h.bar c = c ∧ c ≠ 0 ∧ c ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective fun c : h.fixedField => decide ((c : K) = 0) := by
    intro a b hab
    by_cases ha : (a : K) = 0
    · have hb : (b : K) = 0 := by simpa [ha] using hab.symm
      exact Subtype.ext (ha.trans hb.symm)
    · have hb : (b : K) ≠ 0 := by simpa [ha] using hab.symm
      exact Subtype.ext ((hcon a ((h.mem_fixedField).mp a.2) ha).trans
        (hcon b ((h.mem_fixedField).mp b.2) hb).symm)
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [h.card_fixedField, Nat.card_eq_fintype_card, Fintype.card_bool] at hle
  have h4 : 4 ≤ 2 ^ m :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  omega

theorem radQ_inf_centralizer_u4PtTorus (hm : 2 ≤ m) :
    radQ h ⊓ Subgroup.centralizer (u4PtTorus h : Set (hypSU h 2 0)) = ⊥ := by
  have := h.charP
  obtain ⟨c, hc, hc0, hc1⟩ := exists_fixed_ne_zero_ne_one h hm
  obtain ⟨⟨d, hd⟩, hdk⟩ := u4PtKappa_surjective h (Units.mk0 c hc0)
  have hκ : u4PtKappaVal h d = c := congrArg Units.val hdk
  have hN : h.norm c ≠ 1 := by
    rw [UnitaryFieldData.norm, hc]
    exact fun e => hc1 (eq_one_of_mul_self_pt e)
  rw [eq_bot_iff]
  rintro g ⟨⟨x, y, z, -, hg⟩, hgC⟩
  have hcomm : d * g * d⁻¹ = g := by
    rw [Subgroup.mem_centralizer_iff.mp hgC d hd, mul_inv_cancel_right]
  have hm' := coe_conj_sMat_of_mem_u4PtTorus h hd hg
  rw [hcomm, hg, hκ] at hm'
  obtain ⟨hx, hy, hz⟩ := sMat_injective h hm'
  have hx0 : x = 0 := by
    have e : (c - 1) * x = 0 := by linear_combination -hx
    exact (mul_eq_zero.mp e).resolve_left (sub_ne_zero.mpr hc1)
  have hy0 : y = 0 := by
    have e : (c - 1) * y = 0 := by linear_combination -hy
    exact (mul_eq_zero.mp e).resolve_left (sub_ne_zero.mpr hc1)
  have hz0 : z = 0 := by
    have e : (h.norm c - 1) * z = 0 := by linear_combination -hz
    exact (mul_eq_zero.mp e).resolve_left (sub_ne_zero.mpr hN)
  rw [Subgroup.mem_bot]
  exact hypSU_ext h (by rw [hg, hx0, hy0, hz0, sMat_zero_u4]; rfl)

end CFSG.Quasithin.F112R.St84

end
