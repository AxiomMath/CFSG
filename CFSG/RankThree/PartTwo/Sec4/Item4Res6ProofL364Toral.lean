module

public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofL364Gen
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofL364Sylow

public section

namespace CFSG.RankThree.PartTwo.Sec4.Res6L364

open CFSG CFSG.LieType.Seitz CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix

@[expose] noncomputable def slι (M : Matrix (Fin 3) (Fin 3) F4) (h : M.det = 1) :
    SpecialLinearGroup (Fin 3) K64 :=
  ⟨M.map ι, by rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_one]⟩

theorem coe_slι (M : Matrix (Fin 3) (Fin 3) F4) (h : M.det = 1) :
    ((slι M h : SpecialLinearGroup (Fin 3) K64) : Matrix (Fin 3) (Fin 3) K64) = M.map ι := rfl

theorem slι_mul (M N : Matrix (Fin 3) (Fin 3) F4) (hM : M.det = 1) (hN : N.det = 1) :
    slι (M * N) (by rw [Matrix.det_mul, hM, hN, one_mul]) = slι M hM * slι N hN := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_slι, coe_slι, coe_slι, Matrix.map_mul]

theorem fieldAut_proj_slι (M : Matrix (Fin 3) (Fin 3) F4) (h : M.det = 1) :
    fieldAut 3 K64 σ4 (proj 3 K64 (slι M h)) = proj 3 K64 (slι M h) := by
  rw [fieldAut_proj]
  congr 1
  apply Subtype.ext
  ext a b
  change σ4 (ι (M a b)) = ι (M a b)
  exact σ4_ι _

theorem proj_scalar_mul (l : F4) (hl : l ≠ 0) (X : SpecialLinearGroup (Fin 3) K64)
    (Y : SpecialLinearGroup (Fin 3) K64)
    (hXY : (X : Matrix (Fin 3) (Fin 3) K64) = ι l • (Y : Matrix (Fin 3) (Fin 3) K64)) :
    proj 3 K64 X = proj 3 K64 Y := by
  have hl0 : ι l ≠ 0 := (map_ne_zero ι).mpr hl
  have hl3 : (Units.mk0 (ι l) hl0) ^ 3 = 1 := Units.ext (by simpa using ι_pow_three hl)
  have hX : X = scalarElement (Units.mk0 (ι l) hl0) hl3 * Y := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_scalarElement, hXY, Units.val_mk0,
      Matrix.scalar_apply, smul_eq_diagonal_mul]
  rw [hX, map_mul, (proj_eq_one_iff).mpr (scalarElement_mem_scalars _ _), one_mul]

theorem ρ_proj_slι {y : Lab} {M : Matrix (Fin 3) (Fin 3) F4} (h : M.det = 1) {l : F4}
    (hl : l ≠ 0) (hM : M * L y = l • (L y * M)) :
    ρ y (proj 3 K64 (slι M h)) = proj 3 K64 (slι M h) := by
  rw [ρ, conjAut_proj]
  refine proj_scalar_mul l⁻¹ (inv_ne_zero hl) _ _ ?_
  rw [coe_slConjugation, coe_slι, coe_glι, coe_LGL]
  have hinv : (((glι (LGL y))⁻¹ : GL (Fin 3) K64) : Matrix (Fin 3) (Fin 3) K64) =
      (((LGL y)⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4).map ι := by
    rw [← map_inv, coe_glι]
  rw [hinv]
  have key : L y * M * (((LGL y)⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) = l⁻¹ • M := by
    have h1 : M * L y * (((LGL y)⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) = M := by
      rw [Matrix.mul_assoc, ← coe_LGL, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.mul_one]
    rw [hM, Matrix.smul_mul] at h1
    calc L y * M * (((LGL y)⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4)
        = l⁻¹ • (l • (L y * M * (((LGL y)⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4))) := by
          rw [smul_smul, inv_mul_cancel₀ hl, one_smul]
      _ = l⁻¹ • M := by rw [h1]
  rw [← Matrix.map_mul, ← Matrix.map_mul, key]
  ext a b
  simp [map_mul]

theorem fieldAut_σ4_not_mem : fieldAut 3 K64 σ4 ∉ linearAutGroup 3 K64 := by
  intro h
  rw [linearAutGroup_three_eq_range] at h
  obtain ⟨A, hA⟩ := h
  have h1 : conjAut 3 K64 A⁻¹ * fieldAut 3 K64 σ4 = 1 := by
    rw [← hA, ← map_mul, inv_mul_cancel, map_one]
  exact σ4_ne_one (eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num) _ _ h1).1

theorem ρ_mem (y : Lab) : ρ y ∈ linearAutGroup 3 K64 := conjAut_mem_linearAutGroup _

theorem ρ_ne_one {y : Lab} (hy : y ≠ (0, 0, 0)) : ρ y ≠ 1 := by
  intro h
  exact hy (ρ_injective (h.trans ρ_zero.symm))

theorem mem_H_of_fixed {E : Subgroup (MulAut Y64)} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (h27 : Nat.card E = 27) {a b : MulAut Y64} (ha : a ∈ E) (hb : b ∈ E)
    (haD : a ∈ linearAutGroup 3 K64) (ha1 : a ≠ 1) (hbD : b ∉ linearAutGroup 3 K64) {x : Y64}
    (hax : a x = x) (hbx : b x = x) : x ∈ seitzHyperGamma 3 E := by
  refine mem_seitzHyperGamma_of_pair hE h27 ha hb ha1 ?_ hax hbx
  intro hz
  exact hbD (Subgroup.zpowers_le.mpr haD hz)

theorem eq_of_mem_zpowers_of_pow_three {G : Type*} [Group G] {a x : G} (ha : a ^ 3 = 1)
    (hx : x ∈ Subgroup.zpowers a) : x = 1 ∨ x = a ∨ x = a * a := by
  have hfin : IsOfFinOrder a := isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, ha⟩
  obtain ⟨n, rfl⟩ := (hfin.mem_powers_iff_mem_zpowers).mpr hx
  show a ^ n = 1 ∨ a ^ n = a ∨ a ^ n = a * a
  rw [pow_eq_pow_mod n ha]
  have h3 : n % 3 < 3 := Nat.mod_lt n (by norm_num)
  interval_cases (n % 3)
  · left; simp
  · right; left; simp
  · right; right; rw [pow_two]

@[expose] def t3Lab : Lab := (1, 1, 0)

theorem mulLab_t1_t2 : (mulLab t1Lab t2Lab).1 = t3Lab := by decide

theorem tv_comm_t (c : F4) :
    (Matrix.transvection 0 1 c * L t1Lab = (1 : F4) • (L t1Lab * Matrix.transvection 0 1 c)) ∧
    (Matrix.transvection 1 0 c * L t1Lab = (1 : F4) • (L t1Lab * Matrix.transvection 1 0 c)) ∧
    (Matrix.transvection 0 2 c * L t2Lab = (1 : F4) • (L t2Lab * Matrix.transvection 0 2 c)) ∧
    (Matrix.transvection 2 0 c * L t2Lab = (1 : F4) • (L t2Lab * Matrix.transvection 2 0 c)) ∧
    (Matrix.transvection 1 2 c * L t3Lab = (1 : F4) • (L t3Lab * Matrix.transvection 1 2 c)) ∧
    (Matrix.transvection 2 1 c * L t3Lab = (1 : F4) • (L t3Lab * Matrix.transvection 2 1 c)) := by
  revert c
  decide

theorem slι_transvection {i j : Fin 3} (h : i ≠ j) (c : F4) :
    slι (Matrix.transvection i j c) (Matrix.det_transvection_of_ne i j h c) = tv h (ι c) := by
  apply Subtype.ext
  rw [coe_slι, SpecialLinearGroup.transvection_coe]
  ext a b
  simp only [Matrix.map_apply, Matrix.transvection, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  split_ifs <;> simp_all

@[expose] noncomputable def diagSL3 (d : Fin 3 → K64) (h : d 0 * d 1 * d 2 = 1) :
    SpecialLinearGroup (Fin 3) K64 :=
  ⟨diagonal d, by rw [det_diagonal, Fin.prod_univ_three, h]⟩

theorem ρ_proj_diag {i j : Fin 3} (d : Fin 3 → K64) (h : d 0 * d 1 * d 2 = 1) :
    ρ (i, j, 0) (proj 3 K64 (diagSL3 d h)) = proj 3 K64 (diagSL3 d h) := by
  rw [ρ, conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation]
  have hL : ((glι (LGL (i, j, 0)) : GL (Fin 3) K64) : Matrix (Fin 3) (Fin 3) K64) =
      diagonal (fun k => ι (![1, ω4 ^ (i : ℕ), ω4 ^ (j : ℕ)] k)) := by
    rw [coe_glι, coe_LGL]
    simp only [L, dM]
    ext a b
    simp [Matrix.diagonal_apply]
    split_ifs <;> simp
  have hc : Commute ((glι (LGL (i, j, 0)) : GL (Fin 3) K64) : Matrix (Fin 3) (Fin 3) K64)
      ((diagSL3 d h : SpecialLinearGroup (Fin 3) K64) : Matrix (Fin 3) (Fin 3) K64) := by
    rw [hL]
    exact Matrix.commute_diagonal _ _
  rw [hc.eq, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem seitzHyperGamma_eq_top_toral {E : Subgroup (MulAut Y64)}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (h27 : Nat.card E = 27)
    (hf : fieldAut 3 K64 σ4 ∈ E) (h1 : ρ t1Lab ∈ E) (h2 : ρ t2Lab ∈ E) :
    seitzHyperGamma 3 E = ⊤ := by
  set H := (seitzHyperGamma 3 E).comap (proj 3 K64) with hH
  have h3 : ρ t3Lab ∈ E := by rw [← mulLab_t1_t2, ← ρ_mul]; exact E.mul_mem h1 h2
  have hdiag : ∀ (d : Fin 3 → K64) (h : d 0 * d 1 * d 2 = 1), diagSL3 d h ∈ H := by
    intro d h
    refine mem_seitzHyperGamma_of_pair hE h27 h1 h2 (ρ_ne_one (by decide)) ?_
      (ρ_proj_diag d h) (ρ_proj_diag d h)
    intro hz
    rcases eq_of_mem_zpowers_of_pow_three (hE.2 _ h1) hz with h0 | h0 | h0
    · exact absurd (h0.trans ρ_zero.symm) (fun e => by have := ρ_injective e; revert this; decide)
    · exact absurd (ρ_injective h0) (by decide)
    · rw [ρ_mul] at h0; exact absurd (ρ_injective h0) (by decide)
  have hroot : ∀ (y : Lab) (i j : Fin 3) (h : i ≠ j), ρ y ∈ E → y ≠ (0, 0, 0) →
      (∀ c : F4, Matrix.transvection i j c * L y = (1 : F4) • (L y * Matrix.transvection i j c)) →
      ∀ c : F4, tv h (ι c) ∈ H := by
    intro y i j h hy hy0 hcomm c
    show proj 3 K64 (tv h (ι c)) ∈ seitzHyperGamma 3 E
    rw [← slι_transvection h c]
    exact mem_H_of_fixed hE h27 hy hf (ρ_mem y) (ρ_ne_one hy0) fieldAut_σ4_not_mem
      (ρ_proj_slι _ one_ne_zero (hcomm c)) (fieldAut_proj_slι _ _)
  have c01 := fun c => (tv_comm_t c).1
  have c10 := fun c => (tv_comm_t c).2.1
  have c02 := fun c => (tv_comm_t c).2.2.1
  have c20 := fun c => (tv_comm_t c).2.2.2.1
  have c12 := fun c => (tv_comm_t c).2.2.2.2.1
  have c21 := fun c => (tv_comm_t c).2.2.2.2.2
  have hall : ∀ (i j : Fin 3) (h : i ≠ j), (∀ c : F4, tv h (ι c) ∈ H) → ∀ c : K64, tv h c ∈ H := by
    intro i j h hF4 c
    by_cases hc : c = 0
    · rw [hc, tv_zero]; exact H.one_mem
    set d : Fin 3 → K64 := fun a => if a = i then c else if a = j then 1 else c⁻¹ with hd
    have hdet : d 0 * d 1 * d 2 = 1 := by
      fin_cases i <;> fin_cases j <;> first
        | exact absurd rfl h
        | (simp only [hd]; simp; field_simp)
    have hdj : d j ≠ 0 := by simp [hd, Ne.symm h]
    have e := diag_mul_transvection (D := diagSL3 d hdet) rfl h 1 hdj
    have hdi : d i = c := by simp [hd]
    have hdj' : d j = 1 := by simp [hd, Ne.symm h]
    rw [hdi, hdj', mul_one, div_one] at e
    have h1' : tv h 1 ∈ H := by simpa using hF4 1
    have : tv h c = diagSL3 d hdet * tv h 1 * (diagSL3 d hdet)⁻¹ := by
      rw [e, mul_inv_cancel_right]
    rw [this]
    exact H.mul_mem (H.mul_mem (hdiag _ _) h1') (H.inv_mem (hdiag _ _))
  have hH : H = ⊤ := by
    apply eq_top_of_transvections
    intro i j hij c
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hall _ _ _ (hroot t1Lab 0 1 _ h1 (by decide) c01) c
    · exact hall _ _ _ (hroot t2Lab 0 2 _ h2 (by decide) c02) c
    · exact hall _ _ _ (hroot t1Lab 1 0 _ h1 (by decide) c10) c
    · exact absurd rfl hij
    · exact hall _ _ _ (hroot t3Lab 1 2 _ h3 (by decide) c12) c
    · exact hall _ _ _ (hroot t2Lab 2 0 _ h2 (by decide) c20) c
    · exact hall _ _ _ (hroot t3Lab 2 1 _ h3 (by decide) c21) c
    · exact absurd rfl hij
  rw [eq_top_iff]
  intro x _
  obtain ⟨g, rfl⟩ := proj_surjective 3 K64 x
  have : g ∈ H := by rw [hH]; trivial
  exact this

end CFSG.RankThree.PartTwo.Sec4.Res6L364
