module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitarySublineBasic

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryAutomorphism

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.ShultStronglyClosedTI.TwoCoreGrowth

variable {K : Type} [Field K] {J : HermitianForm 3 K} {C : Subgroup J.specialSubgroup} [C.Normal]

section CharTwo

variable [CharP K 2]

theorem sublineHom_commute_torusHom (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (m : SpecialLinearGroup (Fin 2) (unitaryCoverFixedField J)) (c : normOne J) :
    sublineHom J hJ m * torusHom J hJ c = torusHom J hJ c * sublineHom J hJ m := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_sublineHom, coe_torusHom, coe_diag3]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, mul_comm]

theorem sublineL_commute_torusL (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    ∀ x ∈ sublineL J C hJ, ∀ y ∈ torusL J C hJ, x * y = y * x := by
  rintro _ ⟨m, rfl⟩ _ ⟨c, rfl⟩
  simp only [MonoidHom.coe_comp, Function.comp_apply, ← map_mul,
    sublineHom_commute_torusHom hJ m c]

theorem sublineL_le_centralizer_torusL (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    sublineL J C hJ ≤ Subgroup.centralizer (torusL J C hJ : Set (J.specialSubgroup ⧸ C)) :=
  fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy =>
    (sublineL_commute_torusL hJ x hx y hy).symm

theorem torusL_le_centralizer_sublineL (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    torusL J C hJ ≤ Subgroup.centralizer (sublineL J C hJ : Set (J.specialSubgroup ⧸ C)) :=
  fun y hy => Subgroup.mem_centralizer_iff.mpr fun x hx => sublineL_commute_torusL hJ x hx y hy

theorem pow_three_eq_one_of_pow_six {x : K} (hx : x ^ 6 = 1) : x ^ 3 = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsq : (x ^ 3 - 1) ^ 2 = 0 := by linear_combination hx + (1 - x ^ 3) * h2
  exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq)

theorem sublineL_inf_torusL (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J) : sublineL J C hJ ⊓ torusL J C hJ = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨m, rfl⟩, ⟨c, hc⟩⟩
  obtain ⟨u, hu, -, hu3⟩ := exists_scalar_of_mk_eq hC
    (g := sublineHom J hJ m) (g' := torusHom J hJ c) hc.symm
  rw [coe_sublineHom, coe_torusHom, coe_diag3] at hu
  have e00 := congrFun (congrFun hu 0) 0
  have e02 := congrFun (congrFun hu 0) 2
  have e20 := congrFun (congrFun hu 2) 0
  have e22 := congrFun (congrFun hu 2) 2
  have e11 := congrFun (congrFun hu 1) 1
  simp [Matrix.mul_apply, scalar_apply, diagonal_apply] at e00 e02 e20 e22 e11
  have hc0 : ((c : Kˣ) : K) ≠ 0 := (c : Kˣ).ne_zero
  have hu0 : u ≠ 0 := by
    rw [e11]
    exact inv_ne_zero (pow_ne_zero 2 hc0)
  have hc6 : ((c : Kˣ) : K) ^ 6 = 1 := by
    rw [e11, inv_pow, ← pow_mul] at hu3
    exact inv_eq_one.mp hu3
  have hc3 := pow_three_eq_one_of_pow_six hc6
  have hu' : u = (c : Kˣ) := by
    have hcc : ((c : Kˣ) : K) ^ 2 * (c : Kˣ) = 1 := by rw [← pow_succ]; exact hc3
    rw [e11]
    exact inv_eq_of_mul_eq_one_right hcc
  rw [hu'] at e00 e22
  have h00 : ((m 0 0 : unitaryCoverFixedField J) : K) = 1 :=
    (mul_eq_right₀ hc0).mp e00
  have h22 : ((m 1 1 : unitaryCoverFixedField J) : K) = 1 :=
    (mul_eq_right₀ hc0).mp e22
  have h01 := e02.resolve_right hu0
  have h10 := e20.resolve_right hu0
  have hm : m = 1 := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> apply Subtype.ext <;> simp [h00, h01, h10, h22]
  rw [hm, map_one]
  exact Subgroup.one_mem _

end CharTwo

theorem torusHom_mem_scalarCenter_iff (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (c : normOne J) : torusHom J hJ c ∈ scalarCenter J ↔ ((c : Kˣ) : K) ^ 3 = 1 := by
  have hc0 : ((c : Kˣ) : K) ≠ 0 := (c : Kˣ).ne_zero
  constructor
  · rintro ⟨u, hu, -, -⟩
    rw [coe_torusHom, coe_diag3] at hu
    have e00 := congrFun (congrFun hu 0) 0
    have e11 := congrFun (congrFun hu 1) 1
    simp [scalar_apply] at e00 e11
    rw [← e00] at e11
    field_simp at e11
    linear_combination -e11
  · intro hc3
    refine ⟨(c : Kˣ), ?_, ?_, hc3⟩
    · rw [coe_torusHom, coe_diag3]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [scalar_apply]
      field_simp
      linear_combination -hc3
    · exact c.2

theorem exists_torusHom_eq_of_mem_scalarCenter (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {g : J.specialSubgroup} (hg : g ∈ scalarCenter J) :
    ∃ c : normOne J, torusHom J hJ c = g := by
  obtain ⟨u, hu, hun, hu3⟩ := hg
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hun
  refine ⟨⟨Units.mk0 u hu0, hun⟩, Subtype.ext (Units.ext ?_)⟩
  rw [coe_torusHom, coe_diag3, hu]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scalar_apply]
  field_simp
  linear_combination -hu3

theorem torusHom_injective (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Function.Injective (torusHom J hJ) := by
  intro c d h
  have h' := congrArg (fun g : J.specialSubgroup =>
    ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0) h
  simp only [coe_torusHom, coe_diag3] at h'
  exact Subtype.ext (Units.ext (by simpa using h'))

theorem map_ker_torus_eq (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J) :
    ((QuotientGroup.mk' C).comp (torusHom J hJ)).ker.map (torusHom J hJ) = C := by
  ext g
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact (QuotientGroup.eq_one_iff _).mp hc
  · intro hg
    obtain ⟨c, rfl⟩ := exists_torusHom_eq_of_mem_scalarCenter hJ (hC hg)
    exact ⟨c, (QuotientGroup.eq_one_iff _).mpr hg, rfl⟩

theorem card_torusL_mul_card (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J) :
    Nat.card (torusL J C hJ) * Nat.card C = Nat.card (normOne J) := by
  set φ := (QuotientGroup.mk' C).comp (torusHom J hJ)
  have hker : Nat.card φ.ker = Nat.card C := by
    have h : Nat.card (φ.ker.map (torusHom J hJ)) = Nat.card φ.ker :=
      Subgroup.card_map_of_injective (torusHom_injective hJ)
    rw [map_ker_torus_eq hJ hC] at h
    exact h.symm
  rw [← hker, torusL, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  exact (Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker).symm

variable (J C) in
@[expose] def pairStabilizerL (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J) : Subgroup (J.specialSubgroup ⧸ C) :=
  (MulAction.stabilizer (ProjGenLinGroup (Fin 3) K) (unitaryCoordinatePoint (K := K) 0) ⊓
    MulAction.stabilizer (ProjGenLinGroup (Fin 3) K) (unitaryCoordinatePoint (K := K) 2)).comap
      (coverToPGL J C hJ hC)

theorem mem_pairStabilizerL (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J) (g : J.specialSubgroup) :
    (g : J.specialSubgroup ⧸ C) ∈ pairStabilizerL J C hJ hC ↔
      ProjGenLinGroup.mk (g : GL (Fin 3) K) • unitaryCoordinatePoint (K := K) 0 =
          unitaryCoordinatePoint 0 ∧
        ProjGenLinGroup.mk (g : GL (Fin 3) K) • unitaryCoordinatePoint (K := K) 2 =
          unitaryCoordinatePoint 2 :=
  Iff.rfl

theorem diagonal_of_fix_outer (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {g : J.specialSubgroup}
    (h0 : ProjGenLinGroup.mk (g : GL (Fin 3) K) • unitaryCoordinatePoint (K := K) 0 =
      unitaryCoordinatePoint 0)
    (h2 : ProjGenLinGroup.mk (g : GL (Fin 3) K) • unitaryCoordinatePoint (K := K) 2 =
      unitaryCoordinatePoint 2) :
    ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        !![((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0, 0, 0;
          0, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1, 0;
          0, 0, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2] ∧
      J.conj (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2) *
          ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 ∧
      J.conj (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1) *
          ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1 = 1 ∧
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 *
          ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1 *
          ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
  set A : GL (Fin 3) K := (g : GL (Fin 3) K)
  have hc0 := (unitary_projective_coordinate_maps_iff A 0 0).mp h0
  have hc2 := (unitary_projective_coordinate_maps_iff A 2 2).mp h2
  have h10 := hc0 1 (by decide)
  have h20 := hc0 2 (by decide)
  have h02 := hc2 0 (by decide)
  have h12 := hc2 1 (by decide)
  obtain ⟨h01, h21⟩ := unitary_outer_plane_preserves_middle J hJ A
    (J.specialSubgroup_le_unitarySubgroup g.2) h10 h12
  obtain ⟨hgram, hdet⟩ := (J.mem_specialSubgroup_iff A).mp g.2
  set M : Matrix (Fin 3) (Fin 3) K := (A : Matrix (Fin 3) (Fin 3) K) with hM
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [h10, h20, h01, h21, h02, h12]
  · simpa [hJ, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three, h10, h20,
      h01, h21, h02, h12] using congrArg (fun B => B 2 0) hgram
  · simpa [hJ, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three, h10, h20,
      h01, h21, h02, h12] using congrArg (fun B => B 1 1) hgram
  · have h := congrArg Units.val hdet
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one, Matrix.det_fin_three] at h
    simpa [← hM, h10, h20, h01, h21, h02, h12] using h

theorem torusL_le_pairStabilizerL (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J) : torusL J C hJ ≤ pairStabilizerL J C hJ hC := by
  rintro _ ⟨c, rfl⟩
  refine (mem_pairStabilizerL hJ hC _).mpr ⟨?_, ?_⟩ <;>
  · rw [unitary_projective_coordinate_maps_iff]
    intro k hk
    rw [coe_torusHom, coe_diag3]
    fin_cases k <;> simp_all

section CharTwo

variable [CharP K 2]

theorem pairStabilizerL_inf_centralizer (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J) :
    pairStabilizerL J C hJ hC ⊓
        Subgroup.centralizer (upperRootL J C hJ : Set (J.specialSubgroup ⧸ C)) =
      torusL J C hJ := by
  apply le_antisymm
  · rintro x ⟨hx, hxc⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective C x
    obtain ⟨h0, h2⟩ := (mem_pairStabilizerL hJ hC g).mp hx
    obtain ⟨hdiag, hn02, hn11, hdet⟩ := diagonal_of_fix_outer hJ h0 h2
    set M : Matrix (Fin 3) (Fin 3) K := ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hM
    set Q := sublineHom J hJ (upperSL _ (Multiplicative.ofAdd 1))
    have hQ : (Q : J.specialSubgroup ⧸ C) ∈ upperRootL J C hJ :=
      ⟨Multiplicative.ofAdd 1, rfl⟩
    have hcomm : ((g * Q : J.specialSubgroup) : J.specialSubgroup ⧸ C) =
        ((Q * g : J.specialSubgroup) : J.specialSubgroup ⧸ C) := by
      have := Subgroup.mem_centralizer_iff.mp hxc _ hQ
      simpa only [QuotientGroup.mk'_apply, QuotientGroup.mk_mul] using this.symm
    obtain ⟨u, hu, -, -⟩ := exists_scalar_of_mk_eq hC hcomm
    simp only [Subgroup.coe_mul, Units.val_mul] at hu
    rw [coe_sublineHom_upperSL, ← hM, hdiag] at hu
    have e11 := congrFun (congrFun hu 1) 1
    have e02 := congrFun (congrFun hu 0) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, scalar_apply, diagonal_apply] at e11 e02
    have h11 : M 1 1 ≠ 0 := by
      rintro h
      simp [h] at hn11
    have hu1 : u = 1 := by
      have := e11
      rw [mul_comm, mul_eq_right₀ h11] at this
      exact this
    rw [hu1, mul_one] at e02
    have hs : M 0 0 ≠ 0 := by
      rintro h
      simp [h] at hdet
    have hnorm : M 0 0 * J.conj (M 0 0) = 1 := by
      rw [e02, mul_comm] at hn02
      rw [e02]
      exact hn02
    let s : Kˣ := Units.mk0 (M 0 0) hs
    have hsM : s ∈ normOne J := hnorm
    refine ⟨⟨s, hsM⟩, ?_⟩
    change (torusHom J hJ ⟨s, hsM⟩ : J.specialSubgroup ⧸ C) = (g : J.specialSubgroup ⧸ C)
    congr 1
    apply Subtype.ext
    apply Units.ext
    rw [coe_torusHom, coe_diag3, ← hM, hdiag]
    have h11' : M 1 1 = (M 0 0 ^ 2)⁻¹ := by
      rw [← e02] at hdet
      field_simp
      linear_combination hdet
    ext i j
    fin_cases i <;> fin_cases j <;> simp [s, h11', e02]
  · refine le_inf (torusL_le_pairStabilizerL hJ hC) ?_
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact sublineL_commute_torusL hJ x (upperRootL_le_sublineL hJ hx) y hy

end CharTwo

end CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
