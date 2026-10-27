module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityPairPGL
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityPairCount
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityPairHeis

public section

namespace CFSG.RankThree.PartTwo.Sec19.NF5Pair
open Matrix
open scoped MatrixGroups

variable {F : Type*} [Field F]

@[expose] def PairPropIn {G : Type*} [Group G] (M : Subgroup G) : Prop :=
  ∀ z ∈ M, z ^ 3 = 1 → z ≠ 1 →
    ∃ m ∈ M, (m * z * m⁻¹) * z = z * (m * z * m⁻¹) ∧ m * z * m⁻¹ ∉ Subgroup.zpowers z

theorem PairPropIn.pairProp {G : Type*} [Group G] {M : Subgroup G} (h : PairPropIn M) :
    PairProp M := by
  intro z hz3 hz1
  obtain ⟨m, hm, hc, hn⟩ := h z z.2 (by simpa using congrArg Subtype.val hz3)
    (fun h1 => hz1 (Subtype.ext h1))
  refine ⟨⟨m, hm⟩, Subtype.ext hc, ?_⟩
  intro hmem
  apply hn
  rw [Subgroup.mem_zpowers_iff] at hmem ⊢
  obtain ⟨k, hk⟩ := hmem
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem partner_sub {G : Type*} [Group G] (M : Subgroup G) [Finite M] {z u : G} (hzM : z ∈ M)
    (huM : u ∈ M) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) (hu3 : u ^ 3 = 1)
    (hfree : ∀ m ∈ M, (m * z * m⁻¹) * u ≠ u * (m * z * m⁻¹)) :
    ∃ m ∈ M, (m * z * m⁻¹) * z = z * (m * z * m⁻¹) ∧ m * z * m⁻¹ ∉ Subgroup.zpowers z := by
  obtain ⟨m, hc, hn⟩ := exists_partner_of_free (M := M) (z := ⟨z, hzM⟩) (u := ⟨u, huM⟩)
    (Subtype.ext (by simpa using hz3)) (fun h1 => hz1 (congrArg Subtype.val h1))
    (Subtype.ext (by simpa using hu3)) (fun m hcomm => hfree m m.2 (by
      simpa using congrArg Subtype.val hcomm))
  refine ⟨m, m.2, by simpa using congrArg Subtype.val hc, ?_⟩
  intro hmem
  apply hn
  rw [Subgroup.mem_zpowers_iff] at hmem ⊢
  obtain ⟨k, hk⟩ := hmem
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem heis_not_comm_hom {ω : F} (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1) {dH g : GL (Fin 3) F}
    (hdH : (dH : Matrix (Fin 3) (Fin 3) F) = homMat ω)
    (hE : IsHeis (g : Matrix (Fin 3) (Fin 3) F)) (k : GL (Fin 3) F) :
    ProjGenLinGroup.mk (k * g * k⁻¹) * ProjGenLinGroup.mk dH ≠
      ProjGenLinGroup.mk dH * ProjGenLinGroup.mk (k * g * k⁻¹) := by
  intro hcomm
  have h1 : ProjGenLinGroup.mk (k * g * k⁻¹ * dH) = ProjGenLinGroup.mk (dH * (k * g * k⁻¹)) := by
    rw [map_mul, map_mul]; exact hcomm
  obtain ⟨s, hs0, hs⟩ := (mk_eq_iff _ _).1 h1
  have hK : IsHeis ((k * g * k⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    have := IsHeis.conj_smul (g := (g : Matrix (Fin 3) (Fin 3) F))
      (k := (k : Matrix (Fin 3) (Fin 3) F)) k.isUnit 1 one_ne_zero hE
    simpa [Units.val_mul, Matrix.coe_units_inv, one_smul] using this
  obtain ⟨a, u, v, hu, hv, hgav⟩ : ∃ (a : F) (u v : Fin 3 → F), u ≠ 0 ∧ v ≠ 0 ∧
      homMat ω = a • (1 : Matrix (Fin 3) (Fin 3) F) + Matrix.vecMulVec u v :=
    (homMat_spec hω1 hω3).1
  refine no_commute_homol_heis (dH : Matrix (Fin 3) (Fin 3) F)
    ((k * g * k⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) dH.isUnit (Units.isUnit _) a u v hu
    hv (by rw [hdH]; exact hgav) hK s ?_
  rw [Units.val_mul] at hs
  simpa [Units.val_mul] using hs

theorem homol_not_comm_heis {l : F} (hl : ∀ θ : F, θ ^ 3 ≠ l) {cH g : GL (Fin 3) F}
    (hcH : (cH : Matrix (Fin 3) (Fin 3) F) = heisMat l)
    (hH : IsHomol (g : Matrix (Fin 3) (Fin 3) F)) (k : GL (Fin 3) F) :
    ProjGenLinGroup.mk (k * g * k⁻¹) * ProjGenLinGroup.mk cH ≠
      ProjGenLinGroup.mk cH * ProjGenLinGroup.mk (k * g * k⁻¹) := by
  intro hcomm
  have h1 : ProjGenLinGroup.mk (k * g * k⁻¹ * cH) = ProjGenLinGroup.mk (cH * (k * g * k⁻¹)) := by
    rw [map_mul, map_mul]; exact hcomm
  obtain ⟨s, hs0, hs⟩ := (mk_eq_iff _ _).1 h1
  have hK : IsHomol ((k * g * k⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    have := IsHomol.conj_smul (g := (g : Matrix (Fin 3) (Fin 3) F))
      (k := (k : Matrix (Fin 3) (Fin 3) F)) k.isUnit 1 one_ne_zero hH
    simpa [Units.val_mul, Matrix.coe_units_inv, one_smul] using this
  obtain ⟨a, u, v, hu, hv, hgav⟩ : ∃ (a : F) (u v : Fin 3 → F), u ≠ 0 ∧ v ≠ 0 ∧
      ((k * g * k⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        a • (1 : Matrix (Fin 3) (Fin 3) F) + Matrix.vecMulVec u v := hK
  refine no_commute_homol_heis ((k * g * k⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
    (cH : Matrix (Fin 3) (Fin 3) F) (Units.isUnit _) cH.isUnit a u v hu hv hgav
    (by rw [hcH]; exact (heisMat_spec hl).1) s⁻¹ ?_
  have hs' : (cH : Matrix (Fin 3) (Fin 3) F) *
      ((k * g * k⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      s • (((k * g * k⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        (cH : Matrix (Fin 3) (Fin 3) F)) := by simpa [Units.val_mul] using hs
  rw [hs', smul_smul, inv_mul_cancel₀ hs0, one_smul]

section Sub

variable [Finite F]

theorem pair_E_sub (H : Subgroup (GL (Fin 3) F)) {ω : F} (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1)
    {dH : GL (Fin 3) F} (hdHmat : (dH : Matrix (Fin 3) (Fin 3) F) = homMat ω) (hdH : dH ∈ H)
    {g : GL (Fin 3) F} (hg : g ∈ H) (hz3 : ProjGenLinGroup.mk g ^ 3 = 1)
    (hz1 : ProjGenLinGroup.mk g ≠ 1) (hE : IsHeis (g : Matrix (Fin 3) (Fin 3) F)) :
    ∃ m ∈ H.map (ProjGenLinGroup.mk : GL (Fin 3) F →* PGL(3, F)),
      (m * ProjGenLinGroup.mk g * m⁻¹) * ProjGenLinGroup.mk g =
        ProjGenLinGroup.mk g * (m * ProjGenLinGroup.mk g * m⁻¹) ∧
      m * ProjGenLinGroup.mk g * m⁻¹ ∉ Subgroup.zpowers (ProjGenLinGroup.mk g) := by
  have hdH3 : dH ^ 3 = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, hdHmat]; exact (homMat_spec hω1 hω3).2.2)
  have hu3 : ProjGenLinGroup.mk dH ^ 3 = 1 := by rw [← map_pow, hdH3, map_one]
  refine partner_sub (H.map (ProjGenLinGroup.mk : GL (Fin 3) F →* PGL(3, F)))
    (Subgroup.mem_map.2 ⟨g, hg, rfl⟩) (Subgroup.mem_map.2 ⟨dH, hdH, rfl⟩) hz3 hz1 hu3 ?_
  intro m hm
  obtain ⟨k, -, rfl⟩ := Subgroup.mem_map.1 hm
  have := heis_not_comm_hom hω1 hω3 hdHmat hE k
  rwa [map_mul, map_mul, map_inv] at this

theorem pair_H_sub (H : Subgroup (GL (Fin 3) F)) {l : F} (hl : ∀ θ : F, θ ^ 3 ≠ l)
    {cH : GL (Fin 3) F} (hcHmat : (cH : Matrix (Fin 3) (Fin 3) F) = heisMat l) (hcH : cH ∈ H)
    {g : GL (Fin 3) F} (hg : g ∈ H) (hz3 : ProjGenLinGroup.mk g ^ 3 = 1)
    (hz1 : ProjGenLinGroup.mk g ≠ 1) (hH : IsHomol (g : Matrix (Fin 3) (Fin 3) F)) :
    ∃ m ∈ H.map (ProjGenLinGroup.mk : GL (Fin 3) F →* PGL(3, F)),
      (m * ProjGenLinGroup.mk g * m⁻¹) * ProjGenLinGroup.mk g =
        ProjGenLinGroup.mk g * (m * ProjGenLinGroup.mk g * m⁻¹) ∧
      m * ProjGenLinGroup.mk g * m⁻¹ ∉ Subgroup.zpowers (ProjGenLinGroup.mk g) := by
  have hcH3 : ProjGenLinGroup.mk cH ^ 3 = 1 := by
    rw [← map_pow, ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar]
    have hl0 : l ≠ 0 := fun h => hl 0 (by simp [h])
    refine ⟨Units.mk0 l hl0, ?_⟩
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hcHmat, (heisMat_spec hl).2.2,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
    rfl
  refine partner_sub (H.map (ProjGenLinGroup.mk : GL (Fin 3) F →* PGL(3, F)))
    (Subgroup.mem_map.2 ⟨g, hg, rfl⟩) (Subgroup.mem_map.2 ⟨cH, hcH, rfl⟩) hz3 hz1 hcH3 ?_
  intro m hm
  obtain ⟨k, -, rfl⟩ := Subgroup.mem_map.1 hm
  have := homol_not_comm_heis hl hcHmat hH k
  rwa [map_mul, map_mul, map_inv] at this

theorem pair_R_sub (H : Subgroup (GL (Fin 3) F)) (hF2 : (2 : F) = 0) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0)
    {P : GL (Fin 3) F} (hPmat : (P : Matrix (Fin 3) (Fin 3) F) = Phi ω) (hPH : P ∈ H)
    {g : GL (Fin 3) F} (hz3 : ProjGenLinGroup.mk g ^ 3 = 1) (hz1 : ProjGenLinGroup.mk g ≠ 1)
    (A : GL (Fin 3) F) (hAH : A ∈ H) (μ : F)
    (hga : (g : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 3) (Fin 3) F) * (μ • Dm ω)) :
    ∃ m ∈ H.map (ProjGenLinGroup.mk : GL (Fin 3) F →* PGL(3, F)),
      (m * ProjGenLinGroup.mk g * m⁻¹) * ProjGenLinGroup.mk g =
        ProjGenLinGroup.mk g * (m * ProjGenLinGroup.mk g * m⁻¹) ∧
      m * ProjGenLinGroup.mk g * m⁻¹ ∉ Subgroup.zpowers (ProjGenLinGroup.mk g) := by
  classical
  obtain ⟨hF1, hF4, hF3⟩ := fourier_identities hF2 hω
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω3
  obtain ⟨D, hDdef⟩ : ∃ D : GL (Fin 3) F, D = A⁻¹ * g * A := ⟨_, rfl⟩
  have hDmat : (D : Matrix (Fin 3) (Fin 3) F) = μ • Dm ω := by
    rw [hDdef, Units.val_mul, Units.val_mul, mul_assoc, hga, ← mul_assoc,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    have := D.isUnit
    rw [hDmat, zero_smul] at this
    exact (not_isUnit_zero (M₀ := Matrix (Fin 3) (Fin 3) F)) this
  obtain ⟨Q, hQdef⟩ : ∃ Q : GL (Fin 3) F, Q = P⁻¹ * D * P := ⟨_, rfl⟩
  have hQmat : (Q : Matrix (Fin 3) (Fin 3) F) = μ • Pm := by
    rw [hQdef, Units.val_mul, Units.val_mul, hDmat, hPmat]
    have h1 : (μ • Dm ω) * Phi ω = Phi ω * (μ • Pm) := by
      rw [Matrix.smul_mul, hF1, Matrix.mul_smul]
    rw [mul_assoc, h1, ← mul_assoc, ← hPmat, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_mul]
  have hgD : g = A * D * A⁻¹ := by rw [hDdef]; group
  have hmz : ProjGenLinGroup.mk (A * P⁻¹ * A⁻¹) * ProjGenLinGroup.mk g *
      (ProjGenLinGroup.mk (A * P⁻¹ * A⁻¹))⁻¹ = ProjGenLinGroup.mk (A * Q * A⁻¹) := by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    rw [hQdef, hDdef]
    group
  have hmkg : ProjGenLinGroup.mk g = ProjGenLinGroup.mk A * ProjGenLinGroup.mk D *
      (ProjGenLinGroup.mk A)⁻¹ := by
    conv_lhs => rw [hgD]
    simp [map_mul, map_inv]
  have hQD : ProjGenLinGroup.mk (Q * D) = ProjGenLinGroup.mk (D * Q) := by
    refine (mk_eq_iff _ _).2 ⟨(ω ^ 2)⁻¹, inv_ne_zero (pow_ne_zero 2 hω0), ?_⟩
    rw [Units.val_mul, Units.val_mul, hQmat, hDmat, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul, hF3, smul_smul, smul_smul]
    congr 1
    field_simp
  refine ⟨ProjGenLinGroup.mk (A * P⁻¹ * A⁻¹),
    Subgroup.mem_map.2 ⟨_, mul_mem (mul_mem hAH (inv_mem hPH)) (inv_mem hAH), rfl⟩, ?_, ?_⟩
  · rw [hmz, hmkg]
    have e1 : ProjGenLinGroup.mk (A * Q * A⁻¹) * (ProjGenLinGroup.mk A * ProjGenLinGroup.mk D *
        (ProjGenLinGroup.mk A)⁻¹) = ProjGenLinGroup.mk A * ProjGenLinGroup.mk (Q * D) *
        (ProjGenLinGroup.mk A)⁻¹ := by simp [map_mul, map_inv, mul_assoc]
    have e2 : (ProjGenLinGroup.mk A * ProjGenLinGroup.mk D * (ProjGenLinGroup.mk A)⁻¹) *
        ProjGenLinGroup.mk (A * Q * A⁻¹) = ProjGenLinGroup.mk A * ProjGenLinGroup.mk (D * Q) *
        (ProjGenLinGroup.mk A)⁻¹ := by simp [map_mul, map_inv, mul_assoc]
    rw [e1, e2, hQD]
  · rw [hmz, hmkg]
    intro hmem
    have hmem' : ProjGenLinGroup.mk Q ∈ Subgroup.zpowers (ProjGenLinGroup.mk D) := by
      have := (mem_zpowers_conj_iff (ProjGenLinGroup.mk A) (ProjGenLinGroup.mk Q)
        (ProjGenLinGroup.mk D)).1 (by simpa [map_mul, map_inv] using hmem)
      exact this
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem'
    have hDm3 : Dm ω ^ 3 = 1 := by
      rw [Dm, Matrix.diagonal_pow]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply] <;> grind
    have hD3 : ProjGenLinGroup.mk D ^ 3 = 1 := by
      rw [← map_pow, ← map_one ProjGenLinGroup.mk]
      refine (mk_eq_iff _ _).2 ⟨(μ ^ 3)⁻¹, inv_ne_zero (pow_ne_zero 3 hμ0), ?_⟩
      rw [Units.val_pow_eq_pow_val, hDmat, smul_pow, hDm3, smul_smul,
        inv_mul_cancel₀ (pow_ne_zero 3 hμ0), one_smul]
      rfl
    have hD1 : ProjGenLinGroup.mk D ≠ 1 := by
      intro h1
      apply hz1
      rw [hmkg, h1]
      simp
    have hord : orderOf (ProjGenLinGroup.mk D) = 3 := orderOf_eq_prime hD3 hD1
    have hk3 := zpow_mod_orderOf (ProjGenLinGroup.mk D) k
    rw [hord] at hk3
    rw [← hk3] at hk
    have hr : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by omega
    rcases hr with hr | hr | hr
    · rw [hr, zpow_zero, ← map_one ProjGenLinGroup.mk] at hk
      obtain ⟨s, hs0, hs⟩ := (mk_eq_iff _ _).1 hk
      have h10 := congrFun (congrFun hs 1) 0
      rw [hQmat] at h10
      simp [Pm] at h10
      exact hμ0 h10
    · rw [hr, zpow_one] at hk
      obtain ⟨s, hs0, hs⟩ := (mk_eq_iff _ _).1 hk
      have h10 := congrFun (congrFun hs 1) 0
      rw [hQmat, hDmat] at h10
      simp [Pm, Dm, Matrix.diagonal_apply] at h10
      exact hμ0 h10
    · rw [hr, zpow_two, ← map_mul] at hk
      obtain ⟨s, hs0, hs⟩ := (mk_eq_iff _ _).1 hk
      have h10 := congrFun (congrFun hs 1) 0
      rw [hQmat, Units.val_mul, hDmat] at h10
      simp [Pm, Dm, Matrix.diagonal_apply, Matrix.mul_apply, Fin.sum_univ_three] at h10
      exact hμ0 h10

theorem pairPropIn_of_data (H : Subgroup (GL (Fin 3) F)) (hF2 : (2 : F) = 0) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0)
    (hdH : ∃ d ∈ H, (d : Matrix (Fin 3) (Fin 3) F) = homMat ω)
    (hcH : ∃ l : F, (∀ θ : F, θ ^ 3 ≠ l) ∧ ∃ c ∈ H, (c : Matrix (Fin 3) (Fin 3) F) = heisMat l)
    (hP : ∃ P ∈ H, (P : Matrix (Fin 3) (Fin 3) F) = Phi ω)
    (hreg : ∀ g ∈ H, IsReg ω (g : Matrix (Fin 3) (Fin 3) F) →
      ∃ A ∈ H, ∃ μ : F, (g : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) =
        (A : Matrix (Fin 3) (Fin 3) F) * (μ • Dm ω)) :
    PairPropIn (H.map (ProjGenLinGroup.mk : GL (Fin 3) F →* PGL(3, F))) := by
  classical
  intro z hz hz3 hz1
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hz
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hω1 : ω ≠ 1 := by
    intro h1
    have h3 : (3 : F) = 0 := by rw [h1] at hω; linear_combination hω
    have h4 : (1 : F) = 0 := by linear_combination h3 - hF2
    exact one_ne_zero h4
  obtain ⟨c, hc⟩ := pgl_pow_three hz3
  rcases trichotomy hF2 hω g.isUnit hc (pgl_not_scalar hz1) with hE | hH | hR
  · obtain ⟨d, hdm, hdmat⟩ := hdH
    exact pair_E_sub H hω1 hω3 hdmat hdm hg hz3 hz1 hE
  · obtain ⟨l, hl, c', hcm, hcmat⟩ := hcH
    exact pair_H_sub H hl hcmat hcm hg hz3 hz1 hH
  · obtain ⟨A, hAH, μ, hga⟩ := hreg g hg hR
    obtain ⟨P, hPH, hPmat⟩ := hP
    exact pair_R_sub H hF2 hω hPmat hPH hz3 hz1 A hAH μ hga

end Sub

end CFSG.RankThree.PartTwo.Sec19.NF5Pair