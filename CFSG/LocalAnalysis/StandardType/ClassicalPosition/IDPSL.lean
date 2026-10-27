module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LieType.Universal.SpecialLinearExtras
public import CFSG.Assembly.Defs
public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeTypeA
public import CFSG.LocalAnalysis.StandardType.GGSixBstarUniqueRootPlaneA

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType

private theorem idPSL_inv_mul_sq {G : Type} [Group G] {a b : G}
    (h : a * b = b * a) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) : (a⁻¹ * b) ^ 2 = 1 := by
  have hba : b * a⁻¹ = a⁻¹ * b := by
    calc b * a⁻¹ = a⁻¹ * (a * b) * a⁻¹ := by group
      _ = a⁻¹ * (b * a) * a⁻¹ := by rw [h]
      _ = a⁻¹ * b := by group
  rw [pow_two] at ha hb ⊢
  calc (a⁻¹ * b) * (a⁻¹ * b)
      = a⁻¹ * (b * a⁻¹) * b := by group
    _ = a⁻¹ * (a⁻¹ * b) * b := by rw [hba]
    _ = (a⁻¹ * a⁻¹) * (b * b) := by group
    _ = 1 := by rw [← mul_inv_rev, ha, inv_one, hb, one_mul]

private theorem idPSL_char2_sq_eq_one {F : Type} [Field F] [CharP F 2] {a : F}
    (ha : a * a = 1) : a = 1 := by
  have ha' : a ^ 2 = 1 := by simpa [pow_two] using ha
  have h : (a + 1) ^ 2 = 0 := by
    rw [add_sq, ha']
    ring_nf
    simp [CharTwo.two_eq_zero]
  have h2 : a + 1 = 0 := sq_eq_zero_iff.mp h
  have : a = -1 := by rwa [eq_neg_iff_add_eq_zero]
  rw [this, CharTwo.neg_eq]

private theorem idPSL_center_eq_one {F : Type} [Field F] [CharP F 2]
    {A : Matrix.SpecialLinearGroup (Fin (1 + 1)) F}
    (hA : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin (1 + 1)) F)) : A = 1 := by
  obtain ⟨a, hapow, hamat⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have ha2 : a ^ 2 = 1 := by simpa using hapow
  have haa : a * a = 1 := by simpa [pow_two] using ha2
  have ha1 : a = 1 := idPSL_char2_sq_eq_one haa
  apply Subtype.ext
  rw [← hamat, ha1]
  simp [Matrix.scalar_apply, Matrix.SpecialLinearGroup.coe_one]

private theorem idPSL_eq_of_center_involution {m : ℕ} {F : Type} [Field F] [CharP F 2]
    {u1 u2 : Matrix.SpecialLinearGroup (Fin (m + 1)) F}
    (hC : u1⁻¹ * u2 ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    (h1 : u1 ^ 2 = 1) (h2 : u2 ^ 2 = 1) : u1 = u2 := by
  have hcomm : u1 * u2 = u2 * u1 := by
    have hcent := (Subgroup.mem_center_iff.mp hC) u1
    rw [mul_inv_cancel_left] at hcent
    have := congrArg (fun z => u1 * z) hcent
    simpa [mul_assoc] using this
  have hCsq : (u1⁻¹ * u2) ^ 2 = 1 := idPSL_inv_mul_sq hcomm h1 h2
  obtain ⟨a, hapow, hamat⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hC
  have haa : a * a = 1 := by
    have hmat1 : (↑(u1⁻¹ * u2) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
        (↑(u1⁻¹ * u2) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, ← pow_two, hCsq,
        Matrix.SpecialLinearGroup.coe_one]
    rw [← hamat] at hmat1
    have h1' : Matrix.scalar (Fin (m + 1)) (a * a) = Matrix.scalar (Fin (m + 1)) 1 := by
      simpa [Matrix.scalar_apply, Matrix.diagonal_mul_diagonal] using hmat1
    exact Matrix.scalar_inj.mp h1'
  have ha1 : a = 1 := idPSL_char2_sq_eq_one haa
  have hC1 : u1⁻¹ * u2 = 1 := by
    apply Subtype.ext
    rw [← hamat, ha1]
    simp [Matrix.scalar_apply, Matrix.SpecialLinearGroup.coe_one]
  calc u1 = u1 * (u1⁻¹ * u2) := by rw [hC1, mul_one]
    _ = u2 := by group

private theorem idPSL_g_commute_transvection {m : ℕ} {F : Type} [Field F] [CharP F 2]
    {X : Type} [Group X]
    (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* X)
    (hψ : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {b : X} {s s' : GL (Fin (m + 1)) F}
    (hs : IsGLLift Matrix.SpecialLinearGroup.toGL ψ s b)
    (hs' : IsGLLift Matrix.SpecialLinearGroup.toGL ψ s' b)
    (i j : Fin (m + 1)) (hij : i ≠ j) (t : F) :
    Commute (Matrix.transvection i j t)
      (((s'⁻¹ * s : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) := by
  obtain ⟨u1, h1, h1ψ⟩ := hs (Matrix.SpecialLinearGroup.transvection hij t)
  obtain ⟨u2, h2, h2ψ⟩ := hs' (Matrix.SpecialLinearGroup.transvection hij t)
  have hker : u1⁻¹ * u2 ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← h1ψ, ← h2ψ, inv_mul_cancel]
  have hcenter : u1⁻¹ * u2 ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F) :=
    hψ hker
  have hXsq : (Matrix.SpecialLinearGroup.transvection hij t) ^ 2 = 1 := by
    rw [pow_two, ← Matrix.SpecialLinearGroup.transvection_add,
      show t + t = 0 from by rw [← two_mul, CharTwo.two_eq_zero, zero_mul],
      Matrix.SpecialLinearGroup.transvection_coeff_zero]
  have hXsq' : (Matrix.SpecialLinearGroup.toGL
      (Matrix.SpecialLinearGroup.transvection hij t)) ^ 2 = 1 := by
    rw [← map_pow, hXsq, map_one]
  have h1sq : u1 ^ 2 = 1 := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    have hc : Matrix.SpecialLinearGroup.toGL u1 =
        (MulAut.conj s)
          (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij t)) := by
      rw [h1]; simp [MulAut.conj_apply]
    rw [map_pow, map_one, hc, ← map_pow, hXsq', map_one]
  have h2sq : u2 ^ 2 = 1 := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    have hc : Matrix.SpecialLinearGroup.toGL u2 =
        (MulAut.conj s')
          (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij t)) := by
      rw [h2]; simp [MulAut.conj_apply]
    rw [map_pow, map_one, hc, ← map_pow, hXsq', map_one]
  have hu : u1 = u2 := idPSL_eq_of_center_involution hcenter h1sq h2sq
  have hGL : s * Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.transvection hij t) * s⁻¹ =
      s' * Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.transvection hij t) * s'⁻¹ := by
    rw [← h1, ← h2, hu]
  have hcommGL : (s'⁻¹ * s) *
      Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij t) =
      Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij t) *
        (s'⁻¹ * s) := by
    have h := congrArg (fun z : GL (Fin (m + 1)) F => s'⁻¹ * z * s) hGL
    calc (s'⁻¹ * s) * Matrix.SpecialLinearGroup.toGL
          (Matrix.SpecialLinearGroup.transvection hij t)
        = s'⁻¹ * (s * Matrix.SpecialLinearGroup.toGL
            (Matrix.SpecialLinearGroup.transvection hij t) * s⁻¹) * s := by group
      _ = s'⁻¹ * (s' * Matrix.SpecialLinearGroup.toGL
            (Matrix.SpecialLinearGroup.transvection hij t) * s'⁻¹) * s := h
      _ = Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij t) *
            (s'⁻¹ * s) := by group
  change (Matrix.transvection i j t) *
      (((s'⁻¹ * s : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) =
      (((s'⁻¹ * s : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) *
        (Matrix.transvection i j t)
  have h := congrArg (fun z : GL (Fin (m + 1)) F =>
    (z : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) hcommGL
  rw [Units.val_mul, Units.val_mul] at h
  simpa [Matrix.transvection, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using h.symm

private theorem idPSL_weyl_mul {F : Type} [Field F] [CharP F 2]
    (h01 : (0 : Fin (1 + 1)) ≠ 1) (h10 : (1 : Fin (1 + 1)) ≠ 0) (t : F) :
    (Matrix.SpecialLinearGroup.transvection h01 1 *
        Matrix.SpecialLinearGroup.transvection h10 1 *
        Matrix.SpecialLinearGroup.transvection h01 1) *
      Matrix.SpecialLinearGroup.transvection h01 t =
    Matrix.SpecialLinearGroup.transvection h10 t *
      (Matrix.SpecialLinearGroup.transvection h01 1 *
        Matrix.SpecialLinearGroup.transvection h10 1 *
        Matrix.SpecialLinearGroup.transvection h01 1) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply, Matrix.one_apply]
  · exact Or.inl (show (1 : F) + 1 = 0 from by
      rw [show (1 : F) + 1 = 2 by norm_num, CharTwo.two_eq_zero])
  · exact Or.inr (show (1 : F) + 1 = 0 from by
      rw [show (1 : F) + 1 = 2 by norm_num, CharTwo.two_eq_zero])
  · rw [show (1 : F) + 1 = 0 from by
      rw [show (1 : F) + 1 = 2 by norm_num, CharTwo.two_eq_zero]]
    ring

private theorem idPSL_M_matrix {F : Type} [Field F] [CharP F 2]
    (h01 : (0 : Fin (1 + 1)) ≠ 1) (h10 : (1 : Fin (1 + 1)) ≠ 0) (r s : F) :
    ((Matrix.SpecialLinearGroup.transvection h01 r *
        Matrix.SpecialLinearGroup.transvection h10 s *
        Matrix.SpecialLinearGroup.transvection h01 r :
        Matrix.SpecialLinearGroup (Fin (1 + 1)) F) :
      Matrix (Fin (1 + 1)) (Fin (1 + 1)) F) =
    !![1 + r * s, r * r * s; s, 1 + r * s] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply, Matrix.one_apply]
  · ring_nf
    simp [CharTwo.two_eq_zero]
  · ring

private theorem idPSL_hrs_of_mul_eq {F : Type} [Field F] [CharP F 2]
    (h01 : (0 : Fin (1 + 1)) ≠ 1) (h10 : (1 : Fin (1 + 1)) ≠ 0)
    {r s : F} (hr : r ≠ 0)
    (h : (Matrix.SpecialLinearGroup.transvection h01 r *
        Matrix.SpecialLinearGroup.transvection h10 s *
        Matrix.SpecialLinearGroup.transvection h01 r) *
      Matrix.SpecialLinearGroup.transvection h01 r =
      Matrix.SpecialLinearGroup.transvection h10 s *
      (Matrix.SpecialLinearGroup.transvection h01 r *
        Matrix.SpecialLinearGroup.transvection h10 s *
        Matrix.SpecialLinearGroup.transvection h01 r)) :
    r * s = 1 := by
  let M : Matrix.SpecialLinearGroup (Fin (1 + 1)) F :=
    Matrix.SpecialLinearGroup.transvection h01 r *
      Matrix.SpecialLinearGroup.transvection h10 s *
      Matrix.SpecialLinearGroup.transvection h01 r
  have hM : (M : Matrix (Fin (1 + 1)) (Fin (1 + 1)) F) =
      !![1 + r * s, r * r * s; s, 1 + r * s] := idPSL_M_matrix h01 h10 r s
  have hmat_eq : (M : Matrix (Fin (1 + 1)) (Fin (1 + 1)) F) *
        (Matrix.SpecialLinearGroup.transvection h01 r :
          Matrix (Fin (1 + 1)) (Fin (1 + 1)) F) =
      (Matrix.SpecialLinearGroup.transvection h10 s :
          Matrix (Fin (1 + 1)) (Fin (1 + 1)) F) *
        (M : Matrix (Fin (1 + 1)) (Fin (1 + 1)) F) := by
    have := congrArg (fun z : Matrix.SpecialLinearGroup (Fin (1 + 1)) F =>
      (z : Matrix (Fin (1 + 1)) (Fin (1 + 1)) F)) h
    simpa [M, Matrix.SpecialLinearGroup.coe_mul] using this
  have h01e := congrFun (congrFun hmat_eq 0) 1
  rw [hM, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two] at h01e
  simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply, Matrix.one_apply] at h01e
  rcases h01e with h | h
  · have hrs : r * s = -1 :=
      ((neg_eq_iff_add_eq_zero (a := (1 : F)) (b := r * s)).mpr h).symm
    rw [hrs, CharTwo.neg_eq]
  · exact absurd h hr

private theorem idPSL_exists_conj_one {F : Type} [Field F] [CharP F 2] {X : Type} [Group X]
    (ψ : Matrix.SpecialLinearGroup (Fin (1 + 1)) F →* X)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (1 + 1)) F))
    {x : X} {χ : Fin (1 + 1) → Fin (1 + 1) → F}
    (hχ : ∀ (i j : Fin (1 + 1)) (hij : i ≠ j) (t : F),
      x⁻¹ * ψ (Matrix.SpecialLinearGroup.transvection hij t) * x =
        ψ (Matrix.SpecialLinearGroup.transvection hij (χ i j * t))) :
    ∃ D : GL (Fin (1 + 1)) F, ∀ u,
      x⁻¹ * ψ u * x = ψ (InnerDiagA.conjSL D u) := by
  let β : Matrix.SpecialLinearGroup (Fin (1 + 1)) F →* X :=
    (MulAut.conj x⁻¹).toMonoidHom.comp ψ
  have hβ : ∀ u, β u = x⁻¹ * ψ u * x := fun u => by simp [β]
  have hχ' : ∀ (i j : Fin (1 + 1)) (hij : i ≠ j) (t : F),
      β (Matrix.SpecialLinearGroup.transvection hij t) =
        ψ (Matrix.SpecialLinearGroup.transvection hij (χ i j * t)) :=
    fun i j hij t => (hβ _).trans (hχ i j hij t)
  have hne : ∀ i j : Fin (1 + 1), i ≠ j → χ i j ≠ 0 := by
    intro i j hij h0
    have h1 := hχ i j hij 1
    rw [h0, zero_mul, Matrix.SpecialLinearGroup.transvection_coeff_zero, map_one] at h1
    have h2 : ψ (Matrix.SpecialLinearGroup.transvection hij 1) = 1 := by
      calc ψ (Matrix.SpecialLinearGroup.transvection hij 1)
          = x * (x⁻¹ * ψ (Matrix.SpecialLinearGroup.transvection hij 1) * x) * x⁻¹ := by
            group
        _ = 1 := by rw [h1]; group
    exact one_ne_zero (InnerDiagA.eq_zero_of_transvection_mem_center hij (hker h2))
  have h01 : (0 : Fin (1 + 1)) ≠ 1 := by decide
  have h10 : (1 : Fin (1 + 1)) ≠ 0 := by decide
  let r : F := χ 0 1
  let s : F := χ 1 0
  have hr : r ≠ 0 := hne 0 1 h01
  let x01 : F → Matrix.SpecialLinearGroup (Fin (1 + 1)) F := fun t =>
    Matrix.SpecialLinearGroup.transvection h01 t
  let x10 : F → Matrix.SpecialLinearGroup (Fin (1 + 1)) F := fun t =>
    Matrix.SpecialLinearGroup.transvection h10 t
  have hβ01 : ∀ t, β (x01 t) = ψ (x01 (r * t)) := by
    intro t
    have := hχ' 0 1 h01 t
    simpa [x01, r] using this
  have hβ10 : ∀ t, β (x10 t) = ψ (x10 (s * t)) := by
    intro t
    have := hχ' 1 0 h10 t
    simpa [x10, s] using this
  let w : Matrix.SpecialLinearGroup (Fin (1 + 1)) F := x01 1 * x10 1 * x01 1
  let M : Matrix.SpecialLinearGroup (Fin (1 + 1)) F := x01 r * x10 s * x01 r
  have hw : β w = ψ M := by
    simp only [w, M, map_mul]
    rw [hβ01 1, hβ10 1]
    simp only [mul_one]
  have hweyl : ∀ t : F, w * x01 t * w⁻¹ = x10 t := by
    intro t
    have hmul : w * x01 t = x10 t * w := by
      simpa [w, x01, x10] using idPSL_weyl_mul h01 h10 t
    rw [hmul]
    group
  have hconj : ∀ t : F, β (w * x01 t * w⁻¹) = ψ (M * x01 (r * t) * M⁻¹) := by
    intro t
    simp only [map_mul, map_inv]
    rw [hw, hβ01 t]
  have hψw : ∀ t : F, ψ (M * x01 (r * t) * M⁻¹) = ψ (x10 (s * t)) := by
    intro t
    rw [← hconj t, hweyl t, hβ10 t]
  have hUV : ∀ t : F, M * x01 (r * t) * M⁻¹ = x10 (s * t) := by
    intro t
    have hmem : (M * x01 (r * t) * M⁻¹)⁻¹ * x10 (s * t) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      rw [map_mul, map_inv, hψw t]
      group
    have h1 : (M * x01 (r * t) * M⁻¹)⁻¹ * x10 (s * t) = 1 :=
      idPSL_center_eq_one (hker hmem)
    have : x10 (s * t) = M * x01 (r * t) * M⁻¹ := by
      calc x10 (s * t) = (M * x01 (r * t) * M⁻¹) *
            ((M * x01 (r * t) * M⁻¹)⁻¹ * x10 (s * t)) := by group
        _ = M * x01 (r * t) * M⁻¹ := by rw [h1, mul_one]
    exact this.symm
  have hMT : M * x01 r = x10 s * M := by
    have h := hUV 1
    have h' : M * x01 r * M⁻¹ = x10 s := by simpa using h
    calc M * x01 r = (M * x01 r * M⁻¹) * M := by group
      _ = x10 s * M := by rw [h']
  have hrs : r * s = 1 := idPSL_hrs_of_mul_eq h01 h10 hr (by simpa [M, x01, x10] using hMT)
  let d : Fin (1 + 1) → Fˣ := fun i => if i = 0 then Units.mk0 r hr else 1
  have hd : ∀ i j : Fin (1 + 1), i ≠ j → (d i : F) = χ i j * (d j : F) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simp [d, r]
    · simp [d, r, s]
      rw [mul_comm s r, hrs]
    · exact absurd rfl hij
  refine ⟨InnerDiagA.diagGL d, fun u => ?_⟩
  have hβψ : β = ψ.comp (InnerDiagA.conjSL (InnerDiagA.diagGL d)) := by
    refine MonoidHom.eq_of_eqOn_dense
      Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field ?_
    rintro _ ⟨⟨i, j, hij, t⟩, rfl⟩
    rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk, hχ', MonoidHom.comp_apply,
      InnerDiagA.conjSL_diagGL_transvection, hd i j hij, Units.val_inv_eq_inv_val,
      mul_right_comm (χ i j), mul_assoc _ _ ((d j : F))⁻¹, mul_inv_cancel₀ (d j).ne_zero,
      mul_one]
  rw [← hβ, hβψ, MonoidHom.comp_apply]

theorem exists_isGLLift_PSL (m : ℕ) (F : Type) [Field F] [CharP F 2]
    {X : Type} [Group X] (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) {b : X} (hbN : b ∈ Subgroup.normalizer (ψ.range : Set X))
    (hb : GGPsiInnerDiag (SpecialLinear.rootDatum m F) ψ b) :
    ∃ s : GL (Fin (m + 1)) F, IsGLLift Matrix.SpecialLinearGroup.toGL ψ s b := by
  have hm_cases : m = 0 ∨ m = 1 ∨ 2 ≤ m := by omega
  rcases hm_cases with rfl | rfl | hm
  · refine ⟨1, fun u => ⟨u, by group, ?_⟩⟩
    haveI : Subsingleton (Matrix.SpecialLinearGroup (Fin (0 + 1)) F) :=
      (inferInstance : Subsingleton (Matrix.SpecialLinearGroup (Fin 1) F))
    have hu : u = 1 := Subsingleton.elim u 1
    rw [hu, map_one]
    group
  · obtain ⟨g, hg, χ, hχ⟩ := InnerDiagA.exists_chi_of_ggPsiInnerDiag ψ hb
    obtain ⟨s0, rfl⟩ := hg
    obtain ⟨D, hD⟩ := idPSL_exists_conj_one ψ hψ hχ
    refine ⟨Matrix.SpecialLinearGroup.toGL s0 * D, fun u => ?_⟩
    have h2 : b⁻¹ * ψ u * b = ψ (s0 * InnerDiagA.conjSL D u * s0⁻¹) := by
      rw [map_mul, map_mul, map_inv, ← hD u]
      group
    refine ⟨s0 * InnerDiagA.conjSL D u * s0⁻¹, ?_, h2⟩
    rw [map_mul, map_mul, map_inv, RootPlaneA.toGL_conjSL]
    group
  · obtain ⟨A, hA⟩ := RootPlaneA.exists_gl_of_psiInnerDiag hm hψ hb
    exact ⟨A, fun u => ⟨InnerDiagA.conjSL A u, RootPlaneA.toGL_conjSL A u, hA u⟩⟩

theorem isGLLift_unique_PSL (m : ℕ) (F : Type) [Field F] [CharP F 2] {X : Type}
    [Group X] (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) {b : X} {s s' : GL (Fin (m + 1)) F}
    (hs : IsGLLift Matrix.SpecialLinearGroup.toGL ψ s b)
    (hs' : IsGLLift Matrix.SpecialLinearGroup.toGL ψ s' b) :
    ∃ c : F, ((s'⁻¹ * s : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      Matrix.scalar (Fin (m + 1)) c := by
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_transvectionStruct
    (n := Fin (m + 1)) (R := F)
    (M := ((s'⁻¹ * s : GL (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F))
    (fun t => by
      obtain ⟨i, j, hij, tc⟩ := t
      simpa [Matrix.TransvectionStruct.toMatrix_mk] using
        idPSL_g_commute_transvection ψ hψ hs hs' i j hij tc)
  exact ⟨c, hc.symm⟩

end CFSG.StandardType.ClassicalPosition
