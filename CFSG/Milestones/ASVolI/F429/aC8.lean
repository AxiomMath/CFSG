module

public import CFSG.Milestones.ASVolI.F429.aC3

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

section U4Line

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin.H13.U4Par

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

theorem burnsideF429a_U4_eq_one_of_comm {ω : K} (hω : h.bar ω ≠ ω)
    {d : Matrix.SpecialLinearGroup (Fin 2) K}
    (hd : (d : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, ω]) {g : hypSU h 2 0}
    (hg : g ∈ radQ2 h) (hcomm : g * lev2Hom h d = lev2Hom h d * g) : g = 1 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hg
  have hM : ((g : GL Ix K) : Matrix Ix Ix K) * lev2Mat h d =
      lev2Mat h d * ((g : GL Ix K) : Matrix Ix Ix K) := by
    have := congrArg (fun x : hypSU h 2 0 => ((x : GL Ix K) : Matrix Ix Ix K)) hcomm
    simpa only [coe_mul_hypSU, coe_lev2Hom] using this
  have e11 := congrFun (congrFun hM ie1) if1
  have e12 := congrFun (congrFun hM ie1) if2
  have e21 := congrFun (congrFun hM ie2) if1
  have e22 := congrFun (congrFun hM ie2) if2
  rw [mul_apply, mul_apply, sum_ix, sum_ix] at e11 e12 e21 e22
  simp [lev2Mat_apply, hd, a1, a2, a3, a4, a7, a8, a11, a12] at e11 e12 e21 e22
  have hne : h.bar ω - ω ≠ 0 := sub_ne_zero.2 hω
  have z21 : ((g : GL Ix K) : Matrix Ix Ix K) ie2 if1 = 0 := by
    have : ((g : GL Ix K) : Matrix Ix Ix K) ie2 if1 * (h.bar ω - ω) = 0 := by
      linear_combination e21 + e12
    exact (mul_eq_zero.1 this).resolve_right hne
  have z11 : ((g : GL Ix K) : Matrix Ix Ix K) ie1 if1 = 0 := by
    have : ((g : GL Ix K) : Matrix Ix Ix K) ie1 if1 * (h.bar ω - ω) = 0 := by
      linear_combination e11 + e22 - ω * e12
    exact (mul_eq_zero.1 this).resolve_right hne
  have z22 : ((g : GL Ix K) : Matrix Ix Ix K) ie2 if2 = 0 := by rw [← e12, z11]
  have z12 : ((g : GL Ix K) : Matrix Ix Ix K) ie1 if2 = 0 := by
    linear_combination e11 - h.bar ω * z11 + z21
  apply hypSU_ext
  ext i j
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, z11, z12, z21, z22, one_apply]

theorem burnsideF429a_U4_radQ2_le_perfectCore : radQ2 h ≤ perfectCore (parP2 h) := by
  have := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  have := h.charP
  obtain ⟨ω, hω⟩ := h.exists_bar_ne
  set d : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨!![0, 1; 1, ω], by simp [det_fin_two_of, CharTwo.neg_eq]⟩ with hd
  set t := lev2Hom h d with ht
  have htC : t ∈ perfectCore (parP2 h) := lev2Hom_range_le_perfectCore h ⟨d, rfl⟩
  have htP : t ∈ parP2 h := lev2Hom_le_parP2 h ⟨d, rfl⟩
  have hmaps : ∀ x ∈ radQ2 h, x * t * x⁻¹ * t⁻¹ ∈ radQ2 h := fun x hx => by
    have h1 : t * x⁻¹ * t⁻¹ ∈ radQ2 h :=
      (Subgroup.mem_normalizer_iff.mp (parP2_le_normalizer_radQ2 h htP) x⁻¹).mp
        ((radQ2 h).inv_mem hx)
    have e : x * t * x⁻¹ * t⁻¹ = x * (t * x⁻¹ * t⁻¹) := by group
    rw [e]
    exact (radQ2 h).mul_mem hx h1
  let φ : ↥(radQ2 h) → ↥(radQ2 h) := fun x =>
    ⟨(x : hypSU h 2 0) * t * (x : hypSU h 2 0)⁻¹ * t⁻¹, hmaps x x.2⟩
  have hφ : Function.Injective φ := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hxy
    have e : a * t * a⁻¹ * t⁻¹ = b * t * b⁻¹ * t⁻¹ := congrArg Subtype.val hxy
    have hz : b⁻¹ * a ∈ radQ2 h := (radQ2 h).mul_mem ((radQ2 h).inv_mem hb) ha
    have hc : b⁻¹ * a * t = t * (b⁻¹ * a) := by
      calc b⁻¹ * a * t = b⁻¹ * (a * t * a⁻¹ * t⁻¹) * t * a := by group
        _ = b⁻¹ * (b * t * b⁻¹ * t⁻¹) * t * a := by rw [e]
        _ = t * (b⁻¹ * a) := by group
    have h1 := burnsideF429a_U4_eq_one_of_comm h hω (d := d) rfl hz hc
    apply Subtype.ext
    show a = b
    calc a = b * (b⁻¹ * a) := by group
      _ = b := by rw [h1, mul_one]
  intro z hz
  obtain ⟨⟨a, ha⟩, hx⟩ := Finite.surjective_of_injective hφ ⟨z, hz⟩
  have e : z = a * t * a⁻¹ * t⁻¹ := (congrArg Subtype.val hx).symm
  rw [e]
  have hxN : a ∈ Subgroup.normalizer (perfectCore (parP2 h) : Set (hypSU h 2 0)) :=
    (Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore (parP2 h)))
      (radQ2_le_parP2 h ha)
  exact (perfectCore (parP2 h)).mul_mem ((Subgroup.mem_normalizer_iff.mp hxN t).mp htC)
    ((perfectCore (parP2 h)).inv_mem htC)

theorem burnsideF429a_U4_U_le_perfectCore_parP2 :
    hypUnitriangular h 2 0 ≤ perfectCore (parP2 h) :=
  (hypUnitriangular_le_parH2 h).trans ((parH2_le_radQ2_sup h).trans
    (sup_le (burnsideF429a_U4_radQ2_le_perfectCore h) (lev2Hom_range_le_perfectCore h)))

end U4Line

section U4Two

open CFSG.ClassicalGroups.UnitaryFlag CFSG.Quasithin.H13.U4Par

theorem burnsideF429a_U4_line {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .U4 2 f Gp M₁ M₂) :
    pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₂) ∧
      oPPrime 2 (Gp ⊓ M₂) = perfectCore (Gp ⊓ M₂) := by
  haveI := hyp.finite
  obtain ⟨marking, -, h2⟩ := burnsideF4g_marking (c := .U4) hyp.toHypF_4_4g
  obtain ⟨Φ, -, e2⟩ := burnsideF4gU4_exists_equiv marking
  obtain ⟨hS2, -, hS⟩ := burnsideF429a_sbar Gp M₁ M₂
  obtain ⟨k, e⟩ := burnsideF429a_of_model Φ (h2.trans e2) (isSylowTwoOf_hypUnitriangular _)
    (burnsideF429a_U4_U_le_perfectCore_parP2 _)
  exact ⟨k _ hS hS2, e⟩

theorem burnsideF429a_c8_U4two {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .U4 2 1 Gp M₁ M₂) :
    pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₁) ∨
      pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₂) :=
  Or.inr (burnsideF429a_U4_line hyp).1

end U4Two

end CFSG.ASVolI
