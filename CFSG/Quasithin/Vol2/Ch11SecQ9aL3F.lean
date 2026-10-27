module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aL3E
public import CFSG.Quasithin.Vol2.Ch11SecQ9aCartD
public import CFSG.Quasithin.Vol2.Ch11SecQ9aCartE

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LieType.SteinbergBR.BlockPar CFSG.ClassicalInvolution.ModelFacts.OddCover
open scoped commutatorElement

variable {F : Type} [Field F]

instance instFinitePGL3 [Finite F] : Finite (PGL3 F) :=
  have : Finite (GL (Fin 3) F) :=
    Finite.of_injective (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F))
      fun _ _ h => Units.ext h
  Finite.of_surjective _ ProjGenLinGroup.mk_surjective

theorem three_eq_one [CharP F 2] : (3 : F) = 1 := by
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  linear_combination h2

theorem uSL_mem_unitriangular (a b c : F) : uSL a b c ∈ unitriangular 3 F :=
  usl_eq_unitriangular (K := F) ▸ uSL_mem_Usl a b c

theorem conj_unitriangular [CharP F 2] {g : GL (Fin 3) F}
    (hg : ProjGenLinGroup.mk g ∈ Subgroup.normalizer (S0P F : Set (PGL3 F)))
    {u : SpecialLinearGroup (Fin 3) F} (hu : u ∈ unitriangular 3 F) :
    ∃ u' ∈ unitriangular 3 F,
      SpecialLinearGroup.toGL u * g = g * SpecialLinearGroup.toGL u' := by
  have hg' := Subgroup.inv_mem _ hg
  have h1 := (Subgroup.mem_normalizer_iff.mp hg'
    (ProjGenLinGroup.mk (SpecialLinearGroup.toGL u))).mp ⟨proj 3 F u, ⟨u, hu, rfl⟩, rfl⟩
  obtain ⟨_, ⟨u', hu', rfl⟩, hv⟩ := h1
  rw [thetaP_proj, inv_inv, ← map_inv, ← map_mul, ← map_mul, ProjGenLinGroup.mk_eq_mk_iff] at hv
  obtain ⟨c, hc⟩ := hv
  have htr := congrArg (fun A : GL (Fin 3) F => Matrix.trace (A : Matrix (Fin 3) (Fin 3) F)) hc
  have e1 : Matrix.trace (((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      (u : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F)) =
      Matrix.trace (u : Matrix (Fin 3) (Fin 3) F) := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, SpecialLinearGroup.coe_GL_coe_matrix,
    e1] at htr
  simp only [Matrix.trace_fin_three, Matrix.scalar_apply, Matrix.mul_diagonal, hu.2, hu'.2]
    at htr
  have hc1 : (c : F) = 1 := by
    have h3 := three_eq_one (F := F)
    linear_combination htr - (c : F) * h3 + h3
  have hc' : c = 1 := Units.ext hc1
  subst hc'
  rw [map_one, mul_one] at hc
  exact ⟨u', hu', by rw [hc]; group⟩

theorem isUpperTriangular_of_mem_normalizer [CharP F 2] {g : GL (Fin 3) F}
    (hg : ProjGenLinGroup.mk g ∈ Subgroup.normalizer (S0P F : Set (PGL3 F))) :
    (g : Matrix (Fin 3) (Fin 3) F).IsUpperTriangular := by
  obtain ⟨u₁, hu₁, h₁⟩ := conj_unitriangular hg (uSL_mem_unitriangular (1 : F) 0 0)
  obtain ⟨u₂, hu₂, h₂⟩ := conj_unitriangular hg (uSL_mem_unitriangular (0 : F) 0 1)
  have e₁ := congrArg (fun A : GL (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F)) h₁
  have e₂ := congrArg (fun A : GL (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F)) h₂
  simp only [Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix, coe_uSL] at e₁ e₂
  have a1 := congrFun (congrFun e₁ 0) 0
  have a2 := congrFun (congrFun e₂ 1) 0
  have a3 := congrFun (congrFun e₂ 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three, uMat, hu₁.1 1 0 (by decide),
    hu₁.1 2 0 (by decide), hu₁.2 0, hu₂.1 1 0 (by decide), hu₂.1 2 0 (by decide), hu₂.2 0,
    hu₂.2 1, hu₂.1 2 1 (by decide)] at a1 a2 a3
  have h10 : (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 := a1
  have h20 : (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 := by simpa [h10] using a2
  have h21 : (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by simpa [h10] using a3
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

theorem mulVec_mem_flagSpace {A : Matrix (Fin 3) (Fin 3) F} (hA : A.IsUpperTriangular) {d : ℕ}
    {v : Fin 3 → F} (hv : v ∈ flagSpace 3 F d) : A *ᵥ v ∈ flagSpace 3 F d := by
  rw [mem_flagSpace] at hv ⊢
  intro k hk
  rw [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : (l : ℕ) < d
  · rw [hA (show id l < id k from Fin.lt_def.mpr (by simp only [id]; omega)),
      zero_mul]
  · rw [hv l (not_lt.mp hl), mul_zero]

theorem exists_conj_stabilizer {g : GL (Fin 3) F}
    (hg : (g : Matrix (Fin 3) (Fin 3) F).IsUpperTriangular)
    (hg' : ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsUpperTriangular) {d : ℕ}
    {M : SpecialLinearGroup (Fin 3) F} (hM : M ∈ stabilizer (flagSpace 3 F d)) :
    ∃ M' ∈ stabilizer (flagSpace 3 F d),
      SpecialLinearGroup.toGL M' = g * SpecialLinearGroup.toGL M * g⁻¹ := by
  have hdet : ((g * SpecialLinearGroup.toGL M * g⁻¹ : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F).det = 1 := by
    rw [← GeneralLinearGroup.val_det_apply, map_mul, map_mul, map_inv,
      SpecialLinearGroup.coeToGL_det, mul_one, mul_inv_cancel, Units.val_one]
  refine ⟨⟨_, hdet⟩, mem_stabilizer_of_map_le ?_, Units.ext rfl⟩
  rintro _ ⟨v, hv, rfl⟩
  rw [mem_stabilizer] at hM
  change ((g * SpecialLinearGroup.toGL M * g⁻¹ : GL (Fin 3) F) :
    Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ _
  simp only [Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix]
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  refine mulVec_mem_flagSpace hg ?_
  rw [← hM]
  exact Submodule.mem_map_of_mem (mulVec_mem_flagSpace hg' hv)

theorem normalizer_S0P_le [CharP F 2] (j : Fin 2) :
    Subgroup.normalizer (S0P F : Set (PGL3 F)) ≤
      Subgroup.normalizer (Ptheta F j : Set (PGL3 F)) := by
  have key : ∀ x ∈ Subgroup.normalizer (S0P F : Set (PGL3 F)), ∀ m ∈ Ptheta F j,
      x * m * x⁻¹ ∈ Ptheta F j := by
    intro x hx m hm
    obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective x
    have hg := isUpperTriangular_of_mem_normalizer hx
    have hg' := isUpperTriangular_of_mem_normalizer (g := g⁻¹)
      (by rw [map_inv]; exact Subgroup.inv_mem _ hx)
    obtain ⟨_, ⟨M, hM, rfl⟩, rfl⟩ := hm
    obtain ⟨M', hM', he⟩ := exists_conj_stabilizer hg hg' hM
    refine ⟨proj 3 F M', ⟨M', hM', rfl⟩, ?_⟩
    rw [thetaP_proj, thetaP_proj, he, map_mul, map_mul, map_inv]
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro m
  refine ⟨key x hx m, fun h => ?_⟩
  have := key x⁻¹ (Subgroup.inv_mem _ hx) _ h
  rwa [inv_inv, show x⁻¹ * (x * m * x⁻¹) * x = m by group] at this

theorem exists_comm_radU {W : Submodule F (Fin 3 → F)} {D : GL (Fin 3) F} {a b : F}
    (ha : a ≠ 0) (hb : b ≠ 0) (hDW : ∀ w ∈ W, (D : Matrix (Fin 3) (Fin 3) F) *ᵥ w = a • w)
    (hDV : ∀ v, (D : Matrix (Fin 3) (Fin 3) F) *ᵥ v - b • v ∈ W)
    {M : SpecialLinearGroup (Fin 3) F} (hM : M ∈ stabilizer W) :
    ∃ r ∈ radU F W, SpecialLinearGroup.toGL r =
      D * SpecialLinearGroup.toGL M * D⁻¹ * (SpecialLinearGroup.toGL M)⁻¹ := by
  set Dm := (D : Matrix (Fin 3) (Fin 3) F) with hDm
  set Di := ((D⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hDi
  set Mm := (M : Matrix (Fin 3) (Fin 3) F) with hMm
  set Mi := ((M⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hMi
  have hDDi : Dm * Di = 1 := Units.mul_inv D
  have hDiD : Di * Dm = 1 := Units.inv_mul D
  have hMMi : Mm * Mi = 1 := by
    show ((M * M⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1
    rw [mul_inv_cancel]
    rfl
  have hMW : ∀ w ∈ W, Mm *ᵥ w ∈ W := fun w hw => by
    rw [mem_stabilizer] at hM
    rw [← hM]
    exact Submodule.mem_map_of_mem hw
  have hMiW : ∀ w ∈ W, Mi *ᵥ w ∈ W := fun w hw => by
    have hM' := Subgroup.inv_mem _ hM
    rw [mem_stabilizer] at hM'
    rw [← hM']
    exact Submodule.mem_map_of_mem hw
  have hDiW : ∀ w ∈ W, Di *ᵥ w = a⁻¹ • w := fun w hw => by
    have h1 : Dm *ᵥ (a⁻¹ • w) = w := by
      rw [mulVec_smul, hDW w hw, smul_smul, inv_mul_cancel₀ ha, one_smul]
    rw [← h1, mulVec_mulVec, hDiD, one_mulVec, h1]
  have hDiV : ∀ u, Di *ᵥ u - b⁻¹ • u ∈ W := fun u => by
    have h1 := W.smul_mem (-b⁻¹) (hDV (Di *ᵥ u))
    rw [mulVec_mulVec, hDDi, one_mulVec] at h1
    convert h1 using 1
    simp only [smul_sub, smul_smul, neg_mul, inv_mul_cancel₀ hb, neg_smul, one_smul]
    abel
  set X : GL (Fin 3) F := D * SpecialLinearGroup.toGL M * D⁻¹ * (SpecialLinearGroup.toGL M)⁻¹
    with hX
  have hdet : (X : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    rw [← GeneralLinearGroup.val_det_apply, hX, map_mul, map_mul, map_mul, map_inv, map_inv,
      SpecialLinearGroup.coeToGL_det, inv_one, mul_one, mul_one, mul_inv_cancel, Units.val_one]
  have hXm : (X : Matrix (Fin 3) (Fin 3) F) = Dm * Mm * Di * Mi := by
    rw [hX, ← map_inv]
    simp only [Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix, hDm, hDi, hMm, hMi]
  let r : SpecialLinearGroup (Fin 3) F := ⟨X, hdet⟩
  refine ⟨r, ?_, Units.ext rfl⟩
  rw [mem_radU]
  change (∀ v, (X : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v ∈ W) ∧
    ∀ w ∈ W, (X : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w
  rw [hXm]
  refine ⟨fun v => ?_, fun w hw => ?_⟩
  · have hyv : Mm *ᵥ (Di *ᵥ (Mi *ᵥ v)) - b⁻¹ • v ∈ W := by
      have h1 := hMW _ (hDiV (Mi *ᵥ v))
      have e : Mm *ᵥ (Di *ᵥ (Mi *ᵥ v) - b⁻¹ • (Mi *ᵥ v)) =
          Mm *ᵥ (Di *ᵥ (Mi *ᵥ v)) - b⁻¹ • v := by
        have hv' : Mm *ᵥ (Mi *ᵥ v) = v := by rw [mulVec_mulVec, hMMi, one_mulVec]
        rw [mulVec_sub, mulVec_smul, hv']
      rwa [e] at h1
    have h2 := W.add_mem (hDV (Mm *ᵥ (Di *ᵥ (Mi *ᵥ v)))) (W.smul_mem b hyv)
    have e2 : (Dm * Mm * Di * Mi) *ᵥ v - v =
        (Dm *ᵥ (Mm *ᵥ (Di *ᵥ (Mi *ᵥ v))) - b • (Mm *ᵥ (Di *ᵥ (Mi *ᵥ v)))) +
          b • (Mm *ᵥ (Di *ᵥ (Mi *ᵥ v)) - b⁻¹ • v) := by
      rw [← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, smul_sub, smul_smul,
        mul_inv_cancel₀ hb, one_smul]
      abel
    rw [e2]
    exact h2
  · rw [← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hDiW _ (hMiW w hw), mulVec_smul,
      mulVec_mulVec, hMMi, one_mulVec, mulVec_smul, hDW w hw, smul_smul, inv_mul_cancel₀ ha,
      one_smul]

variable [Finite F]

theorem mk_mem_sectionCentralizer [CharP F 2] (hF : Nat.card F = 4) (j : Fin 2)
    {g : GL (Fin 3) F}
    (hg : ProjGenLinGroup.mk g ∈ Subgroup.normalizer (S0P F : Set (PGL3 F))) {a b : F}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hW : ∀ w ∈ flagSpace 3 F ((j : ℕ) + 1), (g : Matrix (Fin 3) (Fin 3) F) *ᵥ w = a • w)
    (hV : ∀ v, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v - b • v ∈ flagSpace 3 F ((j : ℕ) + 1)) :
    ProjGenLinGroup.mk g ∈ sectionCentralizer (Ptheta F j) (pCoreOf 2 (Ptheta F j)) := by
  have hN := normalizer_S0P_le j hg
  refine ⟨hN, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hN, ?_⟩
  rintro _ ⟨_, ⟨M, hM, rfl⟩, rfl⟩
  obtain ⟨r, hr, hre⟩ := exists_comm_radU ha hb hW hV hM
  rw [pCoreOf_map_of_injective (thetaP F) thetaP_injective, pCoreOf_parab34 hF j]
  refine ⟨proj 3 F r, ⟨r, hr, rfl⟩, ?_⟩
  rw [thetaP_proj, thetaP_proj, hre, map_mul, map_mul, map_mul, map_inv, map_inv]

end CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
