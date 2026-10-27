module

public import CFSG.RankThree.PartTwo.KFacts.AutPSU
import CFSG.RankThree.PartTwo.KFacts.K71SU3AutFacts
import CFSG.RankThree.PartTwo.Sec4.RonanK432RowL3OuterUni
import CFSG.RankThree.PartTwo.Sec13.Ronan138WOutAbCube
import CFSG.RankThree.PartTwo.Sec13.Ronan138WOutAbPSL

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138W

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open Matrix

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}

theorem exists_psuConj_psuField_of_pow (hq : 2 < p ^ f) {α : MulAut (unitaryPSU h 3)} {k : ℕ}
    (hα : α ^ 3 ^ k = 1) :
    ∃ (A : unitaryIsom3 h) (σ : K ≃+* K), σ ^ 3 ^ k = 1 ∧ α = psuConj h A * psuField h σ := by
  obtain ⟨A, σ, rfl⟩ := exists_psuConj_mul_psuField hq α
  refine ⟨A, σ, ?_, rfl⟩
  obtain ⟨B, hB⟩ := exists_psuConj_mul_psuField_pow h A σ (3 ^ k)
  rw [hα] at hB
  exact (eq_one_of_psuConj_mul_psuField_eq_one B _ hB.symm).1

theorem det_mem_rootsOfUnity (A : unitaryIsom3 h) :
    GeneralLinearGroup.det (A : GL (Fin 3) K) ∈ rootsOfUnity (p ^ f + 1) K := by
  rw [mem_rootsOfUnity]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, GeneralLinearGroup.val_det_apply, pow_succ]
  have h1 := congrArg Matrix.det (mem_unitaryIsom3.mp A.2)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h1
  have h2 : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar =
      (h.bar : K →+* K).mapMatrix ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := rfl
  rw [h2, ← RingHom.map_det, h.bar_apply] at h1
  exact h1

theorem psuConj_mem_range_conj_of_cube {C : unitaryIsom3 h} {c : Kˣ}
    (hcμ : c ∈ rootsOfUnity (p ^ f + 1) K)
    (hc : c ^ 3 = GeneralLinearGroup.det (C : GL (Fin 3) K)) :
    psuConj h C ∈ (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range := by
  have hcn : h.bar ((c⁻¹ : Kˣ) : K) * ((c⁻¹ : Kˣ) : K) = 1 := by
    have h1 := congrArg Units.val ((mem_rootsOfUnity _ _).mp (inv_mem hcμ))
    rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ] at h1
    rw [h.bar_apply]
    exact h1
  have hs : GeneralLinearGroup.scalar (Fin 3) c⁻¹ ∈ unitaryIsom3 h := by
    rw [mem_unitaryIsom3, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    rw [show (fun _ : Fin 3 => h.bar ((c⁻¹ : Kˣ) : K) * ((c⁻¹ : Kˣ) : K)) = fun _ => (1 : K) from
      funext fun _ => hcn]
    exact Matrix.diagonal_one
  set D : unitaryIsom3 h := C * ⟨_, hs⟩ with hD
  have hDdet : GeneralLinearGroup.det (D : GL (Fin 3) K) = 1 := by
    rw [hD, Subgroup.coe_mul, map_mul, ← hc, GeneralLinearGroup.det_scalar, Fintype.card_fin,
      inv_pow, mul_inv_cancel]
  have hDSU : (D : GL (Fin 3) K) ∈ unitarySU p f K 3 := by
    rw [mem_unitarySU_iff h]
    refine ⟨?_, mem_unitaryIsom3.mp D.2⟩
    have := congrArg Units.val hDdet
    rwa [GeneralLinearGroup.val_det_apply, Units.val_one] at this
  refine ⟨((⟨_, hDSU⟩ : unitarySU p f K 3) : unitaryPSU h 3), ?_⟩
  rw [conj_mk_eq_psuConj]
  have hDeq : (⟨(D : GL (Fin 3) K), unitarySU_le_unitaryIsom3 hDSU⟩ : unitaryIsom3 h) = D := rfl
  rw [hDeq, hD, map_mul]
  have h1 : psuConj h ⟨_, hs⟩ = 1 :=
    (CFSG.RankThree.PartTwo.Sec4.RonanK432.L3Outer.psuConj_eq_one_iff _).mpr
      (CFSG.RankThree.PartTwo.Sec4.mk_eq_one_iff_mem_statedScalars.mpr ⟨c⁻¹, rfl⟩)
  rw [h1, mul_one]

theorem map_mem_rootsOfUnity (σ : K ≃+* K) {x : Kˣ} (hx : x ∈ rootsOfUnity (p ^ f + 1) K) :
    Units.map (σ : K →* K) x ∈ rootsOfUnity (p ^ f + 1) K := by
  rw [mem_rootsOfUnity] at hx ⊢
  rw [← map_pow, hx, map_one]

theorem exists_cube_eq_map_mul_inv_mu [Finite K] {σ : K ≃+* K} {k : ℕ} (hσ : σ ^ 3 ^ k = 1)
    {b : Kˣ} (hb : b ∈ rootsOfUnity (p ^ f + 1) K) :
    ∃ c ∈ rootsOfUnity (p ^ f + 1) K, c ^ 3 = Units.map (σ : K →* K) b * b⁻¹ := by
  haveI : NeZero (p ^ f + 1) := ⟨by omega⟩
  haveI : IsCyclic (rootsOfUnity (p ^ f + 1) K) := rootsOfUnity.isCyclic K _
  set μ := rootsOfUnity (p ^ f + 1) K
  let F : μ →* μ :=
    { toFun := fun x => ⟨Units.map (σ : K →* K) x, map_mem_rootsOfUnity σ x.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ _ _) }
  obtain ⟨c, hc⟩ := exists_cube_eq_mul_inv_of_cyclic F (fun y hy => by
    apply Subtype.ext
    apply Units.ext
    change σ ((y : Kˣ) : K) = ((y : Kˣ) : K)
    have h1 := congrArg (fun z : μ => ((z : Kˣ) : K)) hy
    simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one,
      Units.val_one] at h1
    exact apply_eq_of_pow_three_eq_one hσ h1) ⟨b, hb⟩
  refine ⟨c, c.2, ?_⟩
  have := congrArg Subtype.val hc
  simpa [F] using this

theorem comm_mem_range_conj_of_pow_psu [Finite K] (hq : 2 < p ^ f)
    {α β : MulAut (unitaryPSU h 3)} {a b : ℕ} (hα : α ^ 3 ^ a = 1) (hβ : β ^ 3 ^ b = 1) :
    α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range := by
  obtain ⟨A, σ, hσ, rfl⟩ := exists_psuConj_psuField_of_pow hq hα
  obtain ⟨B, τ, hτ, rfl⟩ := exists_psuConj_psuField_of_pow hq hβ
  have h1 := psuConj_mul_psuField_mul (h := h) A B σ τ
  have h2 := psuConj_mul_psuField_mul (h := h) B A τ σ
  rw [ringAut_comm_of_finite τ σ] at h2
  have e1 : psuConj h A * psuField h σ * (psuConj h B * psuField h τ) *
      (psuConj h A * psuField h σ)⁻¹ * (psuConj h B * psuField h τ)⁻¹ =
      (psuConj h A * psuField h σ * (psuConj h B * psuField h τ)) *
        (psuConj h B * psuField h τ * (psuConj h A * psuField h σ))⁻¹ := by group
  rw [e1, h1, h2]
  set A' : unitaryIsom3 h := A * ⟨glAut σ B, glAut_mem_unitaryIsom3 σ B.2⟩ with hA'
  set B' : unitaryIsom3 h := B * ⟨glAut τ A, glAut_mem_unitaryIsom3 τ A.2⟩ with hB'
  have e2 : psuConj h A' * psuField h (σ * τ) * (psuConj h B' * psuField h (σ * τ))⁻¹ =
      psuConj h A' * (psuConj h B')⁻¹ := by group
  rw [e2, ← map_inv, ← map_mul]
  have hdA := det_mem_rootsOfUnity A
  have hdB := det_mem_rootsOfUnity B
  obtain ⟨c₁, hc₁μ, hc₁⟩ := exists_cube_eq_map_mul_inv_mu hσ hdB
  obtain ⟨c₂, hc₂μ, hc₂⟩ := exists_cube_eq_map_mul_inv_mu hτ hdA
  refine psuConj_mem_range_conj_of_cube (c := c₁ * c₂⁻¹)
    (mul_mem hc₁μ (inv_mem hc₂μ)) ?_
  have hglA : GeneralLinearGroup.det (glAut τ (A : GL (Fin 3) K)) =
      Units.map (τ : K →* K) (GeneralLinearGroup.det (A : GL (Fin 3) K)) := by
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, Units.coe_map, GeneralLinearGroup.val_det_apply,
      coe_glAut]
    exact (RingHom.map_det (τ : K →+* K) _).symm
  have hglB : GeneralLinearGroup.det (glAut σ (B : GL (Fin 3) K)) =
      Units.map (σ : K →* K) (GeneralLinearGroup.det (B : GL (Fin 3) K)) := by
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, Units.coe_map, GeneralLinearGroup.val_det_apply,
      coe_glAut]
    exact (RingHom.map_det (σ : K →+* K) _).symm
  rw [mul_pow, inv_pow, hc₁, hc₂, hA', hB', Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul,
    Subgroup.coe_mul, map_mul, map_inv, map_mul, map_mul]
  change _ = GeneralLinearGroup.det (A : GL (Fin 3) K) *
    GeneralLinearGroup.det (glAut σ (B : GL (Fin 3) K)) *
    (GeneralLinearGroup.det (B : GL (Fin 3) K) *
      GeneralLinearGroup.det (glAut τ (A : GL (Fin 3) K)))⁻¹
  rw [hglA, hglB]
  simp only [_root_.mul_inv_rev, inv_inv, mul_comm, mul_left_comm, mul_assoc]

end CFSG.RankThree.PartTwo.Sec13.Ronan138W
