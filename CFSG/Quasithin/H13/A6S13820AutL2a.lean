module

public import CFSG.RankThree.PartOne.KC.EvenSymplecticSL2Automorphisms
public import CFSG.Quasithin.H13.A6S13821z

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
open CFSG.RankThree.PartOne.KCRootAxis (slFieldAut slFieldAut_apply)
open CFSG.QuasithinUnique (IsSylowTwoOf)

namespace Aut20

variable {F : Type} [Field F]

@[expose] def diag2_20 (t : Fˣ) : SpecialLinearGroup (Fin 2) F :=
  ⟨diagonal ![(t : F), ((t⁻¹ : Fˣ) : F)], by
    rw [det_diagonal, Fin.prod_univ_two]
    simp⟩

theorem coe_diag2_20 (t : Fˣ) :
    ((diag2_20 t : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      diagonal ![(t : F), ((t⁻¹ : Fˣ) : F)] := rfl

theorem diag2_20_mem_upperTriangular (t : Fˣ) : diag2_20 t ∈ upperTriangular 2 F :=
  fun i j hij => by rw [coe_diag2_20, diagonal_apply_ne _ (ne_of_gt hij)]

theorem diag2_20_mul (t s : Fˣ) : diag2_20 t * diag2_20 s = diag2_20 (t * s) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_diag2_20, coe_diag2_20, coe_diag2_20,
    diagonal_mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [mul_comm]

theorem diag2_20_one : diag2_20 (1 : Fˣ) = 1 := by
  ext i j
  rw [coe_diag2_20, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp

theorem diag2_20_pow (t : Fˣ) : diag2_20 t ^ 3 = diag2_20 (t ^ 3) := by
  rw [pow_three, diag2_20_mul, diag2_20_mul, ← pow_three]

theorem diag2_20_inv (t : Fˣ) : (diag2_20 t)⁻¹ = diag2_20 t⁻¹ :=
  inv_eq_of_mul_eq_one_right (by rw [diag2_20_mul, mul_inv_cancel, diag2_20_one])

theorem slFieldAut_diag2_20 (σ : F ≃+* F) (t : Fˣ) :
    slFieldAut F σ (diag2_20 t) = diag2_20 (Units.map σ.toRingHom.toMonoidHom t) := by
  ext i j
  rw [slFieldAut_apply, coe_diag2_20, coe_diag2_20]
  fin_cases i <;> fin_cases j <;> simp

theorem eq_one_of_diag2_mem20 {t : Fˣ} (h : diag2_20 t ∈ unitriangular 2 F) : t = 1 := by
  have h1 := (mem_unitriangular.1 h).2 0
  rw [coe_diag2_20, diagonal_apply_eq] at h1
  exact Units.ext h1

theorem comm_mem_unitriangular2_20 {b x : SpecialLinearGroup (Fin 2) F}
    (hb : b ∈ upperTriangular 2 F) (hx : x ∈ upperTriangular 2 F) :
    b * x * b⁻¹ * x⁻¹ ∈ unitriangular 2 F := by
  have hb' := mem_upperTriangular_iff_isUpperTriangular.mp hb
  have hx' := mem_upperTriangular_iff_isUpperTriangular.mp hx
  have hbi := coe_inv_isUpperTriangular hb'
  have hxi := coe_inv_isUpperTriangular hx'
  have hm : b * x * b⁻¹ * x⁻¹ ∈ upperTriangular 2 F :=
    (upperTriangular 2 F).mul_mem ((upperTriangular 2 F).mul_mem
      ((upperTriangular 2 F).mul_mem hb hx) ((upperTriangular 2 F).inv_mem hb))
      ((upperTriangular 2 F).inv_mem hx)
  refine ⟨hm, fun i => ?_⟩
  have h1 : ((b * x : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).IsUpperTriangular :=
    mem_upperTriangular_iff_isUpperTriangular.mp ((upperTriangular 2 F).mul_mem hb hx)
  have h2 : ((b * x * b⁻¹ : SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F).IsUpperTriangular :=
    mem_upperTriangular_iff_isUpperTriangular.mp
      ((upperTriangular 2 F).mul_mem ((upperTriangular 2 F).mul_mem hb hx)
        ((upperTriangular 2 F).inv_mem hb))
  rw [Matrix.SpecialLinearGroup.coe_mul, mul_apply_self_of_isUpperTriangular h2 hxi,
    Matrix.SpecialLinearGroup.coe_mul, mul_apply_self_of_isUpperTriangular h1 hbi,
    Matrix.SpecialLinearGroup.coe_mul, mul_apply_self_of_isUpperTriangular hb' hx']
  have e1 := coe_inv_apply_self_of_isUpperTriangular hb' i
  have e2 := coe_inv_apply_self_of_isUpperTriangular hx' i
  calc (b : Matrix (Fin 2) (Fin 2) F) i i * (x : Matrix (Fin 2) (Fin 2) F) i i *
        ((b⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i i *
        ((x⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i i =
      ((b : Matrix (Fin 2) (Fin 2) F) i i *
          ((b⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i i) *
        ((x : Matrix (Fin 2) (Fin 2) F) i i *
          ((x⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i i) := by ring
    _ = 1 := by rw [e1, e2, one_mul]

theorem mem_normalizer_of_upper2_20 {b : SpecialLinearGroup (Fin 2) F}
    (hb : b ∈ upperTriangular 2 F) :
    b ∈ Subgroup.normalizer (unitriangular 2 F : Set (SpecialLinearGroup (Fin 2) F)) := by
  have key : ∀ c ∈ upperTriangular 2 F, ∀ u ∈ unitriangular 2 F, c * u * c⁻¹ ∈ unitriangular 2 F :=
    fun c hc u hu => by
      have h1 := comm_mem_unitriangular2_20 hc ((unitriangular_le_upperTriangular 2 F) hu)
      have e : c * u * c⁻¹ = c * u * c⁻¹ * u⁻¹ * u := by group
      rw [e]
      exact (unitriangular 2 F).mul_mem h1 hu
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨key b hb u, fun hu => ?_⟩
  have h1 := key b⁻¹ ((upperTriangular 2 F).inv_mem hb) _ hu
  simpa [mul_assoc] using h1

theorem mem_upperTriangular_of_mem_normalizer2_20 {g : SpecialLinearGroup (Fin 2) F}
    (hg : g ∈ Subgroup.normalizer (unitriangular 2 F : Set (SpecialLinearGroup (Fin 2) F))) :
    g ∈ upperTriangular 2 F := by
  let u : SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp [det_fin_two]⟩
  have hu : u ∈ unitriangular 2 F := by
    refine mem_unitriangular.2 ⟨fun i j hij => ?_, fun i => ?_⟩
    · fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | rfl
    · fin_cases i <;> rfl
  have h1 := (Subgroup.mem_normalizer_iff.mp hg u).mp hu
  generalize hu' : g * u * g⁻¹ = u' at h1
  have e : u' * g = g * u := by rw [← hu']; group
  have h2 := congrArg
    (fun M : SpecialLinearGroup (Fin 2) F => (M : Matrix (Fin 2) (Fin 2) F) 1 1) e
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] at h2
  have hu10 := (mem_unitriangular.1 h1).1 1 0 (by decide)
  have hu11 := (mem_unitriangular.1 h1).2 1
  rw [hu10, hu11] at h2
  have hc : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    have h3 : (u : Matrix (Fin 2) (Fin 2) F) 0 1 = 1 := rfl
    have h4 : (u : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := rfl
    rw [h3, h4] at h2
    linear_combination h2.symm
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | exact hc

theorem isSylowTwoOf_U2_20 [Finite F] [CharP F 2] : IsSylowTwoOf (unitriangular 2 F) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_projUnitriangular (K := F) 2 (n := 2) (by norm_num)
  have h1 := CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  rw [hP] at h1
  have h2 := A6S20.isSylowTwoOf_map_top
    (f := (LinearCover.projectiveSLTwoEquivSL F : projectiveSL 2 F →* SpecialLinearGroup (Fin 2) F))
    (LinearCover.projectiveSLTwoEquivSL F).surjective h1
  have h3 : (projUnitriangular 2 F).map
      ((LinearCover.projectiveSLTwoEquivSL F : projectiveSL 2 F →* SpecialLinearGroup (Fin 2) F)) =
        unitriangular 2 F := by
    ext x
    constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      exact hu
    · intro hx
      exact ⟨proj 2 F x, ⟨x, hx, rfl⟩, rfl⟩
  rwa [h3] at h2

end Aut20

end CFSG.Quasithin.H13.A6
