module

public import CFSG.Quasithin.EmptyFaithful.SzN24Gen
public import CFSG.Quasithin.EmptyFaithful.SzN2Lin
public import CFSG.RankThree.PartTwo.KFacts.AutPSLOrderThree

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

namespace SzN24

section Lin

variable {F : Type} [Field F]

theorem units_cube_eq_one {Ŝ : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (h4 : ∀ b ∈ Subgroup.normalizer (Ŝ : Set (SpecialLinearGroup (Fin 3) F)), orderOf b ≠ 3)
    {c : Fˣ} (hc : c ^ 3 = 1) : c = 1 := by
  by_contra hne
  have hmem : scalarElement c hc ∈ Subgroup.normalizer (Ŝ : Set (SpecialLinearGroup (Fin 3) F)) := by
    have : scalarElement c hc ∈ Subgroup.center (SpecialLinearGroup (Fin 3) F) := by
      rw [← scalars_eq_center]
      exact scalarElement_mem_scalars c hc
    exact Subgroup.center_le_normalizer _ this
  apply h4 _ hmem
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply orderOf_eq_prime
  · apply Subtype.ext
    show (scalar (Fin 3) (c : F)) ^ 3 = 1
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hc, Units.val_one, map_one]
  · intro h1
    apply hne
    have := congrArg (fun A : SpecialLinearGroup (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F) 0 0) h1
    simpa [scalarElement] using this

theorem exists_cube_eq [Finite F] (hcube : ∀ c : Fˣ, c ^ 3 = 1 → c = 1) (δ : Fˣ) :
    ∃ l : Fˣ, l ^ 3 = δ := by
  have hinj : Function.Injective (fun x : Fˣ => x ^ 3) := by
    intro x y hxy
    have h1 : (x * y⁻¹) ^ 3 = 1 := by
      have : x ^ 3 = y ^ 3 := hxy
      rw [mul_pow, inv_pow, this, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hcube _ h1)
  exact Finite.injective_iff_surjective.mp hinj δ

theorem inner_of_descendAut_eq_conjAut [Finite F] (hscal : ∀ A ∈ scalars 3 F, A = 1)
    (hcube : ∀ c : Fˣ, c ^ 3 = 1 → c = 1) (α : MulAut (SpecialLinearGroup (Fin 3) F))
    (H : GL (Fin 3) F) (h : descendAut 3 F α = CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 F H) :
    ∃ x : SpecialLinearGroup (Fin 3) F, ∀ m, α m = x * m * x⁻¹ := by
  have hα : ∀ g, α g =
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F H g := by
    intro g
    have h1 : proj 3 F (α g) = proj 3 F
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F H g) := by
      rw [← descendAut_proj, h, conjAut_proj]
    exact inv_mul_eq_one.mp (hscal _ (proj_eq_proj_iff.mp h1)) |>.symm |>.symm
  obtain ⟨l, hl⟩ := exists_cube_eq hcube (GeneralLinearGroup.det H)
  have hdet : (((l⁻¹ : Fˣ) : F) • (H : Matrix (Fin 3) (Fin 3) F)).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, ← Units.val_pow_eq_pow_val, inv_pow, hl,
      ← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.inv_mul _
  let A : SpecialLinearGroup (Fin 3) F := ⟨((l⁻¹ : Fˣ) : F) • (H : Matrix (Fin 3) (Fin 3) F), hdet⟩
  refine ⟨A, fun m => ?_⟩
  rw [hα]
  apply mul_right_cancel (b := A)
  have e1 : A * m * A⁻¹ * A = A * m := by group
  rw [e1]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.coe_slConjugation]
  show (H : Matrix (Fin 3) (Fin 3) F) * (m : Matrix (Fin 3) (Fin 3) F) *
      ((H⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        (((l⁻¹ : Fˣ) : F) • (H : Matrix (Fin 3) (Fin 3) F)) =
    (((l⁻¹ : Fˣ) : F) • (H : Matrix (Fin 3) (Fin 3) F)) * (m : Matrix (Fin 3) (Fin 3) F)
  rw [Matrix.mul_smul, Matrix.smul_mul, mul_assoc, mul_assoc, Units.inv_mul, mul_one]

@[expose] def dSL3 (a : F) (ha : a ≠ 0) : SpecialLinearGroup (Fin 3) F :=
  ⟨Matrix.diagonal ![a, a⁻¹, 1], by simp [Matrix.det_diagonal, Fin.prod_univ_three, ha]⟩

theorem dSL3_mem_upperTriangular (a : F) (ha : a ≠ 0) : dSL3 a ha ∈ upperTriangular 3 F := by
  intro i j hij
  show (Matrix.diagonal ![a, a⁻¹, 1] : Matrix (Fin 3) (Fin 3) F) i j = 0
  exact Matrix.diagonal_apply_ne _ (ne_of_gt hij)

theorem trace_mul_dSL3 (a : F) (ha : a ≠ 0) {u : SpecialLinearGroup (Fin 3) F}
    (hu : u ∈ unitriangular 3 F) :
    ((u * dSL3 a ha : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).trace =
      a + a⁻¹ + 1 := by
  rw [Matrix.SpecialLinearGroup.coe_mul]
  show (Matrix.trace ((u : Matrix (Fin 3) (Fin 3) F) * Matrix.diagonal ![a, a⁻¹, 1])) = _
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal, hu.2, one_mul, Fin.sum_univ_three]
  simp

theorem trace_dSL3 (a : F) (ha : a ≠ 0) :
    ((dSL3 a ha : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).trace = a + a⁻¹ + 1 := by
  show Matrix.trace (Matrix.diagonal ![a, a⁻¹, 1]) = _
  simp [Matrix.trace, Fin.sum_univ_three]

theorem trace_conj_SL (x m : SpecialLinearGroup (Fin 3) F) :
    ((x * m * x⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).trace =
      (m : Matrix (Fin 3) (Fin 3) F).trace := by
  have h' : ((x⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      (x : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, mul_assoc,
    Matrix.trace_mul_comm, mul_assoc, h', mul_one]

end Lin

section Main

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem sl3_field_eq_one {Ŝ : Subgroup (SpecialLinearGroup (Fin 3) F)} (hŜ : IsSylowTwoOf Ŝ ⊤)
    (α : SpecialLinearGroup (Fin 3) F ≃* SpecialLinearGroup (Fin 3) F)
    (h2 : ∀ b ∈ Subgroup.normalizer (Ŝ : Set (SpecialLinearGroup (Fin 3) F)), α b * b⁻¹ ∈ Ŝ)
    (σ : F ≃+* F) (hσ3 : ∀ a, σ (σ (σ a)) = a)
    (htr : ∀ g : SpecialLinearGroup (Fin 3) F,
      ((α g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).trace =
        σ ((g : Matrix (Fin 3) (Fin 3) F).trace)) : σ = 1 := by
  have hU : IsSylowTwoOf (unitriangular 3 F) ⊤ := SzN2.isSylowTwoOf_unitriangular (by norm_num)
  obtain ⟨x, -, hx⟩ := B6.isSylowTwoOf_exists_conj hU hŜ
  have hmem : ∀ s, s ∈ Ŝ ↔ x⁻¹ * s * x ∈ unitriangular 3 F := by
    intro s
    rw [hx]
    constructor
    · rintro ⟨u, hu, rfl⟩
      show x⁻¹ * (x * u * x⁻¹) * x ∈ unitriangular 3 F
      rw [show x⁻¹ * (x * u * x⁻¹) * x = u by group]
      exact hu
    · intro hs
      refine ⟨x⁻¹ * s * x, hs, ?_⟩
      show x * (x⁻¹ * s * x) * x⁻¹ = s
      group
  refine eq_one_of_trace_eq hσ3 (fun a ha => ?_)
  have hd : dSL3 a ha ∈ Subgroup.normalizer
      ((unitriangular 3 F : Subgroup (SpecialLinearGroup (Fin 3) F)) :
        Set (SpecialLinearGroup (Fin 3) F)) := by
    rw [normalizer_unitriangular]
    exact dSL3_mem_upperTriangular a ha
  have hd' : x * dSL3 a ha * x⁻¹ ∈ Subgroup.normalizer (Ŝ : Set (SpecialLinearGroup (Fin 3) F)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    rw [hmem, hmem]
    have h1 := Subgroup.mem_normalizer_iff.mp hd (x⁻¹ * s * x)
    have e : x⁻¹ * (x * dSL3 a ha * x⁻¹ * s * (x * dSL3 a ha * x⁻¹)⁻¹) * x =
        dSL3 a ha * (x⁻¹ * s * x) * (dSL3 a ha)⁻¹ := by group
    rw [e]
    exact h1
  have hs := (hmem _).mp (h2 _ hd')
  set u : SpecialLinearGroup (Fin 3) F :=
    x⁻¹ * (α (x * dSL3 a ha * x⁻¹) * (x * dSL3 a ha * x⁻¹)⁻¹) * x with hu
  have e2 : α (x * dSL3 a ha * x⁻¹) = x * (u * dSL3 a ha) * x⁻¹ := by
    rw [hu]
    group
  have h3 := htr (x * dSL3 a ha * x⁻¹)
  rw [e2, trace_conj_SL, trace_mul_dSL3 a ha hs, trace_conj_SL, trace_dSL3] at h3
  rw [map_add, map_add, map_inv₀, map_one] at h3
  linear_combination -h3

theorem sl3_autRigid {Ŝ : Subgroup (SpecialLinearGroup (Fin 3) F)} (hŜ : IsSylowTwoOf Ŝ ⊤)
    (α : SpecialLinearGroup (Fin 3) F ≃* SpecialLinearGroup (Fin 3) F)
    (h2 : ∀ b ∈ Subgroup.normalizer (Ŝ : Set (SpecialLinearGroup (Fin 3) F)), α b * b⁻¹ ∈ Ŝ)
    (h3 : ∀ m, α (α (α m)) = m)
    (h4 : ∀ b ∈ Subgroup.normalizer (Ŝ : Set (SpecialLinearGroup (Fin 3) F)), orderOf b ≠ 3) :
    ∃ x : SpecialLinearGroup (Fin 3) F, ∀ m, α m = x * m * x⁻¹ := by
  have hcube : ∀ c : Fˣ, c ^ 3 = 1 → c = 1 := fun c hc => units_cube_eq_one h4 hc
  have hscal : ∀ A ∈ scalars 3 F, A = 1 := by
    intro A hA
    obtain ⟨c, hc, hAc⟩ := mem_scalars.mp hA
    have := hcube c hc
    subst this
    apply Subtype.ext
    simpa using hAc
  have hα3 : α ^ 3 = 1 := by
    ext m
    simp [pow_succ, h3]
  have hα'3 : descendAut 3 F α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  by_cases hD : descendAut 3 F α ∈ linearAutGroup 3 F
  · obtain ⟨H, hH⟩ : ∃ H : GL (Fin 3) F,
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 F H = descendAut 3 F α := by
      have : linearAutGroup 3 F =
          (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut 3 F).range := by
        unfold linearAutGroup
        rw [← MonoidHom.coe_range, Subgroup.closure_eq]
      rw [this] at hD
      exact hD
    exact inner_of_descendAut_eq_conjAut hscal hcube α H hH.symm
  · exfalso
    obtain ⟨σ, hσ, H, hH⟩ :=
      CFSG.RankThree.PartTwo.KFacts.linear_order_three_field_descent (by norm_num) _ hα'3 hD
    have hσ3 : ∀ a, σ (σ (σ a)) = a := by
      have h1 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
      intro a
      have := congrArg (fun τ : F ≃+* F => τ a) h1
      simpa [pow_succ] using this
    have htr : ∀ g : SpecialLinearGroup (Fin 3) F,
        ((α g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).trace =
          σ ((g : Matrix (Fin 3) (Fin 3) F).trace) := by
      intro g
      have e : α g = CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F H
          (SpecialLinearGroup.map σ.toRingHom
            (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F H⁻¹ g)) := by
        have h1 : proj 3 F (α g) = proj 3 F
            (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F H
              (SpecialLinearGroup.map σ.toRingHom
                (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F H⁻¹ g))) := by
          rw [← descendAut_proj, hH]
          simp only [MulAut.mul_apply, ← map_inv, conjAut_proj, fieldAut_proj]
        exact inv_mul_eq_one.mp (hscal _ (proj_eq_proj_iff.mp h1))
      rw [e, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.coe_slConjugation,
        Matrix.trace_units_conj, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
        ← AddMonoidHom.map_trace σ.toRingHom, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.coe_slConjugation,
        Matrix.trace_units_conj]
      rfl
    have hσ1 := sl3_field_eq_one hŜ α h2 σ hσ3 htr
    rw [hσ1, orderOf_one] at hσ
    omega

end Main

section Glue

theorem krig_of_sl3 {Ω : Type} [Group Ω] {K : Subgroup Ω} {F : Type} [Field F] [Finite F] {e : ℕ}
    (hF : Nat.card F = 2 ^ e) (iso : ↥K ≃* ↥(StatedSL 3 F)) : SzN22.KRig K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFin : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = 2 ^ e := by rw [← Nat.card_eq_fintype_card]; exact hF
  have hcp : CharP F 2 := charP_of_card_eq_prime_pow hcard
  exact krig_of_autRigid (iso.trans (specialLinearGroupEquivStatedSL 3 F).symm)
    (fun Ŝ α hŜ _ h2 h3 h4 => sl3_autRigid hŜ α h2 h3 h4)

end Glue

end SzN24

end CFSG.Quasithin
