module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.Blueprint.Catalog
import CFSG.LinearAlgebra.LinearGroups.Perfect
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification Matrix

namespace AUTSL

theorem exists_projectiveSL_equiv_of_lieModel {X : Type} [Group X] {n p f : ℕ}
    (h : Blueprint.LieModel X .PSL n p f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
      Nonempty (X ≃* projectiveSL n K) :=
  CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel h

section ProjectiveAut

variable {X : Type*} [Group X] {n : ℕ} {K : Type*} [Field K] [Finite K]

theorem exists_std_of_mulEquiv (hn : 3 ≤ n) (e : X ≃* projectiveSL n K) (α : MulAut X) :
    ∃ (A : GL (Fin n) K) (σ : K ≃+* K) (ε : ℕ), ε ≤ 1 ∧
      MulAut.congr e α = conjAut n K A * fieldAut n K σ * dualAut n K ^ ε :=
  (automorphism_generation hn).2 (MulAut.congr e α)

theorem exists_std_apply_of_mulEquiv (hn : 3 ≤ n) (e : X ≃* projectiveSL n K) (α : MulAut X) :
    ∃ (A : GL (Fin n) K) (σ : K ≃+* K) (ε : ℕ), ε ≤ 1 ∧
      ∀ x : X, e (α x) = (conjAut n K A * fieldAut n K σ * dualAut n K ^ ε) (e x) := by
  obtain ⟨A, σ, ε, hε, h⟩ := exists_std_of_mulEquiv hn e α
  refine ⟨A, σ, ε, hε, fun x => ?_⟩
  rw [← h]
  simp [MulAut.congr_apply]

end ProjectiveAut

theorem aut_of_lieModel_psl {X : Type} [Group X] {n p f : ℕ} (hn : 3 ≤ n)
    (h : Blueprint.LieModel X .PSL n p f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (e : X ≃* projectiveSL n K), Nat.card K = p ^ f ∧
      ∀ α : MulAut X, ∃ (A : GL (Fin n) K) (σ : K ≃+* K) (ε : ℕ), ε ≤ 1 ∧
        ∀ x : X, e (α x) = (conjAut n K A * fieldAut n K σ * dualAut n K ^ ε) (e x) := by
  obtain ⟨K, hF, hfin, hcard, ⟨e⟩⟩ := exists_projectiveSL_equiv_of_lieModel h
  exact ⟨K, hF, hfin, e, hcard, exists_std_apply_of_mulEquiv hn e⟩

section SpecialLinear

variable {n : ℕ} {K : Type*} [Field K]

private theorem eq_one_of_forall_mul_inv_mem_center {S : Type*} [Group S] [Group.IsPerfect S]
    {τ : MulAut S} (h : ∀ s : S, s⁻¹ * τ s ∈ Subgroup.center S) : τ = 1 := by
  let z : S →* S :=
    { toFun := fun s => s⁻¹ * τ s
      map_one' := by simp
      map_mul' := fun s t => by
        have ht := Subgroup.mem_center_iff.mp (h s)
        calc (s * t)⁻¹ * τ (s * t) = t⁻¹ * (s⁻¹ * τ s) * τ t := by
              rw [map_mul]
              group
          _ = s⁻¹ * τ s * (t⁻¹ * τ t) := by
              rw [ht t⁻¹]
              group }
  have hzc : ∀ s, z s ∈ Subgroup.center S := h
  have hcomm : ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ ≤ z.ker := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    have hab := Subgroup.mem_center_iff.mp (hzc a) (z b)
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact hab.symm
  have htop : ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ = ⊤ := Group.IsPerfect.commutator_eq_top
  rw [htop] at hcomm
  refine MulEquiv.ext fun s => ?_
  have hs : z s = 1 := hcomm (Subgroup.mem_top s)
  change s⁻¹ * τ s = 1 at hs
  rw [MulAut.one_apply]
  exact (inv_mul_eq_one.mp hs).symm

theorem descendAut_injective (hn : 3 ≤ n) : Function.Injective (descendAut n K) := by
  have : Group.IsPerfect (SpecialLinearGroup (Fin n) K) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect hn
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro e he
  rw [MonoidHom.mem_ker] at he
  rw [Subgroup.mem_bot]
  refine eq_one_of_forall_mul_inv_mem_center fun s => ?_
  have h := congrArg (fun φ : MulAut (projectiveSL n K) => φ (proj n K s)) he
  simp only [descendAut_proj, MulAut.one_apply] at h
  rw [proj_eq_proj_iff, scalars_eq_center] at h
  have := (Subgroup.center _).inv_mem h
  simpa using this

variable [Finite K]

theorem exists_eq_std_of_mulAut_sl (hn : 3 ≤ n) (β : MulAut (SpecialLinearGroup (Fin n) K)) :
    ∃ (A : GL (Fin n) K) (σ : K ≃+* K) (ε : ℕ), ε ≤ 1 ∧
      β = CatalogueBHigherLinearAction.slConjugation n K A *
        CatalogueBHigherLinearField.slFieldAut (Fin n) K σ *
          CatalogueBGraphForm.slGraphAut n K ^ ε := by
  obtain ⟨A, σ, ε, hε, h⟩ := (automorphism_generation hn).2 (descendAut n K β)
  refine ⟨A, σ, ε, hε, descendAut_injective hn ?_⟩
  rw [h]
  simp only [conjAut, fieldAut, dualAut, map_mul, map_pow, MonoidHom.comp_apply]

theorem exists_matrix_form_of_mulAut_sl (hn : 3 ≤ n) (β : MulAut (SpecialLinearGroup (Fin n) K)) :
    ∃ (A : GL (Fin n) K) (σ : K ≃+* K),
      (∀ g : SpecialLinearGroup (Fin n) K, (β g : Matrix (Fin n) (Fin n) K) =
        (A : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K).map σ *
          ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ∨
      (∀ g : SpecialLinearGroup (Fin n) K, (β g : Matrix (Fin n) (Fin n) K) =
        (A : Matrix (Fin n) (Fin n) K) *
          ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose.map σ *
            ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  obtain ⟨A, σ, ε, hε, h⟩ := exists_eq_std_of_mulAut_sl hn β
  refine ⟨A, σ, ?_⟩
  have hF : ∀ g : SpecialLinearGroup (Fin n) K,
      (CatalogueBHigherLinearField.slFieldAut (Fin n) K σ g : Matrix (Fin n) (Fin n) K) =
        (g : Matrix (Fin n) (Fin n) K).map σ := fun g => by
    ext i j
    exact CatalogueBHigherLinearField.slFieldEquiv_entry (Fin n) σ g i j
  have hC : ∀ g : SpecialLinearGroup (Fin n) K,
      (CatalogueBHigherLinearAction.slConjugation n K A g : Matrix (Fin n) (Fin n) K) =
        (A : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) *
          ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    fun g => CatalogueBHigherLinearAction.slConjugation_matrix n K A g
  interval_cases ε
  · left
    intro g
    rw [h]
    simp only [pow_zero, mul_one, MulAut.mul_apply]
    rw [hC, hF]
  · right
    intro g
    rw [h]
    simp only [pow_one, MulAut.mul_apply]
    rw [hC, hF, CatalogueBGraphForm.slGraphAut_matrix]

end SpecialLinear

end AUTSL

end CFSG.RankThree.PartOne
