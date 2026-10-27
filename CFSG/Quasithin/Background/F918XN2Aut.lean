module

public import CFSG.Quasithin.Background.F918X0
public import CFSG.RankThree.PartOne.AUTSL.Interface

public section

namespace CFSG.Quasithin.F918X

namespace SLTwist

open Matrix CFSG.RankThree.PartOne.AUTSL CFSG.ComponentClassification.CatalogueBGraphForm

section SemilinearType

variable {n : ℕ} {K : Type} [Field K]

@[expose] def IsSemilinearAut (β : MulAut (SpecialLinearGroup (Fin n) K)) : Prop :=
  ∃ (A : GL (Fin n) K) (σ : K ≃+* K), ∀ g : SpecialLinearGroup (Fin n) K,
    (β g : Matrix (Fin n) (Fin n) K) =
      (A : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K).map σ *
        ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

theorem isSemilinearAut_graph_mul (β : MulAut (SpecialLinearGroup (Fin n) K))
    (A : GL (Fin n) K) (σ : K ≃+* K)
    (h : ∀ g : SpecialLinearGroup (Fin n) K, (β g : Matrix (Fin n) (Fin n) K) =
      (A : Matrix (Fin n) (Fin n) K) *
        ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose.map σ *
          ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    IsSemilinearAut (slGraphAut n K * β) := by
  refine ⟨glGraphAut n K A, σ, fun g => ?_⟩
  have h1 : ((slGraphAut n K * β) g : Matrix (Fin n) (Fin n) K) =
      ((β (g⁻¹) : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose := by
    rw [MulAut.mul_apply, slGraphAut_matrix, map_inv]
  have h2 : (((glGraphAut n K A)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (A : Matrix (Fin n) (Fin n) K).transpose := by
    rw [← map_inv, glGraphAut_matrix, inv_inv]
  have h3 : ((glGraphAut n K A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose :=
    glGraphAut_matrix n K A
  have h4 := h (g⁻¹)
  rw [inv_inv] at h4
  rw [h1, h4, h2, h3, Matrix.transpose_mul, Matrix.transpose_mul, ← Matrix.transpose_map,
    Matrix.transpose_transpose, mul_assoc]

theorem isSemilinearAut_or_graph_mul [Finite K] (hn : 3 ≤ n)
    (β : MulAut (SpecialLinearGroup (Fin n) K)) :
    IsSemilinearAut β ∨ IsSemilinearAut (slGraphAut n K * β) := by
  obtain ⟨A, σ, h | h⟩ := exists_matrix_form_of_mulAut_sl hn β
  · exact Or.inl ⟨A, σ, h⟩
  · exact Or.inr (isSemilinearAut_graph_mul β A σ h)

theorem twoClassMod_of_equiv_sl {W : Type*} [CommGroup W] {L : Subgroup (MulAut W)} [Finite K]
    (hn : 3 ≤ n) (ψ : SpecialLinearGroup (Fin n) K ≃* ↥L)
    (h : ∀ β : MulAut (SpecialLinearGroup (Fin n) K), IsSemilinearAut β →
      MulAut.congr ψ β ∈ realized L) : TwoClassMod L := by
  refine twoClassMod_of_cover (MulAut.congr ψ (slGraphAut n K))⁻¹ fun α => ?_
  obtain ⟨β, rfl⟩ := (MulAut.congr ψ).surjective α
  rcases isSemilinearAut_or_graph_mul hn β with hβ | hβ
  · exact Or.inl (h β hβ)
  · refine Or.inr ?_
    have := h _ hβ
    rw [map_mul] at this
    rwa [inv_inv]

end SemilinearType

section TwoElements

theorem eq_zero_or_one_of_card_two {F : Type} [Field F] (hF : Nat.card F = 2) (x : F) :
    x = 0 ∨ x = 1 := by
  by_contra hx
  push Not at hx
  obtain ⟨hx0, hx1⟩ := hx
  have hfin : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have hinj : Function.Injective (![0, 1, x] : Fin 3 → F) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have := Nat.card_le_card_of_injective _ hinj
  simp at this
  omega

theorem ringEquiv_apply_of_card_two {F : Type} [Field F] (hF : Nat.card F = 2) (σ : F ≃+* F)
    (x : F) : σ x = x := by
  rcases eq_zero_or_one_of_card_two hF x with rfl | rfl
  · simp
  · simp

variable {n : ℕ} {K : Type} [Field K]

theorem exists_conj_of_isSemilinearAut_card_two (hK : Nat.card K = 2)
    {β : MulAut (SpecialLinearGroup (Fin n) K)} (hβ : IsSemilinearAut β) :
    ∃ a : SpecialLinearGroup (Fin n) K, β = MulAut.conj a := by
  obtain ⟨A, σ, hA⟩ := hβ
  have hdet : (A : Matrix (Fin n) (Fin n) K).det = 1 := by
    have hu : IsUnit (A : Matrix (Fin n) (Fin n) K).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp A.isUnit
    rcases eq_zero_or_one_of_card_two hK (A : Matrix (Fin n) (Fin n) K).det with h | h
    · exact absurd h hu.ne_zero
    · exact h
  have hσ : ∀ g : SpecialLinearGroup (Fin n) K,
      (g : Matrix (Fin n) (Fin n) K).map σ = (g : Matrix (Fin n) (Fin n) K) := by
    intro g
    ext i j
    exact ringEquiv_apply_of_card_two hK σ _
  let a : SpecialLinearGroup (Fin n) K := ⟨A, hdet⟩
  refine ⟨a, MulEquiv.ext fun g => ?_⟩
  apply SpecialLinearGroup.toGL_injective
  apply Units.ext
  have hA' : SpecialLinearGroup.toGL a = A := Units.ext rfl
  rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hA', Units.val_mul, Units.val_mul]
  exact (hA g).trans (by rw [hσ g]; rfl)

theorem twoClassMod_of_equiv_sl_card_two {W : Type*} [CommGroup W] {L : Subgroup (MulAut W)}
    [Finite K] (hK : Nat.card K = 2) (hn : 3 ≤ n) (ψ : SpecialLinearGroup (Fin n) K ≃* ↥L) :
    TwoClassMod L := by
  refine twoClassMod_of_equiv_sl hn ψ fun β hβ => ?_
  obtain ⟨a, rfl⟩ := exists_conj_of_isSemilinearAut_card_two hK hβ
  have h : MulAut.congr ψ (MulAut.conj a) = MulAut.conj (ψ a) := by
    refine MulEquiv.ext fun x => ?_
    simp [MulAut.congr_apply]
  rw [h]
  exact conj_mem_realized L _

theorem twoClassMod_of_equiv_statedSL_two {W : Type*} [CommGroup W] {L : Subgroup (MulAut W)}
    (hn : 3 ≤ n) (hK : Nat.card K = 2) (e : ↥L ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL n K)) :
    TwoClassMod L :=
  haveI : Finite K := Nat.finite_of_card_ne_zero (by omega)
  twoClassMod_of_equiv_sl_card_two hK hn
    ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K).trans e.symm)

end TwoElements

end SLTwist

end CFSG.Quasithin.F918X
