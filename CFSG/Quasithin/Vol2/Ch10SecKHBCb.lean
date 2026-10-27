module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSylowNormalizer

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KH

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K]

@[expose] noncomputable def diagThreeHom : Kˣ →* SpecialLinearGroup (Fin 3) K where
  toFun l := ⟨diagonal ![(l : K), ((l⁻¹ : Kˣ) : K), 1], by
    simp [det_diagonal, Fin.prod_univ_three]⟩
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' l m := by
    apply Subtype.ext
    show diagonal ![((l * m : Kˣ) : K), (((l * m)⁻¹ : Kˣ) : K), 1] =
      diagonal ![(l : K), ((l⁻¹ : Kˣ) : K), 1] * diagonal ![(m : K), ((m⁻¹ : Kˣ) : K), 1]
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp [mul_comm]

theorem coe_diagThreeHom (l : Kˣ) :
    (diagThreeHom l : Matrix (Fin 3) (Fin 3) K) = diagonal ![(l : K), ((l⁻¹ : Kˣ) : K), 1] :=
  rfl

theorem projDiagThree_injective : Function.Injective ((proj 3 K).comp (diagThreeHom (K := K))) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro l hl
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, proj_eq_one_iff] at hl
  obtain ⟨c, -, hc⟩ := hl
  rw [coe_diagThreeHom] at hc
  have h22 := congrFun (congrFun hc 2) 2
  have h00 := congrFun (congrFun hc 0) 0
  simp only [diagonal_apply_eq, scalar_apply] at h22 h00
  rw [Subgroup.mem_bot]
  apply Units.ext
  simp only [Matrix.cons_val, Units.val_one] at h22 h00 ⊢
  rw [h00, ← h22]

theorem exists_cartan_projectiveSL_three [Finite K] [CharP K 2] :
    ∃ d₀ ∈ Subgroup.normalizer (projUnitriangular 3 K : Set (projectiveSL 3 K)),
      orderOf d₀ = Nat.card K - 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨l, hl⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  refine ⟨(proj 3 K).comp diagThreeHom l, ?_, ?_⟩
  · rw [normalizer_projUnitriangular (n := 3) 2]
    refine ⟨diagThreeHom l, fun i j hij => ?_, rfl⟩
    rw [coe_diagThreeHom, diagonal_apply_ne _ (ne_of_gt hij)]
  · rw [orderOf_injective _ projDiagThree_injective l, hl, Nat.card_units]

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KH
