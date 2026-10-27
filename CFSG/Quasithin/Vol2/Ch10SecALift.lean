module

public import CFSG.Quasithin.Background.B5Part3

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Quasithin

variable {F : Type} [Field F]

@[expose] def unipSL (b : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, b; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def diagSL {μ : F} (hμ : μ ≠ 0) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![μ, 0; 0, μ⁻¹], by simp [Matrix.det_fin_two, hμ]⟩

theorem coe_unipSL (b : F) : ((unipSL b : Matrix.SpecialLinearGroup (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F) = !![1, b; 0, 1] := rfl

theorem coe_diagSL {μ : F} (hμ : μ ≠ 0) : ((diagSL hμ : Matrix.SpecialLinearGroup (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F) = !![μ, 0; 0, μ⁻¹] := rfl

theorem unipSL_zero : unipSL (0 : F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_unipSL]

theorem unipSL_mul_self [CharP F 2] (a : F) : unipSL a * unipSL a = 1 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_unipSL, Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination a * h2

theorem diagSL_conj {μ : F} (hμ : μ ≠ 0) (b : F) :
    diagSL hμ * unipSL b * (diagSL hμ)⁻¹ = unipSL (μ ^ 2 * b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_unipSL, coe_diagSL, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, hμ]
  ring

theorem unipSL_mulVec (b : F) (v : Fin 2 → F) :
    (!![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) F).mulVec v = ![v 0 + b * v 1, v 1] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem diagSL_mulVec (μ : F) (v : Fin 2 → F) :
    (!![μ, 0; 0, μ⁻¹] : Matrix (Fin 2) (Fin 2) F).mulVec v = ![μ * v 0, μ⁻¹ * v 1] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem exists_beta_of_realizesVia_nat {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)}
    {Z : Subgroup V} {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {π : (FFModel.nat Γ).Gam →* ↥H}
    (h : (FFModel.nat Γ).RealizesVia H ⊤ Z π) :
    ∃ β : V →* Multiplicative (ι → K), Function.Surjective β ∧ (∀ v, β v = 1 ↔ v ∈ Z) ∧
      ∀ (γ : (FFModel.nat Γ).Gam) (v : V), β (((π γ : ↥H) : MulAut V) v) = Multiplicative.ofAdd
        ((((show ↥Γ from γ) : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K).mulVec
          (Multiplicative.toAdd (β v))) := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := h
  let e : (↥(FFModel.nat Γ).sec ⧸ (FFModel.nat Γ).ker.subgroupOf (FFModel.nat Γ).sec) ≃*
      Multiplicative (ι → K) := B5.natQuotEquiv (Multiplicative (ι → K))
  have he : ∀ m : Multiplicative (ι → K),
      e (QuotientGroup.mk (⟨m, Subgroup.mem_top m⟩ : ↥(FFModel.nat Γ).sec)) = m :=
    fun m => rfl
  let β' : V →* Multiplicative (ι → K) :=
    (e.toMonoidHom.comp β).comp (Subgroup.topEquiv (G := V)).symm.toMonoidHom
  have hβ' : ∀ v, β' v = e (β ⟨v, Subgroup.mem_top v⟩) := fun v => rfl
  refine ⟨β', fun m => ?_, fun v => ?_, fun γ v => ?_⟩
  · obtain ⟨u, hu⟩ := hβs (e.symm m)
    refine ⟨(u : V), ?_⟩
    rw [hβ']
    have hu' : (⟨(u : V), Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup V)) = u := Subtype.ext rfl
    rw [hu', hu, MulEquiv.apply_symm_apply]
  · rw [hβ', EmbeddingLike.map_eq_one_iff]
    exact hβk _
  · have h1 : β ⟨v, Subgroup.mem_top v⟩ =
        QuotientGroup.mk ⟨e (β ⟨v, Subgroup.mem_top v⟩), Subgroup.mem_top _⟩ :=
      e.injective (he _).symm
    have h2 := hβe γ ⟨v, Subgroup.mem_top v⟩ ⟨e (β ⟨v, Subgroup.mem_top v⟩), Subgroup.mem_top _⟩
      (Subgroup.mem_top _) (Subgroup.mem_top _) h1
    rw [hβ']
    exact congrArg e h2

end CFSG.Quasithin.Vol2.Ch10.SecA
