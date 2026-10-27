module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2OutFusWeyl
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2UInv

public noncomputable section

namespace CFSG.Quasithin.H13.F431.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2

section Fusion

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [CharP K 2]

theorem pconj_torus {P : Subgroup (C K)} (hT : torusSub Tag.G2 K ≤ P) {x y : C K}
    (h : ∃ g ∈ torusSub Tag.G2 K, g * x * g⁻¹ = y) : PConj P x y := by
  obtain ⟨g, hg, e⟩ := h
  exact ⟨g, hT hg, e⟩

theorem fusion_U_aux [Finite K] {Pr Pa : Subgroup (C K)} (hUr : U K ≤ Pr) (hUa : U K ≤ Pa)
    (hTr : torusSub Tag.G2 K ≤ Pr) (hTa : torusSub Tag.G2 K ≤ Pa)
    (hnr : nW K Cls.iR ∈ Pr) (hna : nW K Cls.iA ∈ Pa) {u : C K} (hu : u ∈ U K)
    (hsq : u * u = 1) (hne : u ≠ 1) :
    PConj Pr u (xa 1) ∨ PConj Pr u (xu 1) ∨ PConj Pr u (xv 1) ∨ PConj Pr u (xb 1) ∨
      PConj Pr u (xc 1) ∨ PConj Pa u (xu 1) := by
  obtain ⟨α, ρ, μ, ν, β, γ, rfl⟩ := exists_nf hu
  rcases (nf_sq_eq_one_iff α ρ μ ν β γ).1 hsq with ⟨rfl, hαβ⟩ | ⟨hρ, rfl, rfl⟩
  · by_cases hα : α = 0
    · subst hα
      have hμν : μ * ν = 0 := by rw [← hαβ, zero_mul]
      by_cases hμ : μ = 0
      · subst hμ
        by_cases hν : ν = 0
        · subst hν
          by_cases hβ : β = 0
          · subst hβ
            have hγ : γ ≠ 0 := by
              rintro rfl
              exact hne nf_one
            refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
            rw [← xc_eq_nf]
            exact pconj_torus hTr (torus_xc hγ)
          · exact Or.inr (Or.inr (Or.inr (Or.inl
              (((pc_T3 hβ γ).mono hUr).trans (pconj_torus hTr (torus_xb hβ))))))
        · exact Or.inr (Or.inr (Or.inl
            (((pc_T2 hν β γ).mono hUr).trans (pconj_torus hTr (torus_xv hν)))))
      · have hν : ν = 0 := (mul_eq_zero.1 hμν).resolve_left hμ
        subst hν
        exact Or.inr (Or.inl (((pc_T1 hμ β γ).mono hUr).trans (pconj_torus hTr (torus_xu hμ))))
    · have h1 := (pc_S (γ := γ) hα hαβ).mono hUr
      by_cases hν' : α * (μ / α) ^ 2 + ν = 0
      · rw [hν'] at h1
        exact Or.inl (h1.trans (((pc_Sa hα _).mono hUr).trans
          (pconj_torus hTr (torus_xa hα))))
      · have h2 : PConj Pr (nf α 0 0 (α * (μ / α) ^ 2 + ν) 0 (α ^ 2 * (μ / α) ^ 3 + γ))
            (nf 0 0 (α * (μ / α) ^ 2 + ν) 0 α (α ^ 2 * (μ / α) ^ 3 + γ)) :=
          ⟨_, hnr, nR_nf _ _ _⟩
        exact Or.inr (Or.inl (h1.trans (h2.trans (((pc_T1 hν' _ _).mono hUr).trans
          (pconj_torus hTr (torus_xu hν'))))))
  · have h1 : PConj Pa (nf 0 ρ μ (ρ * μ) β γ) (xu ρ) :=
      ((pc_R hρ μ β γ).mono hUa).trans ⟨_, hna, nA_xr ρ⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h1.trans (pconj_torus hTa (torus_xu hρ)))))))

open scoped Classical in
theorem fusion_U_of [Finite K] {Pr Pa : Subgroup (C K)} (hUr : U K ≤ Pr) (hUa : U K ≤ Pa)
    (hTr : torusSub Tag.G2 K ≤ Pr) (hTa : torusSub Tag.G2 K ≤ Pa)
    (hnr : nW K Cls.iR ∈ Pr) (hna : nW K Cls.iA ∈ Pa) {u : C K} (hu : u ∈ U K)
    (hsq : u * u = 1) (hne : u ≠ 1) :
    ∃ i ∈ ({xa 1, xu 1, xv 1, xb 1, xc 1} : Finset (C K)),
      (∃ m ∈ Pr, m * u * m⁻¹ = i) ∨ (∃ m ∈ Pa, m * u * m⁻¹ = i) := by
  rcases fusion_U_aux hUr hUa hTr hTa hnr hna hu hsq hne with h | h | h | h | h | h
  · exact ⟨xa 1, by simp, Or.inl h⟩
  · exact ⟨xu 1, by simp, Or.inl h⟩
  · exact ⟨xv 1, by simp, Or.inl h⟩
  · exact ⟨xb 1, by simp, Or.inl h⟩
  · exact ⟨xc 1, by simp, Or.inl h⟩
  · exact ⟨xu 1, by simp, Or.inr h⟩

end Fusion

end CFSG.Quasithin.H13.F431.G2
