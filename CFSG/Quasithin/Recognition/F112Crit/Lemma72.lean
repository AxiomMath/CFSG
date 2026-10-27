module

public import CFSG.Quasithin.Recognition.F112Crit.Lemma65

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

open CosetGeom (graph stab ballStab nbrs sphere vtype γ₀ γ₁ Vv)

variable {G₀ G₁ G₂ T Z : Subgroup G} [Finite G]

theorem lemma72 (hc : CritAmalgam G₀ G₁ G₂ T Z) {γ : CosetGeom G₀ G₁ G₂} (hγ : vtype γ = false)
    {μ : CosetGeom G₀ G₁ G₂} (hd : CosetGeom.dist γ μ < critB G₀ G₁ G₂ Z) :
    Vv Z γ ≤ pCoreOf 2 (stab μ) := by
  suffices h : ∀ d : ℕ, d < critB G₀ G₁ G₂ Z → ∀ μ : CosetGeom G₀ G₁ G₂,
      CosetGeom.dist γ μ = d → Vv Z γ ≤ pCoreOf 2 (stab μ) from h _ hd μ rfl
  intro d
  induction d with
  | zero =>
    intro _ μ hμ
    obtain rfl : γ = μ := (CosetGeom.dist_eq_zero_iff hc.amalgam.gen).mp hμ
    exact (lemma63_1 hc hγ).1
  | succ d ih =>
    intro hdb μ hμ
    obtain ⟨μ', hadj, hμ'⟩ := CosetGeom.exists_adj_dist_eq hc.amalgam.gen hμ
    have hμμ' : μ ∈ nbrs μ' := CosetGeom.mem_nbrs_symm hadj
    have h1 : Vv Z γ ≤ pCoreOf 2 (stab μ') := ih (by omega) μ' hμ'
    have h2 : Vv Z γ ≤ pCoreOf 2 (stab μ' ⊓ stab μ) :=
      h1.trans (pCoreOf_stab_le_pCoreOf_stab_inf hc hμμ')
    have h3 : Vv Z γ ≤ ballStab 1 μ :=
      (le_critB_iff_at hc hγ (d + 1 + 1)).mp (by omega) μ (by omega)
    exact le_pCoreOf_stab_of_le_ballStab hμμ' h2 h3

theorem lemma72_small (hc : CritAmalgam G₀ G₁ G₂ T Z) {δ : CosetGeom G₀ G₁ G₂}
    (hδ : vtype δ = true) {μ : CosetGeom G₀ G₁ G₂}
    (hd : CosetGeom.dist δ μ + 2 ≤ critB G₀ G₁ G₂ Z) : Vv Z δ ≤ pCoreOf 2 (stab μ) := by
  refine Vv_le_of_forall_mem_nbrs hδ fun γ hγ => ?_
  have hγt : vtype γ = false := vtype_eq_false_of_mem_nbrs hδ hγ
  refine lemma72 hc hγt ?_
  have h1 := CosetGeom.dist_triangle hc.amalgam.gen γ δ μ
  have h2 : CosetGeom.dist γ δ = 1 := by
    rw [CosetGeom.dist_comm]; exact CosetGeom.dist_eq_one_iff_adj.mpr hγ
  omega

end CFSG.Quasithin.F112Crit
