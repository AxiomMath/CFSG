module

public import CFSG.Quasithin.Recognition.F112Crit.Lemma63

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

open CosetGeom (graph stab ballStab nbrs sphere vtype γ₀ γ₁ Vv)

variable {G₀ G₁ G₂ T Z : Subgroup G}

@[expose] noncomputable def Wv (Z : Subgroup G) (γ : CosetGeom G₀ G₁ G₂) : Subgroup G :=
  ⨆ (δ : CosetGeom G₀ G₁ G₂) (_ : δ ∈ nbrs γ), Vv Z δ

theorem Vv_le_Vv_of_mem_nbrs {δ μ : CosetGeom G₀ G₁ G₂} (hδ : vtype δ = true)
    (hμ : μ ∈ nbrs δ) : Vv Z μ ≤ Vv Z δ := by
  cases δ with
  | inl x => exact absurd hδ (by simp [CosetGeom.vtype])
  | inr y =>
    cases μ with
    | inl x =>
      rw [CosetGeom.Vv_inr]
      exact le_iSup₂_of_le x hμ le_rfl
    | inr y' =>
      exact absurd (show (graph G₀ G₁ G₂).Adj (Sum.inr y) (Sum.inr y') from hμ)
        CosetGeom.not_adj_inr_inr

theorem Vv_le_of_forall_mem_nbrs {δ : CosetGeom G₀ G₁ G₂} (hδ : vtype δ = true) {K : Subgroup G}
    (h : ∀ μ ∈ nbrs δ, Vv Z μ ≤ K) : Vv Z δ ≤ K := by
  cases δ with
  | inl x => exact absurd hδ (by simp [CosetGeom.vtype])
  | inr y =>
    rw [CosetGeom.Vv_inr]
    exact iSup₂_le fun x hx => h (Sum.inl x) hx

theorem vtype_eq_true_of_mem_nbrs {γ δ : CosetGeom G₀ G₁ G₂} (hγ : vtype γ = false)
    (hδ : δ ∈ nbrs γ) : vtype δ = true := by
  have := CosetGeom.vtype_ne_of_adj (show (graph G₀ G₁ G₂).Adj γ δ from hδ)
  rw [hγ] at this
  cases h : vtype δ
  · exact absurd h.symm this
  · rfl

theorem vtype_eq_false_of_mem_nbrs {γ δ : CosetGeom G₀ G₁ G₂} (hγ : vtype γ = true)
    (hδ : δ ∈ nbrs γ) : vtype δ = false := by
  have := CosetGeom.vtype_ne_of_adj (show (graph G₀ G₁ G₂).Adj γ δ from hδ)
  rw [hγ] at this
  cases h : vtype δ
  · rfl
  · exact absurd h.symm this

variable [Finite G]

theorem dist_le_two_of_mem_nbrs (hc : CritAmalgam G₀ G₁ G₂ T Z) {δ γ μ : CosetGeom G₀ G₁ G₂}
    (hγ : γ ∈ nbrs δ) (hμ : μ ∈ nbrs δ) : CosetGeom.dist γ μ ≤ 2 := by
  have h1 := CosetGeom.dist_triangle hc.amalgam.gen γ δ μ
  have h2 : CosetGeom.dist γ δ = 1 := by
    rw [CosetGeom.dist_comm]; exact CosetGeom.dist_eq_one_iff_adj.mpr hγ
  have h3 : CosetGeom.dist δ μ = 1 := CosetGeom.dist_eq_one_iff_adj.mpr hμ
  omega

theorem pCoreOf_stab_le_pCoreOf_stab_inf (hc : CritAmalgam G₀ G₁ G₂ T Z)
    {δ γ : CosetGeom G₀ G₁ G₂} (hγ : γ ∈ nbrs δ) :
    pCoreOf 2 (stab δ) ≤ pCoreOf 2 (stab δ ⊓ stab γ) :=
  (CosetGeom.pCoreOf_stab_eq hc.amalgam hγ).le.trans inf_le_left

theorem le_pCoreOf_stab_of_le_ballStab {γ δ : CosetGeom G₀ G₁ G₂} (hδ : δ ∈ nbrs γ) {X : Subgroup G}
    (hX : X ≤ pCoreOf 2 (stab γ ⊓ stab δ)) (hX' : X ≤ ballStab 1 δ) :
    X ≤ pCoreOf 2 (stab δ) :=
  fun x hx =>
    pCoreOf_mono_of_le_normalizer (CosetGeom.ballStab_le_stab 1 δ)
      (CosetGeom.le_normalizer_ballStab 1 δ)
      ((CosetGeom.pCoreOf_stab_inf_ballStab_le hδ).2 ⟨hX hx, hX' hx⟩)

theorem lemma65_1 (hc : CritAmalgam G₀ G₁ G₂ T Z) (hb : 3 ≤ critB G₀ G₁ G₂ Z)
    {γ δ : CosetGeom G₀ G₁ G₂} (hγ : vtype γ = false) (hδ : δ ∈ nbrs γ) :
    Vv Z δ ≤ pCoreOf 2 (stab γ) ∧ Vv Z δ ≤ pCoreOf 2 (stab δ) := by
  have hδt := vtype_eq_true_of_mem_nbrs hγ hδ
  have hγδ : γ ∈ nbrs δ := CosetGeom.mem_nbrs_symm hδ
  refine ⟨Vv_le_of_forall_mem_nbrs hδt fun μ hμ => ?_, (lemma63_2' hc hδt).2.1⟩
  have hμt := vtype_eq_false_of_mem_nbrs hδt hμ
  have hd : CosetGeom.dist μ γ < 3 :=
    lt_of_le_of_lt (dist_le_two_of_mem_nbrs hc hμ hγδ) (by norm_num)
  have h1 : Vv Z μ ≤ ballStab 1 γ := (le_critB_iff_at hc hμt 3).mp hb γ hd
  have h2 : Vv Z μ ≤ pCoreOf 2 (stab δ) := (lemma63_2 hc hμt (CosetGeom.mem_nbrs_symm hμ)).1
  have h3 : Vv Z μ ≤ pCoreOf 2 (stab δ ⊓ stab γ) :=
    h2.trans (pCoreOf_stab_le_pCoreOf_stab_inf hc hγδ)
  exact le_pCoreOf_stab_of_le_ballStab hγδ h3 h1

theorem lemma65_2 (hc : CritAmalgam G₀ G₁ G₂ T Z) (hb : 4 ≤ critB G₀ G₁ G₂ Z)
    {γ : CosetGeom G₀ G₁ G₂} (hγ : vtype γ = false) :
    Wv Z γ ≤ pCoreOf 2 (stab γ) ∧ IsElemAbelian 2 (Wv Z γ) := by
  have hb3 : 3 ≤ critB G₀ G₁ G₂ Z := by omega
  refine ⟨iSup₂_le fun δ hδ => (lemma65_1 hc hb3 hγ hδ).1, ?_⟩
  have hcomm : ∀ δ ∈ nbrs γ, ∀ δ' ∈ nbrs γ, ∀ x ∈ Vv Z δ', ∀ y ∈ Vv Z δ, x * y = y * x := by
    intro δ hδ δ' hδ' x hx y hy
    have hδt := vtype_eq_true_of_mem_nbrs hγ hδ
    have hδ't := vtype_eq_true_of_mem_nbrs hγ hδ'
    have hle : Vv Z δ' ≤ Subgroup.centralizer (Vv Z δ : Set G) := by
      refine Vv_le_of_forall_mem_nbrs hδ't fun μ hμ => ?_
      have hμt := vtype_eq_false_of_mem_nbrs hδ't hμ
      have hδ'γ : γ ∈ nbrs δ' := CosetGeom.mem_nbrs_symm hδ'
      have h1 : Vv Z μ ≤ pCoreOf 2 (stab γ) :=
        (Vv_le_Vv_of_mem_nbrs hδ't hμ).trans (lemma65_1 hc hb3 hγ hδ').1
      have h2 : Vv Z μ ≤ pCoreOf 2 (stab γ ⊓ stab δ) :=
        h1.trans (pCoreOf_stab_le_pCoreOf_stab_inf hc hδ)
      have h3 : Vv Z μ ≤ ballStab 1 δ := by
        refine (le_critB_iff_at hc hμt 4).mp hb δ ?_
        have e1 := CosetGeom.dist_triangle hc.amalgam.gen μ γ δ
        have e2 : CosetGeom.dist μ γ ≤ 2 := by
          rw [CosetGeom.dist_comm]; exact dist_le_two_of_mem_nbrs hc hδ'γ hμ
        have e3 : CosetGeom.dist γ δ = 1 := CosetGeom.dist_eq_one_iff_adj.mpr hδ
        omega
      have h4 : Vv Z μ ≤ pCoreOf 2 (stab δ) := le_pCoreOf_stab_of_le_ballStab hδ h2 h3
      have h5 := (lemma63_2' hc hδt).2.2.1
      intro x hx
      exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
        ((Subgroup.mem_centralizer_iff.mp (h5 hy)) x (h4 hx)).symm
    exact ((Subgroup.mem_centralizer_iff.mp (hle hx)) y hy).symm
  have e : Wv Z γ = ⨆ x : {δ : CosetGeom G₀ G₁ G₂ // δ ∈ nbrs γ}, Vv Z x.1 := by
    unfold Wv; exact iSup_subtype'
  rw [e]
  refine CosetGeom.isElemAbelian_iSup _ (fun x => ?_) (fun i j x hx y hy => ?_)
  · exact (lemma63_2' hc (vtype_eq_true_of_mem_nbrs hγ x.2)).1
  · exact hcomm j.1 j.2 i.1 i.2 x hx y hy

end CFSG.Quasithin.F112Crit
