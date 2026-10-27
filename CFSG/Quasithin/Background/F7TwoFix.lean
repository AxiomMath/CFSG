module

public import CFSG.Quasithin.Background.F7

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

variable {G : Type*} [Group G]

namespace CosetGeom

variable {G₀ G₁ G₂ T V : Subgroup G}

theorem exists_nbr_fixed_of_le_normalizer [Finite G] (hyp : AmalgamHypV G₀ G₁ G₂ T V)
    {γ α : CosetGeom G₀ G₁ G₂} (hα : α ∈ nbrs γ) {X : Subgroup G} (hX : IsPGroup 2 X)
    (hXγ : X ≤ stab γ) (hXN : X ≤ Subgroup.normalizer (Vv V α : Set G)) :
    ∃ α' ∈ nbrs γ, Vv V α' = Vv V α ∧ X ≤ stab α' := by
  have hadj : (graph G₀ G₁ G₂).Adj γ α := hα
  obtain ⟨S, hS, hSle⟩ := exists_isSylowTwoOf_stab_inf hyp.toAmalgamHyp hadj
  have hSN : S ≤ stab γ ⊓ Subgroup.normalizer (Vv V α : Set G) :=
    le_inf hS.1 ((hSle.trans inf_le_right).trans (stab_le_normalizer_Vv hyp.normalizes α))
  have hSyl : IsSylowTwoOf S (stab γ ⊓ Subgroup.normalizer (Vv V α : Set G)) :=
    isSylowTwoOf_mono_right hS hSN inf_le_left
  obtain ⟨n, hn, hXn⟩ := isSylowTwoOf_exists_conj_le hSyl (le_inf hXγ hXN) hX
  have hn0 : n ∈ G₀ := stab_le γ hn.1
  refine ⟨(⟨n, hn0⟩ : ↥G₀) • α, ?_, ?_, ?_⟩
  · have := (smul_adj (⟨n, hn0⟩ : ↥G₀)).mpr hadj
    rw [smul_eq_of_mem_stab (g := ⟨n, hn0⟩) hn.1] at this
    exact this
  · rw [Vv_smul hyp.normalizes]
    exact F7.conjSub_eq_of_mem_normalizer hn.2
  · rw [stab_smul]
    exact hXn.trans (conjSub_mono n (hSle.trans inf_le_right))

end CosetGeom

end CFSG.Quasithin
