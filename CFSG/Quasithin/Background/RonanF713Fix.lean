module

public import CFSG.Quasithin.Background.RonanF713Sylow
public import CFSG.Quasithin.Background.F7

public section

namespace CFSG.Quasithin.RonanF713

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

variable {G : Type*} [Group G] {G₀ G₁ G₂ T V : Subgroup G}

theorem exists_edge_conj_sylow_loc [Finite ↥G₂] (hyp : AmalgamHyp G₀ G₁ G₂ T)
    {β γ : CosetGeom G₀ G₁ G₂} (hadj : (graph G₀ G₁ G₂).Adj β γ) (hvt : vtype γ = true)
    {A : Subgroup G} (hAstab : A ≤ stab β ⊓ stab γ) (hA : IsPGroup 2 A) :
    ∃ g : ↥G₀, g • γ₀ G₀ G₁ G₂ = β ∧ g • γ₁ G₀ G₁ G₂ = γ ∧ A ≤ conjSub (g : G) T := by
  obtain ⟨g, ⟨hg0, hg1⟩ | ⟨hg0, hg1⟩⟩ := exists_smul_edge hadj
  · have heq : stab β ⊓ stab γ = conjSub (g : G) (G₁ ⊓ G₂) := by
      rw [← hg0, ← hg1, stab_smul, stab_smul, stab_γ₀ hyp.le₁, stab_γ₁ hyp.le₂, ← conjSub_inf]
    haveI : Finite ↥(G₁ ⊓ G₂) :=
      Finite.of_injective (Subgroup.inclusion (inf_le_right : G₁ ⊓ G₂ ≤ G₂))
        (Subgroup.inclusion_injective _)
    haveI : Finite ↥(stab β ⊓ stab γ) := by
      rw [heq]
      exact finite_conjSub _ _
    have hSyl : IsSylowTwoOf (conjSub (g : G) T) (stab β ⊓ stab γ) := by
      rw [heq]
      exact isSylowTwoOf_conj hyp.sylow_inf _
    obtain ⟨x, hx, hAx⟩ := isSylowTwoOf_exists_conj_le_loc hSyl hAstab hA
    have hx0 : x ∈ G₀ := stab_le β hx.1
    refine ⟨⟨x, hx0⟩ * g, ?_, ?_, ?_⟩
    · rw [mul_smul, hg0]
      exact smul_eq_of_mem_stab (g := ⟨x, hx0⟩) hx.1
    · rw [mul_smul, hg1]
      exact smul_eq_of_mem_stab (g := ⟨x, hx0⟩) hx.2
    · rw [Subgroup.coe_mul, conjSub_mul]
      exact hAx
  · exfalso
    have := congrArg vtype hg0
    rw [vtype_smul, vtype_γ₀, hvt] at this
    exact absurd this (by decide)

theorem exists_nbr_fixed_of_le_normalizer_loc (hyp : AmalgamHypV G₀ G₁ G₂ T V)
    {γ α : CosetGeom G₀ G₁ G₂} [Finite ↥(stab γ)] (hα : α ∈ nbrs γ) {X : Subgroup G}
    (hX : IsPGroup 2 X) (hXγ : X ≤ stab γ) (hXN : X ≤ Subgroup.normalizer (Vv V α : Set G)) :
    ∃ α' ∈ nbrs γ, Vv V α' = Vv V α ∧ X ≤ stab α' := by
  have hadj : (graph G₀ G₁ G₂).Adj γ α := hα
  obtain ⟨S, hS, hSle⟩ := exists_isSylowTwoOf_stab_inf hyp.toAmalgamHyp hadj
  have hSN : S ≤ stab γ ⊓ Subgroup.normalizer (Vv V α : Set G) :=
    le_inf hS.1 ((hSle.trans inf_le_right).trans (stab_le_normalizer_Vv hyp.normalizes α))
  have hSyl : IsSylowTwoOf S (stab γ ⊓ Subgroup.normalizer (Vv V α : Set G)) :=
    isSylowTwoOf_mono_right hS hSN inf_le_left
  haveI : Finite ↥(stab γ ⊓ Subgroup.normalizer (Vv V α : Set G)) :=
    Finite.of_injective
      (Subgroup.inclusion (inf_le_left : stab γ ⊓ Subgroup.normalizer (Vv V α : Set G) ≤ stab γ))
      (Subgroup.inclusion_injective _)
  obtain ⟨n, hn, hXn⟩ := isSylowTwoOf_exists_conj_le_loc hSyl (le_inf hXγ hXN) hX
  have hn0 : n ∈ G₀ := stab_le γ hn.1
  refine ⟨(⟨n, hn0⟩ : ↥G₀) • α, ?_, ?_, ?_⟩
  · have := (smul_adj (⟨n, hn0⟩ : ↥G₀)).mpr hadj
    rw [smul_eq_of_mem_stab (g := ⟨n, hn0⟩) hn.1] at this
    exact this
  · rw [Vv_smul hyp.normalizes]
    exact F7.conjSub_eq_of_mem_normalizer hn.2
  · rw [stab_smul]
    exact hXn.trans (conjSub_mono n (hSle.trans inf_le_right))

end CFSG.Quasithin.RonanF713
