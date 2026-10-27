module

public import CFSG.OddTranspositions.Blocks

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem Aalpha.conj_normalizer {D α β : Set G} (hN : IsNormalSet D) {g : G}
    (hg : g ∈ Subgroup.normalizer α) (hβ : β ∈ Aalpha D α) :
    (fun x => g * x * g⁻¹) '' β ∈ Aalpha D α := by
  rw [mem_Aalpha_iff] at hβ ⊢
  have hsm : ConjAct.toConjAct g • β = (fun x => g * x * g⁻¹) '' β := by
    rw [← Set.image_smul]
    rfl
  refine ⟨?_, ?_⟩
  · rw [mem_blockClass_iff] at hβ ⊢
    obtain ⟨h, rfl⟩ := hβ.1
    refine ⟨g * h, ?_⟩
    show (fun x => g * x * g⁻¹) '' ((fun x => h * x * h⁻¹) '' α) =
      (fun x => (g * h) * x * (g * h)⁻¹) '' α
    rw [Set.image_image]
    congr 1
    ext z
    group
  · intro hconj
    rw [← hsm] at hconj
    have hαeq : ConjAct.toConjAct g • α = α := by
      rw [show ConjAct.toConjAct g • α = MulAut.conj g '' α from by
        rw [← Set.image_smul]
        rfl]
      exact Subgroup.mem_normalizer_iff_conj_image_eq.mp hg
    have h1 : ConjAct.toConjAct g • perp D α = perp D α := by
      rw [smul_perp hN, hαeq]
    have h1' : (ConjAct.toConjAct g)⁻¹ • perp D α = perp D α := by
      have h := congrArg (fun s : Set (Set G) => (ConjAct.toConjAct g)⁻¹ • s) h1
      simpa [inv_smul_smul] using h.symm
    have hmem : (ConjAct.toConjAct g)⁻¹ • (ConjAct.toConjAct g • β) ∈
        (ConjAct.toConjAct g)⁻¹ • perp D α := ⟨_, hconj, rfl⟩
    rw [inv_smul_smul, h1'] at hmem
    exact hβ.2 hmem

end CFSG.OddTranspositions
