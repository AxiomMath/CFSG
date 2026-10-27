module

public import CFSG.LocalAnalysis.EvenSmallLie.ThreeTransposition.Section24Connected
public import CFSG.Timmesfeld.Bridge.OddTranspDefs

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity
open CFSG.Timmesfeld.Bridge.OddTransp

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem sylow_inter_D_transitive (hcls : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hodd : IsOddTransp D) (T : Sylow 2 G) {e f : G}
    (he : e ∈ (T : Set G) ∩ D) (hf : f ∈ (T : Set G) ∩ D) :
    ∃ h ∈ Subgroup.normalizer ((T : Set G) ∩ D), h * e * h⁻¹ = f := by
  have hDinv : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D :=
    fun g x hx => CFSG.Timmesfeld.conj_mem_of_isClass hcls g hx
  have hcomm : ∀ a ∈ (T : Set G) ∩ D, ∀ b ∈ (T : Set G) ∩ D, a * b = b * a :=
    fun a ha b hb => (hodd.commute_of_isPGroup T.isPGroup' ha.2 hb.2 ha.1 hb.1).eq
  obtain ⟨g, hg⟩ := isConj_iff.mp (CFSG.Timmesfeld.isConj_of_isClass hcls he.2 hf.2)
  obtain ⟨h, hh, hhe⟩ :=
    CFSG.EvenSmallLie.ThreeTransposition.exists_mem_normalizer_conj_eq hDinv T hcomm
      (y := (1 : G)) (fun a _ => by simp) he hf (by simp) hg
  exact ⟨h, (Subgroup.mem_inf.mp hh).1, hhe⟩

end CFSG.OddTranspositions
