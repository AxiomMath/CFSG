module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.S28
public import CFSG.LocalAnalysis.UniquenessCase.UC6S27

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.RankTwoShapes (IsAlperinSubgroup AlperinDecomposition alperin_centric_radical_fusion)
open CFSG.Yardstones.Mf4cdcdf2e013 (TheoremCAt)
open scoped commutatorElement
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

variable {G : Type} [Group G] [Finite G] {Dat : Data G}

namespace Mc614

variable (c : Mc614 Dat)

theorem exists_sylow_eq_R : ∃ S : Sylow c.r G, (S : Subgroup G) = c.R := by
  haveI : Fact c.r.Prime := ⟨c.d.prime⟩
  have hRp : IsPGroup c.r c.R := c.d.sylow.isPGroup
  obtain ⟨S, hRS⟩ := hRp.exists_le_sylow
  refine ⟨S, ?_⟩
  by_contra hne
  have hlt : c.R < (S : Subgroup G) := lt_of_le_of_ne hRS (fun h => hne h.symm)
  have hNR : normalizer (c.R : Set G) ≤ c.M :=
    c.d.normalizer_le_of_le_pGroup c.hC le_rfl (E_ne_bot c) c.E_le_R hRp
  have hN : c.R < (S : Subgroup G) ⊓ normalizer (c.R : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.pGroup_proper_subgroup_lt_internal_normalizer c.r
      c.d.prime (S : Subgroup G) c.R S.isPGroup' hlt
  have hNM : (S : Subgroup G) ⊓ normalizer (c.R : Set G) ≤ c.M := fun x hx => hNR hx.2
  have hNp : IsPGroup c.r ((S : Subgroup G) ⊓ normalizer (c.R : Set G) : Subgroup G) :=
    S.isPGroup'.to_inf_left
  have := c.d.sylow.eq_of_le hN.le hNM hNp
  exact hN.ne this.symm

noncomputable def sylowTop : Sylow c.r G := (c.exists_sylow_eq_R).choose

theorem coe_sylowTop : (c.sylowTop : Subgroup G) = c.R := (c.exists_sylow_eq_R).choose_spec

theorem normalizer_le_of_alperin {Q : Subgroup G}
    (hQ : IsAlperinSubgroup c.r (c.sylowTop : Subgroup G) Q) : normalizer (Q : Set G) ≤ c.M := by
  have hQR : Q ≤ c.R := by
    have := hQ.1
    rwa [c.coe_sylowTop] at this
  have hEQ : c.E ≤ Q := fun e he => by
    have hES : e ∈ (c.sylowTop : Subgroup G) := by
      rw [c.coe_sylowTop]
      exact c.E_le_R he
    refine hQ.2.2.1 (Subgroup.mem_inf.2 ⟨?_, hES⟩)
    rw [mem_centralizer_iff]
    intro q hq
    exact mem_centralizer_iff.1 (c.d.E_le he).2 q (hQR hq)
  exact c.d.normalizer_le_of_le_pGroup c.hC le_rfl (E_ne_bot c) hEQ
    (c.d.sylow.isPGroup.to_le hQR)

theorem fusion_control {x g : G} (hx : x ∈ c.sylowTop) (hg : g * x * g⁻¹ ∈ c.sylowTop) :
    ∃ k ∈ c.M, g * x * g⁻¹ = k⁻¹ * x * k := by
  haveI : Fact c.r.Prime := ⟨c.d.prime⟩
  exact fusion_control_of_alperin_uc6 c.sylowTop (fun Q hQ => c.normalizer_le_of_alperin hQ) hx hg

theorem R_le_commutator : c.R ≤ ⁅c.M, c.M⁆ := by
  haveI : Fact c.r.Prime := ⟨c.d.prime⟩
  have hSM : (c.sylowTop : Subgroup G) ≤ c.M := by
    rw [c.coe_sylowTop]
    exact c.R_le_M
  have := sylow_le_commutator_of_fusion_uc6 Dat.standing.simple Dat.standing.nonab c.sylowTop hSM
    (fun x hx g hg => c.fusion_control hx hg)
  rwa [c.coe_sylowTop] at this

end Mc614

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

theorem c627 : m.C627 := m.hZ.le.trans m.toMc614.R_le_commutator

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
