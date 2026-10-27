module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1c
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubComponent

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_omega_commutator_barSub_le (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (X Y : Subgroup G) : ⁅barSub V₀ V hV X, barSub V₀ V hV Y⁆ ≤ barSub V₀ V hV ⁅X, Y⁆ := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨g, hgX, rfl⟩ := (mem_barSub V₀ V hV X a).1 ha
  obtain ⟨k, hkY, rfl⟩ := (mem_barSub V₀ V hV Y b).1 hb
  refine (mem_barSub V₀ V hV _ _).2 ⟨⁅g, k⁆, ?_, map_commutatorElement (actTil V₀ V hV) g k⟩
  have : ((⁅g, k⁆ : stabTil V₀ V) : G) = ⁅(g : G), (k : G)⁆ :=
    map_commutatorElement (stabTil V₀ V).subtype g k
  rw [this]
  exact Subgroup.commutator_mem_commutator hgX hkY

theorem s16h_e3_omega_calC_eq_of_barSub_eq {D : Data G} {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    {L K : Subgroup G} (hL : L ∈ calC D.M) (hK : K ∈ calC D.M)
    (heq : barSub V₀ V h.isElemAbelian L = barSub V₀ V h.isElemAbelian K)
    (hna : ⁅barSub V₀ V h.isElemAbelian L, barSub V₀ V h.isElemAbelian L⁆ ≠ ⊥) : L = K := by
  by_contra hne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : ⁅L, K⁆ ≤ CFSG.Open.pCoreOf 2 D.M :=
    (calC_commutator_le_of_ne hL hK hne).trans
      (inf_le_left.trans (CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2 hL.1))
  apply hna
  refine le_bot_iff.1 ?_
  calc ⁅barSub V₀ V h.isElemAbelian L, barSub V₀ V h.isElemAbelian L⁆
      = ⁅barSub V₀ V h.isElemAbelian L, barSub V₀ V h.isElemAbelian K⁆ := by rw [← heq]
    _ ≤ barSub V₀ V h.isElemAbelian ⁅L, K⁆ := s16h_e3_omega_commutator_barSub_le V₀ V _ L K
    _ ≤ barSub V₀ V h.isElemAbelian (CFSG.Open.pCoreOf 2 D.M) := barSub_mono V₀ V _ hcomm
    _ = ⊥ := barSub_pCoreOf_eq_bot_of_hyp125 h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
