module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen21Star
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen21Nat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen21Inputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

namespace Sixteen21

theorem forall_fix_vStar_of_case4 (hSU : RSU4NatFix) {D : Data G} {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hc : Case167_4 D V₀ V hV L) :
    ∀ w : vStar D.M V₀ V hV L, ∃ φ ∈ lStar D.M V₀ V hV L, orderOf φ = 3 ∧ φ w = w := by
  obtain ⟨K, hKfield, hKfinite, hKcard, hR⟩ := hc.2.1
  letI := hKfield
  letI := hKfinite
  have hK4 : Nat.card K = 4 := by
    rw [hKcard]
    norm_num
  have hR' : (FFModel.nat (StatedSU 4 2 K)).Realizes (lStar D.M V₀ V hV L) ⊤ ⊥ := hR
  intro w
  exact exists_fix_of_realizes_nat (Γ := StatedSU 4 2 K) hR' (hSU K hK4) w

theorem one_le_pRank_of_case4 (hSU : RSU4NatFix) {D : Data G} {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (h16 : Hyp16 D V₀ V) (h151 : Hyp151 D V₀ V L)
    (hc : Case167_4 D V₀ V hV L) :
    ∀ v ∈ V, v ≠ 1 → 1 ≤ CFSG.Open.pRank 3 (D.M ⊓ centralizer ({v} : Set G)) := by
  have hrk : 2 ≤ CFSG.Open.pRank 3 D.M :=
    D.sig_rank 3 (by rw [hc.2.2]; exact Set.mem_singleton 3)
  exact one_le_pRank_of_forall_fix_vStar hV h16 h151 Nat.prime_three (by norm_num) hrk
    (forall_fix_vStar_of_case4 hSU hV hc)

end Sixteen21

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
