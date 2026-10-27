module

import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofTools
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec14.Item148StepPoint
public import CFSG.RankThree.PartTwo.Sec17.Item17HeadProofDefs

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open scoped Pointwise

namespace Proof171Steps

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem centralizer_le_M_of_mem_omegaA (h : Sec17Std G A c L Y₀)
    (h1514 : Item1514 A (lB A) c L) (hMeets : MeetsY4 A (lB A) L Y₀) {e : G}
    (he : Subgroup.zpowers e ∈ omegaA A) :
    Subgroup.centralizer ({e} : Set G) ≤ Subgroup.normalizer (Y₀ : Set G) := by
  rcases h1514 Y₀ h.mem_y0Star hMeets with ⟨-, -, hΩ, -⟩ | ⟨-, -, hT, -⟩ |
      ⟨-, -, -, -, hno, -⟩
  · rw [hΩ, Set.mem_singleton_iff] at he
    rw [centralizer_singleton_eq_of_zpowers_eq he]
    exact HeadProof.centralizer_c_le_M h
  · obtain ⟨w, hw, hew⟩ := hT.2 _ he
    have hwM : w ∈ Subgroup.normalizer (Y₀ : Set G) := h.normalizer_le hw
    have hC : Subgroup.centralizer ({e} : Set G) =
        (Subgroup.centralizer ({c} : Set G)).map (MulAut.conj w).toMonoidHom := by
      rw [← centralizer_zpowers148, hew, ← map_conj_centralizer, centralizer_zpowers148]
    rw [hC]
    calc (Subgroup.centralizer ({c} : Set G)).map (MulAut.conj w).toMonoidHom
        ≤ (Subgroup.normalizer (Y₀ : Set G)).map (MulAut.conj w).toMonoidHom :=
          Subgroup.map_mono (HeadProof.centralizer_c_le_M h)
      _ = Subgroup.normalizer (Y₀ : Set G) :=
          map_conj_eq_of_mem_normalizer' (Subgroup.le_normalizer hwM)
  · exact absurd h.le_y0 (hno Y₀ h.mem_y0Star)

theorem lB_le_of_centralizer_le {B M : Subgroup G}
    (hM : ∀ e : G, Subgroup.zpowers e ∈ omegaA A → Subgroup.centralizer ({e} : Set G) ≤ M) :
    lB A B ≤ M := by
  refine iSup_le fun b'' => iSup_le fun d'' => iSup_le fun L'' => iSup_le fun hc => ?_
  have hL'' : L'' ∈ lA A b'' := hc.2.2.1 ▸ Set.mem_singleton L''
  exact ((Item148HJ.residual_le L'' d'').trans
    (le_centralizer_of_mem_thetaComponentsAt hL''.1)).trans (hM b'' hc.2.1)

end Proof171Steps

end CFSG.RankThree.PartTwo.Sec17
