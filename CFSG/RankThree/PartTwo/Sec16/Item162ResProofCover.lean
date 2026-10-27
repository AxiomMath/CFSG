module

public import CFSG.RankThree.PartTwo.Sec16.Item163StepsPtProof
import CFSG.RankThree.PartTwo.Sec16.Item162ResProofTools
public import CFSG.RankThree.PartTwo.Sec16.Item162Proof

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15

namespace Res162

variable {G : Type} [Group G] [Finite G]

theorem meetsY4_of_cover
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L) (h1514 : Item1514R)
    (h1523 : Item1523R) (h153 : Item153MainR) (hobs : Claim153ObsR) (h1411 : Item1411_1R)
    (hM : Step163MeetsPoint) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    (hcov : L = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 L) : MeetsY4 A (lB A) L Y := by
  have hD := h.toSec13Data
  obtain ⟨e, Le, he, hLe, hm⟩ := exists_point_meetsY4 h (fun G _ _ A c' L' hR' _ =>
    h1514 G A c' L' hR') h1523 h153 hobs h1411 hM hY
  by_cases hec : Subgroup.zpowers e = Subgroup.zpowers c
  · rwa [eq_of_zpowers_eq h he hLe hec] at hm
  have he' : Sec15R G A e Le := sec15R_of_point h he hLe
  have hne : omegaA A ≠ {Subgroup.zpowers e} := fun hΩ => hec (by
    have := hΩ ▸ h.zpowers_mem_omegaA
    exact (Set.mem_singleton_iff.mp this).symm)
  rcases h1514 G A e Le he' Y hY hm with ⟨-, -, hΩ, -⟩ | ⟨h7, -, hT, hY'⟩ | ⟨-, -, -, hΩ, -⟩
  · exact (hne hΩ).elim
  · rcases hY' with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
    ·
      exfalso
      obtain ⟨w, hw, hcw⟩ := hT.2 (Subgroup.zpowers c) h.zpowers_mem_omegaA
      obtain ⟨φL⟩ := nonempty_a7_of_map_conj (map_conj_eq_of_zpowers h he hLe hw hcw) h7
      have hsc := sectionCentralizer_eq_zpowers_of_cover h.mem_lA hY.prop.1.1.2 hcov
        (by rw [Nat.card_congr φ.toEquiv, Nat.card_congr φL.toEquiv])
      obtain ⟨X, hX, hXLY⟩ := hm
      have heA : e ∈ A := (zpowers_mem_omegaA_iff.mp he).1
      have hXe : X ≤ Subgroup.centralizer {e} :=
        (hXLY.trans inf_le_left).trans (le_centralizer_of_mem_thetaComponentsAt hLe.1)
      have hesc := mem_sectionCentralizer_of_meets hD.isElemAbelian heA hY.prop.1.1.2 φ hX
        (hXLY.trans inf_le_right) hXe
      rw [hsc] at hesc
      exact hec (zpowers_eq_of_mem_zpowers h.zpowers_mem_omegaA he hesc)
    ·
      exact meetsY4_of_alternating_ten h hT.1 hY φ he hLe hm
  · exact (hne hΩ).elim

end Res162

end CFSG.RankThree.PartTwo.Sec16
