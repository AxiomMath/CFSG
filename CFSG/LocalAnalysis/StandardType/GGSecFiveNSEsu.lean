module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeakNbr
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSExcl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRowMember
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanAD5

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggX_esu_of_nonSplit
    (hEn : GGSecFiveNSEnnolaInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hL : ¬ GGSplitLie p L) {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hA : ∃ (m : ℕ) (σ : Fin m ≃ ι), 5 ≤ m ∧ M = (CoxeterMatrix.A m).reindex σ) {X : Subgroup G}
    (hX : X = L ∨ GGSecFiveWeakNbr p B Bs x L D J 𝒦 X) (hXns : ¬ GGSplitLie p X) : GGInnerDiagOnLabel ggRowP_ESU p Bs X := by
  have hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := fun i j hij =>
    GGIsWeylMatrixAD5.le_three (Or.inl hA) i j hij
  have hE := ggX_ennola_of_nonSplit hcfg hpres hle3 hX hXns
  have h' : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∨ (ggRowP_Ennola p lab ∧ ¬ ggRowP_ESU p lab)) p Bs X :=
    hE.mono' fun lab hl => (em (ggRowP_ESU p lab)).imp id fun hn => ⟨hl, hn⟩
  rcases GGInnerDiagOnLabel.elim_or h' with h | h
  · exact h
  · exact absurd h (hEn G p B Bs x L D J 𝒦 hcfg hL ι M e hpres hA X hX hXns)

end CFSG.StandardType

end
