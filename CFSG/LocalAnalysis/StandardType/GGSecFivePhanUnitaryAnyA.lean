module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaMain
public import CFSG.LocalAnalysis.StandardType.GGNsq2Main
public import CFSG.LocalAnalysis.StandardType.GGNsq2NbrMain
public import CFSG.LocalAnalysis.StandardType.GGMemberRowsDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveDataResDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveRowMember

public section

namespace CFSG.StandardType

open CFSG.Assembly


theorem ggX_esu_of_nonSplit_anyA (hRk : GGTwE6ThreeNbrRankInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    {m : ℕ} {σ : Fin m ≃ ι} (hM : M = (CoxeterMatrix.A m).reindex σ) {X : Subgroup G}
    (hX : X = L ∨ ((∃ y : G, GGNbr p B x D J y X) ∧ ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦))
    (hXns : ¬ GGSplitLie p X) :
    GGInnerDiagOnLabel ggRowP_ESU p Bs X := by
  have hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := by
    intro i j hij
    rw [hM, CoxeterMatrix.reindex_apply]
    simp only [CoxeterMatrix.A, Matrix.of_apply]
    split_ifs <;> omega
  have hE := ggX_ennola_of_nonSplit hcfg hpres hle3 hX hXns
  have h' : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∨ (ggRowP_Ennola p lab ∧ ¬ ggRowP_ESU p lab)) p Bs X :=
    hE.mono' fun lab hl => (em (ggRowP_ESU p lab)).imp id fun hn => ⟨hl, hn⟩
  rcases GGInnerDiagOnLabel.elim_or h' with h | h
  · exact h
  · exact (ggSecFiveNSEnnola_absurd hRk hcfg hpres hM hX h).elim

theorem ggMemberUnitary_anyA (hRk : GGTwE6ThreeNbrRankInput) (hU : GGU62OuterDiagInput) (hTB : GGTBFixInput)
    (hWA : GGTBFixNbrXInput) (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hL : ¬ GGSplitLie p L)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) {m : ℕ} {σ : Fin m ≃ ι}
    (hM : M = (CoxeterMatrix.A m).reindex σ)
    (hno6 : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6)
    {X : Subgroup G}
    (hX : X = L ∨ ((∃ y : G, GGNbr p B x D J y X) ∧ ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦))
    (hXns : ¬ GGSplitLie p X) :
    GGMemberUnitary p Bs X := by
  have hcov : GGMemberUnitary p Bs L :=
    ggNsq2Cov_of_esu hcfg.1.1 (ggX_esu_of_nonSplit_anyA hRk hcfg hpres hM (Or.inl rfl) hL)
      (ggNsq2L_of_u62 hU hTB hWA hcfg hpres hM hno6)
  rcases hX with hXL | hXnb
  · rw [hXL]
    exact hcov
  · have hE := ggX_esu_of_nonSplit_anyA hRk hcfg hpres hM (Or.inr hXnb) hXns
    have h' : GGInnerDiagOnLabel (fun p lab =>
        (ggRowP_ESU p lab ∧ lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5)) ∨
        (ggRowP_ESU p lab ∧ ¬ (lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5)))) p Bs X :=
      hE.mono' fun lab hl => (em (lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5))).imp
        (fun h3 => ⟨hl, h3⟩) (fun h3 => ⟨hl, h3⟩)
    rcases GGInnerDiagOnLabel.elim_or h' with h | h
    · exact (ggNsq2Nbr_of_cov hLB hP hcfg hpres hM hno6 hcov hXnb h).elim
    · exact h

end CFSG.StandardType

end
