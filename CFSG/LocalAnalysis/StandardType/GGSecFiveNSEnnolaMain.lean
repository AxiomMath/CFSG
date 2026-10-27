module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaFork
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaTypeA
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaForkCox
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrCoxOrder
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaOrth
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaExcPlus
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaTwE6
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaTwE6Three
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSExcl
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrOfEnnola
public import Certificates.Certificate43
public import Certificates.Certificate1952
public import Certificates.Certificate3951
public import Certificates.Certificate13657
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6Holds
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenTwE6Three
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaCore

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggSecFiveNSEnnola_core
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) {m : ℕ} {σ : Fin m ≃ ι}
    (hM : M = (CoxeterMatrix.A m).reindex σ) {X : Subgroup G}
    (hX : X = L ∨ ((∃ y, GGNbr p B x D J y X) ∧ ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦))
    (hrk3 : p = 3 → GGInnerDiagOnLab GGTableBTwE6ThreeLabel p Bs X →
      ∀ hN : Bs ≤ Subgroup.normalizer (X : Set G), p ^ 5 ≤ Nat.card (ggGamma X hN).range)
    (hrow : GGInnerDiagOnLabel (fun p lab => ggRowP_Ennola p lab ∧ ¬ ggRowP_ESU p lab) p Bs X) :
    False := by
  have hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := by
    intro i j _
    rw [hM, CoxeterMatrix.reindex_apply]
    simp only [CoxeterMatrix.A, Matrix.of_apply]
    split_ifs <;> omega
  have hle : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦 := by
    rcases hX with rfl | ⟨-, hle⟩
    · exact ggAutomizer_le_ggAutomizerJoin (Or.inl rfl)
    · exact hle
  exact ggSecFiveNSEnnola_core_of_noReflFork hcfg hpres hle3 hX
    (ggX_noReflFork_typeA hcfg hpres hM hle3 hle) hrk3 hrow

theorem ggSecFiveNSEnnola_absurd
    (hRk : GGTwE6ThreeNbrRankInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) {m : ℕ} {σ : Fin m ≃ ι}
    (hM : M = (CoxeterMatrix.A m).reindex σ) {X : Subgroup G}
    (hX : X = L ∨ ((∃ y, GGNbr p B x D J y X) ∧ ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦))
    (hrow : GGInnerDiagOnLabel (fun p lab => ggRowP_Ennola p lab ∧ ¬ ggRowP_ESU p lab) p Bs X) :
    False :=
  ggSecFiveNSEnnola_core hcfg hpres hM hX (fun hp3 hLab hN => by
    subst hp3
    rcases hX with rfl | ⟨⟨y, hnb⟩, -⟩
    · exact ggTwE6ThreeBstarRankInput_holds G 3 B Bs x X D J hcfg.1.1 hLab hN
    · have hLab' : GGInnerDiagOnLab GGTwE6BadLabel 3 Bs X := hLab
      exact hRk G 3 B Bs x L D J hcfg.1.1 rfl y X hnb hLab' hN
        (ggTorusSelfCent_ggGamma hN hcfg.1.1.2.1.2.2.2)) hrow

theorem ggSecFiveNSEnnola_absurd_L
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) {m : ℕ} {σ : Fin m ≃ ι}
    (hM : M = (CoxeterMatrix.A m).reindex σ)
    (hrow : GGInnerDiagOnLabel (fun p lab => ggRowP_Ennola p lab ∧ ¬ ggRowP_ESU p lab) p Bs L) :
    False :=
  ggSecFiveNSEnnola_core hcfg hpres hM (Or.inl rfl) (fun hp3 hLab hN => by
    subst hp3
    exact ggTwE6ThreeBstarRankInput_holds G 3 B Bs x L D J hcfg.1.1 hLab hN) hrow

theorem ggSecFiveNSEnnolaInput_of_rank
    (hRk : GGTwE6ThreeNbrRankInput) : GGSecFiveNSEnnolaInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg _ ι M e hpres hA X hX _ hrow
  obtain ⟨m, σ, -, hM⟩ := hA
  exact ggSecFiveNSEnnola_absurd hRk hcfg hpres hM hX hrow

end CFSG.StandardType

end
