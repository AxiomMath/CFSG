module

public import CFSG.LocalAnalysis.StandardType.GGResidualGenFrame
import CFSG.LocalAnalysis.StandardType.GGRootGenResQFourL
import CFSG.LocalAnalysis.StandardType.GGRootGenResQFourTwE6Nbr
import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRootGenKG
import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenTwFinal
import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenTwEightMain
import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6Holds
import CFSG.LocalAnalysis.StandardType.GGSecFiveL1AbsorbAux

public section

namespace CFSG.StandardType

private theorem resGen3_ggFixG_eq_ggHyperplane {G : Type} [Group G] (Bs : Subgroup G)
    (r : MulAut ↥Bs) : ggFixG Bs r = ggHyperplane Bs r := by
  have h : ggFix r = MonoidHom.eqLocus (r : ↥Bs →* ↥Bs) (MonoidHom.id ↥Bs) := by
    ext b; rfl
  rw [ggFixG, ggHyperplane, h]

theorem le_iSup_ggRankOneIn_of_rootCompGenAvoiding {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {Bs X : Subgroup G} (h : GGRootCompGenAvoiding p Bs X) :
    X ≤ ⨆ r : MulAut ↥Bs, ⨆ (_ : r ∈ ggAutomizer X Bs), ⨆ (_ : GGIsReflection p r),
      ggRankOneIn X Bs r := by
  refine (h 1).le.trans (iSup_le fun t => iSup_le fun Jt => iSup_le fun ht => ?_)
  obtain ⟨-, hrefl, hind, hJX, hJC, hJp⟩ := ht
  have hJperf : ⁅Jt, Jt⁆ = Jt := by
    have := CFSG.ComponentClassification.CatalogueBHeldSmallCore.pComponent_perfect p _ hJp
    exact Subgroup.isPerfect_iff.mp (Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hJC).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hJC).surjective)
  have hJR : Jt ≤ ggRankOneIn X Bs t := by
    rw [resGen3_ggFixG_eq_ggHyperplane] at hJC
    exact ggL1Ab_perfect_le_ggOTwoPrime_of_le (le_inf hJX hJC) hJperf
  have htA : t ∈ ggAutomizer X Bs := by
    obtain ⟨g, hgJ, hgN, hg⟩ := hind
    exact Subgroup.subset_closure ⟨g, hJX hgJ, hgN, hg⟩
  exact le_iSup_of_le t (le_iSup_of_le htA (le_iSup_of_le hrefl hJR))

theorem ggGenConcl_of_twE6Three_resGen
    (hRk : GGTwE6ThreeNbrRankInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {X : Subgroup G}
    (hXw : X = L ∨ GGSecFiveWeakNbr p B Bs x L D J 𝒦 X) (hp3 : p = 3)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ 2 ≤ lab.n) p Bs X) :
    GGGenConcl M Bs X L 𝒦 e := by
  have hKG : GGTwE6ThreePlusKGAvoid := ggTwE6ThreePlusKGAvoid_of_lss92
    (PhiTwoRootGen.phiTwoTwE6GenInput_of_eight' PhiTwoRootGen.phiTwoTwE6Eight_holds)
  have hXA : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦 := by
    rcases hXw with rfl | hw
    · exact ggAutomizer_le_ggAutomizerJoin (Or.inl rfl)
    · exact hw.2
  subst hp3
  refine ggGenConcl_of_le_iSup_isReflection hcfg hpres h3 hXA
    (le_iSup_ggRankOneIn_of_rootCompGenAvoiding ?_)
  rcases hXw with rfl | ⟨⟨y, hnb⟩, -⟩
  · exact ggRootCompGenAvoiding_L_resL ggTwE6ThreeBstarRankInput_holds hKG hcfg.1.1
      (hmark.mono_label fun _ h => ⟨h.1.1, rfl, h.2, h.1.2⟩)
  · exact ggRootCompGenAvoiding_nbr_twE6ThreePlus hRk hKG hcfg.1.1 hnb
      (hmark.mono_label fun _ h => ⟨⟨h.1.1, rfl, h.1.2⟩, h.2⟩)

end CFSG.StandardType

end
