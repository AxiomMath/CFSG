module

public import CFSG.LocalAnalysis.StandardType.GGNbrD4TwoField
public import CFSG.LocalAnalysis.StandardType.GGNbrD4TwoCommonJ
public import CFSG.LocalAnalysis.StandardType.GGResidualRk1FrameRest
import CFSG.LocalAnalysis.StandardType.GGTCJHolds
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseOrthFrame
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseRankFive

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem GGSecFiveRouteCfg.not_unitary_higher_of_D4two_nbr_eq_center
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {y : G} {X : Subgroup G}
    (hnb : GGNbr p B x D J y X) (hRig : GGLabelRigidInput)
    (hmarkX : GGInnerDiagOnLabel
      (fun p lab => ggRowP_EOmP p lab ∧ lab.n = 1 ∧ lab.rank = 4) p Bs X)
    (hEq : B = Bs) (hZ : Subgroup.center X ≠ ⊥)
    (hmarkL : GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ 2 ≤ lab.n) p Bs L) :
    False := by
  have hN := GGInnerDiagOn.le_normalizer
    (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.2) hmarkX : GGInnerDiagOn Bs X)
  obtain ⟨rfl, -⟩ := hcfg.1.1.card_gamma_of_D4two_nbr hnb hRig hmarkX hN
  have hJ := (hcfg.original_J_component_of_D4two_nbr_eq_center
    hnb hRig hmarkX hEq hZ).2
  exact hcfg.1.1.not_unitary_higher_of_D4two_component TCJ.ggTCJKnown_holds hRig
    hnb hmarkX hmarkL hJ

theorem GGSecFiveRouteCfg.unitary_baseLabel_field_two_singular_of_D4two_nbr_eq_center
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hRig : GGLabelRigidInput)
    {y : G} {X : Subgroup G} (hnb : GGNbr p B x D J y X)
    (hmarkX : GGInnerDiagOnLabel
      (fun p lab => ggRowP_EOmP p lab ∧ lab.n = 1 ∧ lab.rank = 4) p Bs X)
    (hEq : B = Bs) (hZ : Subgroup.center X ≠ ⊥) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) (hnsL : ¬ GGSplitLie p L) :
    GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧
      lab.n = 1 ∧ 3 ∣ lab.rank + 1) p Bs L := by
  have hu := hcfg.unitary_baseLabel_singular_two_of_D4two_nbr_of_eq
    hRig hnb hmarkX hEq hpres h3 hnsL
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hcfg
  have hpos : ∀ lab, ggRowP_ESU p lab → 1 ≤ lab.n := by
    intro lab hl
    by_contra hn
    have hn0 : lab.n = 0 := by omega
    have hd : p ∣ 2 := by simpa [hn0] using hl.2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)
  have hs : GGInnerDiagOnLabel (fun p lab =>
      (ggRowP_ESU p lab ∧ lab.n = 1 ∧ 3 ∣ lab.rank + 1) ∨
      (ggRowP_ESU p lab ∧ 2 ≤ lab.n)) p Bs L :=
    largeEvenMarking_mono (fun lab _ _ _ _ _ h => ⟨by
      by_cases hn : lab.n = 1
      · exact Or.inl ⟨h.1.1, hn, h.1.2 hn⟩
      · exact Or.inr ⟨h.1.1, by have := hpos lab h.1.1; omega⟩, h.2⟩) hu
  rcases GGInnerDiagOnLabel.elim_or hs with htwo | hhigh
  · exact htwo
  · exact (hcfg.not_unitary_higher_of_D4two_nbr_eq_center
      hnb hRig hmarkX hEq hZ hhigh).elim

end CFSG.StandardType

end
