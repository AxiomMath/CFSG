module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggWTP8_secFiveE6TwoSeven_false {G : Type} [Group G] [Finite G]
    (hRig : GGLabelRigidInput) (hTCJ : GGTCJKnown) (hTP : GGSecFiveA8TablePInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (h : GGSecFiveRestHyp p B Bs x L D J) {y : G} {K : Subgroup G} (hK : GGNbr p B x D J y K)
    (hp : p = 7) (hE : GGHasLabel ⟨.E6, 0, 1⟩ (K ⧸ Subgroup.center K)) : False := by
  subst hp
  obtain ⟨lab, labJ, hlab, hsplit, hhasL, hlabJ, hdvd, hhasJ⟩ := ggNbr_label_J_of_tcj hTCJ h.1 hK
  have h3 : 3 ∣ lab.n := largeEvenSplit_seven_dvd hsplit
  have hn1 : 1 ≤ lab.n := hlab.1
  obtain ⟨hTPJ, hTPL⟩ := hTP G 7 B Bs x L D J h rfl y K hK (Or.inr hE)
  obtain ⟨jlab, klab, hjΛ, hkΛ, hrow, hhasJ1, hhasK1⟩ := hTPJ labJ hlabJ hhasJ
  have hkE : klab = ⟨.E6, 0, 1⟩ := eq_of_ggLabelIso_of_exc (Or.inr rfl)
    (hRig klab ⟨.E6, 0, 1⟩ _ hkΛ largeEvenInLambda2_e6 hhasK1 hE)
  subst hkE
  obtain ⟨t, r, n⟩ := jlab
  obtain ⟨rfl, rfl⟩ := ggTablePRow_e6_left hrow
  have hJ := eq_of_ggLabelIso_triD4 (hRig labJ ⟨.triD4, r, 1⟩ _ hlabJ hjΛ hhasJ hhasJ1)
  subst hJ
  have := Nat.le_of_dvd one_pos hdvd
  omega

end CFSG.StandardType

end
