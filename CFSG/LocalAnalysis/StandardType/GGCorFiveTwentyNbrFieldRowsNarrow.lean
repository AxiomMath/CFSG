module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyNbrFieldRows
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrow

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem cfrn_two_le_n_of_ggLabelIso {p : ℕ} {lab labJ labK : LargeEvenLabel}
    (hrow : GGTablePRow p labJ labK) (hiso : GGLabelIso lab labJ) (h2 : 2 ≤ lab.n) :
    2 ≤ labJ.n := by
  rcases hiso with rfl | ⟨-, -, -, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
  · exact h2
  · omega
  all_goals first
    | (rw [h]; exact h2)
    | (rw [h]; dsimp only; omega)
    | (exfalso; rw [h] at hrow; simp [GGTablePRow] at hrow)

theorem ggNbr_fieldRow_of_not_labelOk_narrow (hRig : GGLabelRigidInput) (hTCJ : GGTCJKnown)
    (hTP : GGNbrTablePNbrInputOn GGRegimeFieldTwo) {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hH : GGCorFiveTwentyHyp p B Bs x L D J)
    (hq : GGInnerDiagOnLabel GGLabQFour p Bs L) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) (hK : ¬ GGInnerDiagOnLabel GGLabNbrOk p Bs K) :
    (p = 3 ∧ GGHasLabel ⟨.twE6, 0, 1⟩ (K ⧸ Subgroup.center K)) ∨
      (p = 7 ∧ GGHasLabel ⟨.A, 8, 1⟩ (K ⧸ Subgroup.center K)) := by
  have hcfg := hH.1
  have hInn := hH.2.2.1
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  obtain ⟨labK, hKΛ, hhasK, -⟩ := largeEvenMarking_exists_hasLabel (hInn.2 y K hnb)
  obtain ⟨labL, labJ, -, hq4, -, hJΛ, hdvd, hhasJ⟩ :=
    ggNbr_label_J_of_tcj_onLabel hTCJ hcfg hq hnb
  have hJ2 : 2 ≤ labJ.n := le_trans hq4 (Nat.le_of_dvd (by have := hJΛ.1; omega) hdvd)
  have hnokK : ¬ GGLabNbrOk p labK := fun hok => hK (largeEvenMarking_mono
    (fun _ _ _ _ _ _ ⟨he, hP⟩ => ⟨he ▸ hok, hP⟩)
    (ggInnerDiagOn_relabel hRig (hInn.2 y K hnb) hKΛ hhasK))
  have hK1 : labK.n = 1 := by
    have h := hnokK
    simp only [GGLabNbrOk, not_or, not_le] at h
    have h1 := hKΛ.1
    omega
  have hKnA : ¬ (labK.tag = .A ∧ p = 3 ∧ 5 ≤ labK.rank) := by
    have h := hnokK
    simp only [GGLabNbrOk, not_or, not_le] at h
    rintro ⟨ht, hp3, hr⟩
    exact h.2 ⟨ht, hK1, hp3, hr⟩
  have hreg : GGRegimeFieldTwo p (Nat.card Bs) labJ labK := ⟨hJ2, hK1, hKnA⟩
  obtain ⟨jlab, klab, hjΛ, hkΛ, hrow, hhasJ1, hhasK1⟩ :=
    hTP G p B Bs x L D J y K hcfg hInn.1 (hInn.2 y K hnb) hnb labJ labK hJΛ hKΛ hreg hhasJ
      hhasK
  have hj2 : 2 ≤ jlab.n :=
    cfrn_two_le_n_of_ggLabelIso hrow (hRig labJ jlab _ hJΛ hjΛ hhasJ hhasJ1) hJ2
  have hnok : ¬ GGLabNbrOk p klab := fun hok => hK (largeEvenMarking_mono
    (fun _ _ _ _ _ _ ⟨he, hP⟩ => ⟨he ▸ hok, hP⟩)
    (ggInnerDiagOn_relabel hRig (hInn.2 y K hnb) hkΛ hhasK1))
  rcases ggTablePRow_fieldTwo hp hrow hkΛ hj2 hnok with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, hhasK1⟩
  · exact Or.inr ⟨rfl, hhasK1⟩

theorem GGCorFiveTwentyInputNbrQTwoQFourNoA11CfgR3.of_fieldRows_narrow
    (hRig : GGLabelRigidInput) (hTCJ : GGTCJKnown)
    (hTP : GGNbrTablePNbrInputOn GGRegimeFieldTwo) (h : GGCorFiveTwentyInputNbrFieldRows) :
    GGCorFiveTwentyInputNbrQTwoQFourNoA11CfgR3 :=
  fun G _ _ p B Bs x L D J hH hq hN hA hR => h G p B Bs x L D J hH hq hN hA hR
    fun _ _ hnb hK => ggNbr_fieldRow_of_not_labelOk_narrow hRig hTCJ hTP hH hq hnb hK

end CFSG.StandardType

end
