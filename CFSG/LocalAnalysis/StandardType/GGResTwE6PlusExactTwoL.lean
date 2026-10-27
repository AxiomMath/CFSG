module

public import CFSG.LocalAnalysis.StandardType.GGResTwoCells
import CFSG.LocalAnalysis.StandardType.GGResTwE6PlusIOne
import CFSG.LocalAnalysis.StandardType.GGResExcSplitExactTwoL
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1CenterE6
import CFSG.LocalAnalysis.StandardType.GGResJOpenLabel
import CFSG.LocalAnalysis.StandardType.GGTCJHolds
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGTBE6
import CFSG.LocalAnalysis.StandardType.GGTBTorLiftRowsHolds
import CFSG.LocalAnalysis.StandardType.GGTBTorLiftRowsCls

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

theorem GGResHyp.false_of_exact2_L_twE6Plus
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hp5 : 5 ≤ p)
    (hM : GGInnerDiagOnLabel (fun p lab => lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n + 1) p Bs L)
    (hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) = D)
    (hD : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) : False := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hT : GGTBTorAll := ggTBTorAll_of_remaining trivial
  have hrow : ∀ lab : LargeEvenLabel, (lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n + 1) →
      ∃ (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ) (M : CoxeterMatrix (Fin N)),
        GGTBTorRowAt p lab r m N C M ∧ 5 ≤ r := by
    rintro lab ⟨ht, hpq⟩
    have hEnn : ggTorEnn p lab = 1 := ggTorEnn_eq_one_of_dvd_add_one hpq
    have hm : p ∣ ggTorM lab := by
      simpa [ggTorM, ht] using hpq
    exact ⟨_, _, _, _, _, GGTBTorRowAt.e6Ind hp3 (Or.inr ht) hm, by omega⟩
  have hm6 : 6 ≤ LargeEvenTwoLocalRank p G := by
    obtain ⟨_, r, _, _, _, _, _, _, θ, _, _, hperf, -, -, hr5, -, hlift, -, -⟩ :=
      l05nPlQ_marking_with (ggTBTorWRows_of_all hT) ggTBTorLiftRows_holds hp2
        (fun r _ _ _ _ => 5 ≤ r) (GGInnerDiagOnLabel.mono_label (fun lab h => hrow lab h) hM)
    have := hH.succ_le_twoLocalRank_of_torusLift_L hperf θ hlift
    omega
  have hMc : GGInnerDiagOnLabel (fun p lab => S2MathAs51642Interfaces.CenterPrimeTo p lab ∧
      (lab.tag = .E6 ∨ lab.tag = .twE6)) p Bs L :=
    GGInnerDiagOnLabel.mono_label (fun lab h => by
        obtain ⟨ht, -⟩ := h
        refine ⟨⟨?_, ?_⟩, Or.inr ht⟩
        · simp [S2MathAs51642Interfaces.SmallDerived, ht]
        · simp [ht, hp3]) hM
  have hJ : GGInnerDiagOn Bs J := q1CenterPrimeE6TwE6_holds G p B Bs x L D J hH.1 hMc
  have hJlab : GGInnerDiagOnLabel (fun _ _ => True) p Bs J :=
    (GGInnerDiagOn.label (fun _ _ => True) p hJ).mono_label (fun _ _ => trivial)
  have hfwd := (hH.fix_mem_centralizer_J_or_twE6_of_tcj_of_six hT ggTBTorLiftRows_holds
    TCJ.ggTCJKnown_holds ggLabelRigidInput_holds hm6 hJlab).resolve_right (by
      rintro ⟨-, lab, -, hraw⟩
      obtain ⟨R, _, I, F, -, -, θ, ⟨-, h3⟩, -⟩ := largeEvenRawDatum_exists hraw
      obtain ⟨-, hp3', -⟩ := h3
      exact hp3 hp3')
  have hL : GGInnerDiagOnLabel (fun p lab => GGTBTorCov p lab ∧ ¬ ggSingularBaseLabel p lab)
      p Bs L :=
    GGInnerDiagOnLabel.mono_label (fun lab h => by
        obtain ⟨r, m, N, C, M, hr, -⟩ := hrow lab h
        refine ⟨⟨r, m, N, C, M, hr⟩, ?_⟩
        obtain ⟨ht, -⟩ := h
        simp [ggSingularBaseLabel, ht]) hM
  exact hH.false_of_exact2_nonsingular_L hT ggTBTorLiftRows_holds hfwd hL hI1 hD

theorem ggResMultiNodeRestTwoCellInput_twE6Plus :
    GGResMultiNodeRestTwoCellInput
      (fun p lab => lab.tag = .twE6 ∧ p ≠ 3 ∧ p ∣ 2 ^ lab.n + 1) := by
  apply GGResMultiNodeRestTwoCellInput.of_false
  intro G _ _ p _ B Bs x L D J y K hH hL hD
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hp3 : p ≠ 3 := by
    obtain ⟨-, lab, -, hraw⟩ := hL
    obtain ⟨R, _, I, F, -, -, θ, ⟨-, h3, -⟩, -⟩ := largeEvenRawDatum_exists hraw
    exact h3
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    have h4 : p ≠ 4 := fun h => by subst h; norm_num at hp
    omega
  have hM : GGInnerDiagOnLabel (fun p lab => lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n + 1) p Bs L :=
    hL.mono_label (fun _ h => ⟨h.1, h.2.2⟩)
  exact hH.false_of_exact2_L_twE6Plus hp5 hM (hH.iOne_of_twE6Plus_L hp5 hM) hD

end CFSG.StandardType

end
