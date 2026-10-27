module

public import CFSG.LocalAnalysis.StandardType.GGD5LabelExclUnit
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenCore
import CFSG.LocalAnalysis.StandardType.GGForkJrPumpLattice

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

theorem qtwoDU5_not_twA45
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) (hNoTr : GGNoTransvection 3 Bs) {K : Subgroup G}
    (hmark : GGInnerDiagOnLabel
      (fun _ lab => lab = ⟨.twA, 4, 1⟩ ∨ lab = ⟨.twA, 5, 1⟩) 3 Bs K)
    (hγ : ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G), Nat.card (ggGamma K hN).range = 3 ^ 4)
    (hZ : Nat.card ↥(Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)) ≤ 3)
    (h192 : 192 ∣ Nat.card (ggAutomizer K Bs)) : False := by
  obtain ⟨-, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hSC' : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  rcases GGInnerDiagOnLabel.elim_or hmark with h4 | h5
  · obtain ⟨hperf, lab, hlab, hraw⟩ := h4
    obtain ⟨-, -, -, -, -, -, -, hEq, -, -⟩ := largeEvenRawDatum_exists hraw
    obtain rfl := hEq
    obtain ⟨R, iR, I, F, hconj⟩ :=
      largeEvenRawDatum_exists (lup10eU_labelAll_twA4_autCard _ hraw)
    obtain ⟨⟨-, -, θ, -, hN, hind⟩, hSC⟩ := hconj
    have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I :=
      fun b hb => ggLAut_mem_of_induces K θ hN hind hb
    have hcardγ := hγ hN
    have hTB : GGTorusTBGroup 3 4 R I K (ggQuotHom θ) (ggGamma K hN).range :=
      ggTorusTBGroup_of_marking Nat.prime_three hBs hSC' hperf θ hN hBsI
        (le_of_eq hcardγ.symm) (by rw [hcardγ]; norm_num)
    obtain ⟨hsurj, hker, hcomm, hA, hAI, -, h3, hSelf⟩ := hTB
    have hinner : Nat.card (ggAutomizer (MulAut.conj : ↥K →* MulAut ↥K).range
        (ggGamma K hN).range) = 120 :=
      (hSC K (ggQuotHom θ) hsurj hker hcomm (ggGamma K hN).range hA hAI h3 hSelf).2
    have hdvd := card_ggAutomizer_dvd_gamma Nat.prime_three hBs hNoTr hN hZ
    rw [hinner] at hdvd
    exact absurd (h192.trans hdvd) (by norm_num)
  · obtain ⟨hperf, lab, hlab, hraw⟩ := h5
    obtain ⟨-, -, -, -, -, -, -, hEq, -, -⟩ := largeEvenRawDatum_exists hraw
    obtain rfl := hEq
    obtain ⟨R, iR, I, F, hconj⟩ :=
      largeEvenRawDatum_exists (lup10eU_labelAll_twA5_inner _ hraw)
    obtain ⟨⟨-, -, θ, -, hN, hind⟩, hInnerCard⟩ := hconj
    have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I :=
      fun b hb => ggLAut_mem_of_induces K θ hN hind hb
    have hcardγ := hγ hN
    have hTB : GGTorusTBGroup 3 4 R I K (ggQuotHom θ) (ggGamma K hN).range :=
      ggTorusTBGroup_of_marking Nat.prime_three hBs hSC' hperf θ hN hBsI
        (le_of_eq hcardγ.symm) (by rw [hcardγ]; norm_num)
    obtain ⟨hsurj, hker, hcomm, hA, hAI, -, h3, hSelf⟩ := hTB
    have hinner : Nat.card (ggAutomizer (MulAut.conj : ↥K →* MulAut ↥K).range
        (ggGamma K hN).range) = 720 :=
      hInnerCard K (ggQuotHom θ) hsurj hker hcomm (ggGamma K hN).range hA hAI
        (le_of_eq hcardγ.symm) hSelf
    have hdvd := card_ggAutomizer_dvd_gamma Nat.prime_three hBs hNoTr hN hZ
    rw [hinner] at hdvd
    exact absurd (h192.trans hdvd) (by norm_num)

end CFSG.StandardType.QTwo

end
