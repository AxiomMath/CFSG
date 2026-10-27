module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanSmallDefs
public import CFSG.LocalAnalysis.StandardType.GGStdUnitaryFourExcl
public import CFSG.LocalAnalysis.StandardType.GGPhanSmallStrict
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosAssemble
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSCornerDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanAD5
public import CFSG.LocalAnalysis.StandardType.GGRCWeylCard

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggSecFivePhanSmallFalseInput_of_small

    (hEn : GGSecFiveNSEnnolaSmallInput) (hU6 : GGSecFiveNSU6SmallInput)
    (hC : GGSecFiveNSCornerInput) (hW : GGNbrInnerWeylInput) :
    GGSecFivePhanSmallFalseInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hregion hns ι M e hpres hA
  have hA' := hA
  obtain ⟨n, e', hn, hM⟩ := hA
  have hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := fun i j hij =>
    GGIsWeylMatrixAD.le_three (Or.inl ⟨n, e', by omega, hM⟩) i j hij
  have hE := ggX_ennola_of_nonSplit hcfg hpres hle3 (Or.inl rfl) hns
  have hEn' := hEn G p B Bs x L D J 𝒦 hcfg hregion hns ι M e hpres hA'
  have hESU : GGInnerDiagOnLabel ggRowP_ESU p Bs L := by
    have h' : GGInnerDiagOnLabel
        (fun p lab => ggRowP_ESU p lab ∨ (ggRowP_Ennola p lab ∧ ¬ ggRowP_ESU p lab)) p Bs L :=
      hE.mono' fun lab hl => (em (ggRowP_ESU p lab)).imp id fun hn' => ⟨hl, hn'⟩
    rcases GGInnerDiagOnLabel.elim_or h' with h | h
    · exact h
    · exact absurd h hEn'
  have h3 : GGInnerDiagOnLabel
      (fun p lab => (ggRowP_ESU p lab ∧ lab.rank = 3) ∨
        ((ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) ∨
          (ggRowP_ESU p lab ∧ lab.rank ≠ 3 ∧ ¬ (lab.n = 1 ∧ lab.rank = 5)))) p Bs L :=
    hESU.mono' fun lab hl => by
      by_cases h1 : lab.rank = 3
      · exact Or.inl ⟨hl, h1⟩
      · by_cases h2 : lab.n = 1 ∧ lab.rank = 5
        · exact Or.inr (Or.inl ⟨hl, h2⟩)
        · exact Or.inr (Or.inr ⟨hl, h1, h2⟩)
  rcases GGInnerDiagOnLabel.elim_or h3 with h4 | h5
  ·
    refine not_ggInnerDiagOnLabel_unitary_four hcfg.1.1 (h4.mono' fun lab hl => ?_)
    obtain ⟨⟨hlab, hdvd⟩, hr⟩ := hl
    refine ⟨?_, hr, hdvd⟩
    rcases hlab with ⟨ht, -⟩ | ⟨ht, -⟩
    exacts [Or.inl ht, Or.inr ht]
  rcases GGInnerDiagOnLabel.elim_or h5 with h6 | h7
  · exact hU6 G p B Bs x L D J 𝒦 hcfg hregion hns ι M e hpres hA' h6
  have hcover := ggNSLie_cover_of_esu_pred (X := L)
    (P := fun p lab => ggRowP_ESU p lab ∧ lab.rank ≠ 3 ∧ ¬ (lab.n = 1 ∧ lab.rank = 5))
    (fun p lab hl => ⟨hl.1, by
      rintro ⟨hn1, hr | hr⟩
      exacts [hl.2.1 hr, hl.2.2 ⟨hn1, hr⟩]⟩) h7
  obtain ⟨lab, K, hKf, hKfin, hKchar, f, n', ψ, hlabP, hn'r, -, hcard, h4n, hker, hrange, hdvd,
    hacts, -⟩ := hcover
  letI : Field K := hKf
  letI : Finite K := hKfin
  letI : CharP K 2 := hKchar
  have hrk : 4 ≤ lab.rank := by
    rcases hlabP.1.1 with ⟨-, h3le⟩ | ⟨-, h3eq⟩
    · have := hlabP.2.1
      omega
    · exact absurd h3eq hlabP.2.1
  have hn5 : 5 ≤ n' := by omega
  have hloc : GGNSLocalHyp p B Bs K f n' ψ :=
    ggNSLocalHyp_of_routeCfg hcfg (X := L) (Or.inl rfl) hcard h4n hker hrange hdvd hacts
  obtain ⟨c, hc⟩ := ggNSLocal_position hC hloc
  rw [hrange] at hc
  obtain ⟨ε, -⟩ := hc
  have hAL : Nat.card ↥(ggAutomizer L Bs) = n'.factorial := by
    rw [← Nat.card_congr ε.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  have hJoin : Nat.card ↥(ggAutomizerJoin L Bs 𝒦) = (n + 1).factorial := by
    rw [← Nat.card_congr e.toEquiv, hM, card_coxeterGroup_reindex, l05nK3a_card_coxeterA]
  have hlt := ggPhanSmall_card_lt_join hW hcfg
  rw [hAL, hJoin] at hlt
  have h120 : (n + 1).factorial ≤ n'.factorial :=
    (Nat.factorial_le (by omega : n + 1 ≤ 5)).trans (Nat.factorial_le hn5)
  exact absurd (lt_of_lt_of_le hlt h120) (lt_irrefl _)

theorem ggSecFiveDataResPhanASmallInput_of_small


    (hEn : GGSecFiveNSEnnolaSmallInput) (hU6 : GGSecFiveNSU6SmallInput)
    (hC : GGSecFiveNSCornerInput) (hW : GGNbrInnerWeylInput) :
    GGSecFiveDataResPhanASmallInput :=
  ggSecFiveDataResPhanASmallInput_of_false (ggSecFivePhanSmallFalseInput_of_small hEn hU6 hC hW)

end CFSG.StandardType

end
