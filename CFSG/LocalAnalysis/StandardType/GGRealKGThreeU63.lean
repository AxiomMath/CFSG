module

public import CFSG.LocalAnalysis.StandardType.GGRealKGThreeUDvd
public import CFSG.LocalAnalysis.StandardType.GGTableBUnit63Main
public import CFSG.LocalAnalysis.StandardType.GGNbrU63

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Subgroup


theorem ggReflRealizedIn_three_U63 (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hNT : GGNoTransvection p Bs) (hp3 : p = 3)
    {X : Subgroup G} (hX : X = L ∨ ∃ y, GGNbr p B x D J y X)
    (hq : GGInnerDiagOnLabel (fun p lab => GGLabQFour p lab ∧ GGNbrInner937U63Label p lab) p Bs
      X) :
    GGReflRealizedIn p Bs X := by
  subst hp3
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hSC : ∀ g ∈ centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨hXc, lab, hlab, hraw'⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => GGLabQFour 3 lab ∧ GGNbrInner937U63Label 3 lab)
    (P' := fun R _ I _ => GGTorusRootSL2 3 4 R I)
    (fun lab _ hs => by
      obtain ⟨t, l, n⟩ := lab
      obtain ⟨h2, ⟨ht, -, hpn, -⟩, h5, -⟩ := hs
      dsimp only at ht h5 h2 hpn
      subst ht h5
      exact largeEvenLabelAll_torusRootSL2_four_U63 h2 hpn)
    (fun _ _ _ _ _ _ hP => hP.1) hq
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, h3I⟩, hT⟩ := largeEvenRawDatum_exists hraw'
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hBsN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces X θ hBsN h3I hb
  rcases hX with rfl | ⟨y, hnb⟩
  · have hM : GGInnerDiagOnLab GGUnitDvd63Label 3 Bs X :=
      largeEvenMarking_mono (fun lab _ _ _ _ _ hP => by
        obtain ⟨t, l, n⟩ := lab
        obtain ⟨⟨-, ⟨ht, hl3, hpn, hpd⟩, h5, -⟩, hN, hI⟩ := hP
        dsimp only at ht hl3 hpn hpd h5
        subst ht
        exact ⟨⟨⟨rfl, hl3, hpn, hpd⟩, h5, rfl⟩,
          Or.inr (Or.inl ⟨by simp [LargeEvenUntwisted], by simp, hpn⟩), hN, hI⟩) hq
    obtain ⟨hr, h3⟩ := card_range_ggGamma_unitDvd63 hcfg hM hBsN
    exact ggReflRealizedIn_of_rootSL2 hp hp2 hBs hSC hNT hXc θ hBsN hBsI hr h3 hT
  · exact ggReflRealizedIn_of_rootSL2 hp hp2 hBs hSC hNT hXc θ hBsN hBsI
      (ggUnitDvd63NbrRankInput_holds hLB hSP G 3 B Bs x L D J hcfg y X hnb hBsN
        (GGInnerDiagOnLabel.mono_label (fun _ h => h.2) hq))
      (pow_three_le_card_range_ggGamma_bstar hcfg hnb hBsN) hT

theorem ggReflRealizedQFourInputThree_of_rootSL2On_U63 (hLB : GGLBalanceInput)
    (hSP : GGStdSubPrimeInput)
    (hKG : GGRealRootSL2On fun p lab => p = 3 ∧ ¬ GGNbrInner937U63Label p lab) :
    GGReflRealizedQFourInputThree := by
  intro G _ _ p B Bs x L D J hcfg _ hNT hp3 X hX hq
  rcases (GGInnerDiagOnLabel.mono_label
      (T := fun p lab => (GGLabQFour p lab ∧ GGNbrInner937U63Label p lab) ∨
        (GGLabQFour p lab ∧ ¬ GGNbrInner937U63Label p lab))
      (fun lab h => (em (GGNbrInner937U63Label p lab)).elim (fun h' => Or.inl ⟨h, h'⟩)
        (fun h' => Or.inr ⟨h, h'⟩)) hq).elim_or with h₁ | h₂
  · exact ggReflRealizedIn_three_U63 hLB hSP hcfg hNT hp3 hX h₁
  · exact ggReflRealizedIn_three_of_rootSL2On (S := fun p lab => ¬ GGNbrInner937U63Label p lab)
      hKG hcfg hNT hp3 hX h₂

theorem ggRealRootSL2On_three_offU63_of_rows
    (h : ∀ i, i ≠ .uNonsplitDvd → GGRealKGThreeRow i) :
    GGRealRootSL2On fun p lab => p = 3 ∧ ¬ GGNbrInner937U63Label p lab := by
  intro p lab hp hlab hl ⟨h3, hU⟩
  subst h3
  by_cases hs : GGTypeALabel 3 lab
  · exact ggRealRootSL2On_typeA 3 lab hp hlab hl hs
  obtain ⟨i, hi⟩ := ggKGRow_cover_three lab
  by_cases hiU : i = .uNonsplitDvd
  · subst hiU
    have h5 : lab.rank ≠ 5 := fun h5 => hU ⟨⟨hi.1, by omega, hi.2.1, hi.2.2⟩, h5, rfl⟩
    exact ggRealRootSL2On_three_uNonsplitDvd_ne_five 3 lab hp hlab hl ⟨rfl, hi, h5⟩
  · exact h i hiU 3 lab hp hlab hl ⟨rfl, hi, hs⟩

end CFSG.StandardType

end
