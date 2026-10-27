module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3C6Prod
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3A5Local
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V0Main

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s1611e3_case6_a5_core {D : Data G} (h : S1611e3Std D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (h6 : Case168_6 D V₀ V hV L)
    (hA5 : UC22.IsAlt ↥(lBar V₀ V hV L) 5) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  have hp3 : 3 ∈ D.sig := by
    rw [h6.2.2.2]
    exact Set.mem_singleton 3
  obtain ⟨x, Z, hxT, hcomm, hinf, hE, hfixL', hfixL, hWinf, hWsup, hSylow, hZc, hZM, hZnorm,
    hZL, hZW, hZf, hZE, hZinfE, hZL'c, hZW'c, hZf', hfix, hA5impl⟩ :=
    s1611e3_case6_prod h hc h6
  have hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z 5) (lBar V₀ V hV L)
      (wTil V₀ V hV L) ⊥ 2 := by
    rcases h6.2.1 with ⟨-, hsum⟩ | ⟨hL3, -⟩
    · exact hsum
    · exfalso
      have h60 : Nat.card ↥(lBar V₀ V hV L) = 60 := by
        obtain ⟨eA⟩ := hA5
        rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
        norm_num [Nat.factorial]
      have h168 : Nat.card ↥(lBar V₀ V hV L) = 168 := card_eq_of_isL3 hL3
      omega
  obtain ⟨hL', hsum'⟩ := hA5impl hA5
  have hFX : Fstar (Mbar D.M V₀ V hV) ≤ Mbar D.M V₀ V hV :=
    (s16c167_cfg10_fstar_facts (Mbar D.M V₀ V hV)).1
  have hLsupM : lBar V₀ V hV L ⊔ (lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom ≤
      Mbar D.M V₀ V hV := by
    rw [← hE]
    exact (Subgroup.map_subtype_le (commutator ↥(Fstar (Mbar D.M V₀ V hV)))).trans hFX
  have hLm : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV := le_sup_left.trans hLsupM
  have hL'm : (lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom ≤ Mbar D.M V₀ V hV :=
    le_sup_right.trans hLsupM
  have hTm : barSub V₀ V hV D.T ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV D.sylowM.le
  have hT2 : IsPGroup 2 ↥(barSub V₀ V hV D.T) := by
    have hMstab : D.M ≤ stabTil V₀ V :=
      le_stabTil hc.setting.hyp151.hyp125.pairFacts.le_normalizer
        hc.setting.hyp151.hyp125.pairFacts.le_normalizer₀
    exact (s1611e3_barSub_sylow hMstab
      (CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM)).isPGroup
  obtain ⟨Itil, hIT, hI3', hMod⟩ := s1611e3_a5_local (W := Vtil V₀ V hV)
    (s15_Infra_vtil_sq_eq_one V₀ V hV) hA5 hL' hWinf hWsup hsum hsum' hcomm hfixL' hfixL
    hZc hZL hZL'c hZW hZW'c hZf hZf' hT2 (fun y hy => hfix y (hTm hy))
    (fun y hy => hZnorm y (hTm hy))
  exact s1611e3_normalizer_le_of_local h hc (p := 3) hp3 Itil hIT
    (fun w hw hwne => by
      obtain ⟨y, hy, hyo, hyw⟩ := hI3' w hw hwne
      exact ⟨y, (sup_le hLm hL'm) hy, hyo, hyw⟩) hMod

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
