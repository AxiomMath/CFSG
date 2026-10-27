module

public import CFSG.RankThree.PartTwo.Sec8.Hering418FD4
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofEvenDesc

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF418
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.TauCetiBridge.Twisted

section D4Main


theorem kF418OuterOn_trialityD4Six :
    KF418OuterOn (fun X _ => IsTrialityD4Six X) := by
  intro G _ _ L hL hl a b ha3 hb3 hab hb1 habz haN hbN hbC haC K hK n hn htype hKa hbk
  obtain ⟨f, hX⟩ := hl
  obtain ⟨⟨hp, hf, -⟩, htw⟩ := hX
  have c := Cfg.of_model hK ha3 hb3 hab haN hbN hbC haC hKa
  have hβ : Sec4.InducesOuterTheta b L := by
    rcases hbk with h | h
    · exact KFacts.InducesStdKind.inducesOuterTheta (k := .field) L h (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta (k := .graphField) L h (by decide)
  obtain ⟨Kf, _, _, σ, hKf, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card TwistTag.D4 hp hf htw
  have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
    KFacts.center_eq_bot_of_mulEquiv_fwd e.symm (center_graphFixedRootGroup_eq_bot σ.toRingHom)
  have hOTC : KFacts.OutThreeCyclic (L ⧸ aschbacherSolvableCore 3 L) :=
    (KFacts.outThreeCyclic_triality hf hKf hσ).of_mulEquiv e
  set α := KFacts.inducedAutHom L e ⟨b, c.hbL⟩ with hαdef
  have hα3 : α ^ 3 = 1 := KFacts.inducedAutHom_pow_eq_one L e c.hbL c.hb3
  have hαout : ¬ KFacts.IsInnerAut α := (KFacts.not_isInnerAut_inducedAutHom_iff L e c.hbL).mpr hβ
  have hfix := KFacts.map_barCentralizer_eq c.hbL e (Sec4.autFix α) (fun z => Iff.rfl)
  set C := Sec8.barCentralizer (Subgroup.zpowers b) L with hC
  set φ : C ≃* Sec4.autFix α := (e.subgroupMap C).trans (MulEquiv.subgroupCongr hfix) with hφ
  have hcomm : Commute c.beta c.alpha := c.alpha_mul_beta.symm
  have hinn : ∃ j : ℕ, c.alpha * c.beta ^ j ∈ innBar L := by
    obtain ⟨i, -, x, hx⟩ :=
      hOTC c.beta c.alpha hcomm c.beta_pow_three c.alpha_pow_three hβ.2
    refine ⟨i, ?_⟩
    rw [(hcomm.pow_left i).symm.eq]
    exact ⟨x, hx⟩
  rcases Item8KFacts2Proof.isStdGraphFieldConj_or_nonempty_autFix_equiv hf hKf hσ hα3 hαout with
    ⟨β, hβ'⟩ | he₂
  · exact c.false_of_isoGTwoEven hK hn htype hf
      (KFacts.isoGTwoEven_barCentralizer_of_conj_fieldActor hf hKf hσ e c.hbL β hβ') hZ hinn
  · obtain ⟨e₂⟩ := he₂
    rcases Nat.even_or_odd f with hfe | hfo
    · obtain ⟨F, _, _, hF, ⟨e₃⟩⟩ := kF82D4SecondCentY0Even_holds f hfe hf Kf σ hKf hσ
      have hPi : Sec4.PiField true 2 f F := ⟨hp, hf, hF⟩
      exact c.false_of_pgl_class hK hKa hβ hZ hOTC hf hPi hfe (φ.trans (e₂.trans e₃))
    · obtain ⟨F, _, _, hF, ⟨e₃⟩⟩ := kF82D4SecondCentY0_holds f hfo Kf σ hKf hσ
      have hPi : Sec4.PiField false 2 f F := ⟨hp, hf, hF⟩
      exact c.false_of_pgl_class hK hKa hβ hZ hOTC hf hPi hfo (φ.trans (e₂.trans e₃))


theorem kF418ModelOn_trialityD4Six_of_rank
    (hrank : Sec21.TrialityD4EvenThreeRankTwo) :
    KF418ModelOn (fun X _ => IsTrialityD4Six X) := by
  refine kF418ModelOn_of_outer ?_ ?_ kF418OuterOn_trialityD4Six
  · rintro X _ _ ⟨f, hX⟩
    exact bound_inner_of_pRank (MulEquiv.refl _) (hrank X f hX)
  · intro G _ _ L hL hl x hx3 hout
    obtain ⟨f, hX⟩ := hl
    obtain ⟨⟨hp, hf, -⟩, htw⟩ := hX
    obtain ⟨Kf, _, _, σ, hKf, hσ, ⟨e⟩⟩ :=
      exists_mulEquiv_graphFixedRootGroup_card TwistTag.D4 hp hf htw
    exact Or.inr (KFacts.InducesStdKind.triality f hf Kf hKf σ hσ
      (KFacts.inducesKindTriality_graphField hf hKf hσ L hx3 hout e))

theorem kF418ModelOn_trialityD4Six :
    KF418ModelOn (fun X _ => IsTrialityD4Six X) :=
  kF418ModelOn_trialityD4Six_of_rank Sec21.trialityD4EvenThreeRankTwo_holds

end D4Main

end CFSG.RankThree.PartTwo.Sec8.Hering418
