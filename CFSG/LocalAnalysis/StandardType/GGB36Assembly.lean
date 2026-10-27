module

public import CFSG.LocalAnalysis.StandardType.GGB36Defs
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrowC6
public import CFSG.LocalAnalysis.StandardType.GGTPNI1

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ltqAsm_rankOne_of_labelIso {lab lab' : LargeEvenLabel}
    (h : GGLabelIso lab lab') (hr : GGTPNRankOne lab) : GGTPNRankOne lab' := by
  obtain ⟨t, r, m⟩ := lab
  obtain ⟨t', r', m'⟩ := lab'
  unfold GGLabelIso at h
  unfold GGTPNRankOne at hr ⊢
  rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    (rcases h with h | h | h | h | h | h | h | h <;> simp_all)

private theorem ltqAsm_not_rankOne_of_b36 {labL labJ' : LargeEvenLabel}
    (h : GGB36JLabel labL labJ') : ¬ GGTPNRankOne labJ' := by
  intro hr
  obtain ⟨t, r, m⟩ := labL
  obtain ⟨t', r', m'⟩ := labJ'
  unfold GGB36JLabel at h
  unfold GGTPNRankOne at hr
  rcases h with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩
  · rcases h with h | h | h | h | h <;> simp_all
  · rcases h with h | h | ⟨-, h⟩ <;> simp_all
  · rcases h with h | h <;> simp_all
  · rcases h with h | h | h | h | h | ⟨-, h⟩ <;> simp_all

private theorem ltqAsm_three_of_b36_not_pair {labL labJ' : LargeEvenLabel}
    (h : GGB36JLabel labL labJ') (hnot : ¬ GGPairE6Three 3 labL labJ') :
    labJ' = ⟨.A, 2, 2⟩ ∨ labJ' = ⟨.twA, 4, 1⟩ ∨ labJ' = ⟨.D, 4, labL.n⟩ := by
  obtain ⟨t, r, m⟩ := labL
  obtain ⟨t', r', m'⟩ := labJ'
  unfold GGB36JLabel at h
  unfold GGPairE6Three at hnot
  rcases h with ⟨ht, -, h⟩ | ⟨ht, -, h⟩ | ⟨ht, -, h⟩ | ⟨ht, -, h⟩
  · rcases h with h | h | h | h | h <;> simp_all
  · rcases h with h | h | ⟨-, h⟩ <;> simp_all
  · rcases h with h | h <;> simp_all
  · rcases h with h | h | h | h | h | ⟨-, h⟩ <;> simp_all

private theorem ltqAsm_one_le_n_of_hasLabel_exc {lab : LargeEvenLabel} {R : Type} [Group R]
    (h : GGHasLabel lab R) (ht : lab.tag = .E6 ∨ lab.tag = .twE6) : 1 ≤ lab.n := by
  obtain ⟨t, r, n⟩ := lab
  rcases ht with ht | ht <;> subst ht
  · unfold GGHasLabel LargeEvenRawDatum at h
    obtain ⟨K, hfield, hfin, hcard, -⟩ := h
    haveI := hfield
    haveI := hfin
    haveI : Fintype K := Fintype.ofFinite K
    have h1 : 1 < Fintype.card K := Fintype.one_lt_card
    rw [← Nat.card_eq_fintype_card, hcard] at h1
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp at h1
    · exact h0
  · unfold GGHasLabel LargeEvenRawDatum at h
    obtain ⟨K, hfield, hfin, hcard, -⟩ := h
    haveI := hfield
    haveI := hfin
    haveI : Fintype K := Fintype.ofFinite K
    have h1 : 1 < Fintype.card K := Fintype.one_lt_card
    rw [← Nat.card_eq_fintype_card, hcard] at h1
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp at h1
    · exact h0

theorem ggNbrTablePNbrInputOnL_b36_of_pieces
    (hT : GGTPNTransferBNoCorners) (h1 : GGB36StepOne) (h2 : GGE6ThreeI1Rank)
    (h3 : GGB36KernelFail) (hK : GGTablePKnownRK GGRegimeB36J)
    (hD4 : GGTablePKnownR GGRegimeB36D4E6) : GGNbrTablePNbrInputOnL GGRegimeB36L := by
  intro G _ _ p B Bs x L D J y K hc hL hKi hn labL labJ labK hΛL hΛJ hΛK hr hhL hhJ hhK
  obtain ⟨hp3, hcard, htagL⟩ := hr
  obtain ⟨labJ', hJLabel, hΛJ', hhJ'⟩ := h1 G p B Bs x L D J hc hL hp3 labL hΛL htagL hhL
  obtain ⟨hJK, hN, hx, hBasic⟩ := hT G p B Bs x L D J y K hc hL hKi hn
  have hβ := hc.1.2.2.2.2.2.1
  have hhJ'' : GGHasLabel labJ' ((J.subgroupOf K) ⧸ Subgroup.center (J.subgroupOf K)) :=
    ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK).symm hhJ'
  have hcorners : GGTPNCorners p (J.subgroupOf K) := by
    refine ⟨fun h7 _ => absurd h7 (by omega), fun _ n _ lab hΛlab hlab => ?_⟩
    have hlab' : GGHasLabel lab (J ⧸ Subgroup.center J) :=
      ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK) hlab
    have hiso : GGLabelIso lab labJ' :=
      ggLabelRigidInput_holds lab labJ' (J ⧸ Subgroup.center J) hΛlab hΛJ' hlab' hhJ'
    exact fun hrk => ltqAsm_not_rankOne_of_b36 hJLabel (ltqAsm_rankOne_of_labelIso hiso hrk)
  have hD : GGTPNDatumB p (Nat.card Bs) (fun _ _ => True) (ggAutsOf K Bs hN)
      (ggAutsOf K B (hc.2.1.1.trans hN)) (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K) :=
    ⟨hBasic, hcorners⟩
  have hfinish : GGTPNRow p (J.subgroupOf K) →
      ∃ labJ0 labK0 : LargeEvenLabel, LargeEvenInLambda2 labJ0 ∧ LargeEvenInLambda2 labK0 ∧
        GGTablePRow p labJ0 labK0 ∧ GGHasLabel labJ0 (J ⧸ Subgroup.center J) ∧
        GGHasLabel labK0 (K ⧸ Subgroup.center K) := by
    rintro ⟨labJ0, labK0, hΛJ0, hΛK0, hrow, hJ0, hK0⟩
    exact ⟨labJ0, labK0, hΛJ0, hΛK0, hrow,
      ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK) hJ0, hK0⟩
  by_cases hpair : GGPairE6Three 3 labL labJ'
  ·
    have hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D :=
      ggI1OfPairLOn_of_rank h2 G p B Bs x L D J hc hL labL labJ' hΛL hΛJ' (hp3.symm ▸ hpair) hhL hhJ'
    have hker : GGTPNKernel (ggAutsOf K Bs hN) (K.normalizerMonoidHom ⟨x, hx⟩)
        (J.subgroupOf K) :=
      ggTPNTrKernelI1_holds G p B Bs x L D J y K hc hL hKi hn hJK hN hx hI1
    exact hfinish (hK p hβ.1 hβ.2.1 ↥K (ggAutsOf K Bs hN)
      (ggAutsOf K B (hc.2.1.1.trans hN)) (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K)
      (Nat.card Bs) hD hker labJ' labK hΛJ' hΛK ⟨hp3, hcard, ⟨labL, htagL, hJLabel⟩⟩ hhJ'' hhK)
  ·
    have hthree := ltqAsm_three_of_b36_not_pair hJLabel hpair
    rcases h3 G p B Bs x L D J y K hc hL hKi hn hp3 hcard labL labJ' hΛL hΛJ' htagL hhL hhJ'
      hthree hJK hN hx with hker | hesc
    · exact hfinish (hK p hβ.1 hβ.2.1 ↥K (ggAutsOf K Bs hN)
        (ggAutsOf K B (hc.2.1.1.trans hN)) (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K)
        (Nat.card Bs) hD hker labJ' labK hΛJ' hΛK ⟨hp3, hcard, ⟨labL, htagL, hJLabel⟩⟩ hhJ'' hhK)
    ·
      obtain ⟨rfl, labK', htagK', hhK'⟩ := hesc
      obtain ⟨t, r, n⟩ := labK'
      have hn1 : 1 ≤ n := ltqAsm_one_le_n_of_hasLabel_exc hhK' htagK'
      let labX : LargeEvenLabel := ⟨t, 0, n⟩
      have hΛX : LargeEvenInLambda2 labX := by
        unfold LargeEvenInLambda2
        refine ⟨hn1, ?_⟩
        rcases htagK' with ht | ht
        · subst ht; rfl
        · subst ht; rfl
      have hhX : GGHasLabel labX (K ⧸ Subgroup.center K) := by
        unfold GGHasLabel at hhK' ⊢
        rcases htagK' with ht | ht
        · subst ht; exact hhK'
        · subst ht; exact hhK'
      have htagX : labX.tag = .E6 ∨ labX.tag = .twE6 := by
        rcases htagK' with ht | ht
        · subst ht; exact Or.inl rfl
        · subst ht; exact Or.inr rfl
      exact hfinish (hD4 p hβ.1 hβ.2.1 ↥K (ggAutsOf K Bs hN)
        (ggAutsOf K B (hc.2.1.1.trans hN)) (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K)
        (Nat.card Bs) hD ⟨.D, 4, labL.n⟩ labX hΛJ' hΛX ⟨hp3, rfl, rfl, htagX⟩ hhJ'' hhX)

end CFSG.StandardType

end
