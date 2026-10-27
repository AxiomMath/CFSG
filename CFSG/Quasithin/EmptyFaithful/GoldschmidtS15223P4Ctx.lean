module

public import CFSG.Quasithin.EmptyFaithful.S152O4Facts
public import CFSG.Quasithin.EmptyFaithful.S152U19
public import CFSG.Quasithin.EmptyFaithful.T1515Der4
public import CFSG.Quasithin.EmptyFaithful.S146zVA
public import CFSG.Quasithin.EmptyFaithful.S153DC27
public import CFSG.Quasithin.EmptyFaithful.SBc17Cases
public import CFSG.Quasithin.EmptyFaithful.S152NWreath
public import CFSG.Quasithin.EmptyFaithful.S14113Case
public import CFSG.Quasithin.EmptyFaithful.T1515Der3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S15223P4

variable {G : Type} [Group G] [Finite G]

abbrev P4R (M I : Subgroup G) : Subgroup G := pCoreOf 2 (M ⊓ I)

abbrev P4V (M I X : Subgroup G) : Subgroup G := omegaOneCenterOf (pCoreOf 2 (X ⊔ P4R M I))

structure P4Ctx (T Mc M H : Subgroup G) (B₀ : Subgroup (MulAut (V154 T Mc M)))
    (I X : Subgroup G) : Prop where
  setting : Setting152 T Mc M
  hstar : IsHStar T M H
  b0 : IsB0 T Mc M B₀
  min : Hyp15215.Min T Mc M B₀ I
  charTwoI : CharTwo I
  inputs : Inputs152 T Mc M H B₀ I
  quotH : Nonempty (OTwoQuot H ≃* S152N.W3)
  noChi : ∀ Y : Subgroup G, ¬ IsChiBlock2 I Y
  concl : Concl15218ii T Mc M H B₀ I
  hyp : HypC23 I (P4R M I) (M ⊓ I)
  comp : X ∈ cComp I
  quasi : CFSG.IsQuasisimple (↥X ⧸ CFSG.pCore 2 ↥X)
  charTwoX : CharTwo X
  not_le : ¬ X ≤ M ⊓ I
  K_norm : oTwoUpper H ≤ Subgroup.normalizer (X : Set G)
  R_norm : P4R M I ≤ Subgroup.normalizer (X : Set G)
  sylow : IsSylowTwoOf (sOf152 T Mc M B₀) I
  c27 : C27Concl I (P4R M I) (M ⊓ I) X (P4V M I X)

section Ctx

variable {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

namespace P4Ctx

theorem K_le_I (c : P4Ctx T Mc M H B₀ I X) : oTwoUpper H ≤ I :=
  (K_le_inf152 c.inputs).trans inf_le_right

theorem K_not_le_M (c : P4Ctx T Mc M H B₀ I X) : ¬ oTwoUpper H ≤ M := fun h =>
  c.hstar.2.1 (by rw [H_eq152 c.setting c.hstar]; exact sup_le h (T_le_M152 c.setting))

theorem S_le_N (c : P4Ctx T Mc M H B₀ I X) : sOf152 T Mc M B₀ ≤ M ⊓ I :=
  le_inf (S_le_T152.trans (T_le_M152 c.setting)) (S_le_I152 c.inputs)

theorem R_le_S (c : P4Ctx T Mc M H B₀ I X) : P4R M I ≤ sOf152 T Mc M B₀ := by
  have hsylN : IsSylowTwoOf (sOf152 T Mc M B₀) (M ⊓ I) :=
    ⟨c.S_le_N, c.sylow.isPGroup, fun hdvd => c.sylow.2.2 (by
      have h1 := Subgroup.relIndex_mul_relIndex (sOf152 T Mc M B₀) (M ⊓ I) I c.S_le_N inf_le_right
      have h2 : 2 ∣ (sOf152 T Mc M B₀).relIndex I := by
        rw [← h1]; exact Dvd.dvd.mul_right hdvd _
      exact h2)⟩
  exact hsylN.pCoreOf_le

theorem K_le_centralizer (c : P4Ctx T Mc M H B₀ I X) :
    oTwoUpper H ≤ Subgroup.centralizer (zSOf T Mc M B₀ : Set G) := by
  obtain ⟨B, hB⟩ := c.inputs.hN.sigmaPrime_nonempty
  have hZ := commutator_eq_zSOf c.inputs.h13 c.b0 hB
  exact hZ ▸ (c.inputs.h11 B hB).centralizes

theorem S_le_centralizer (_c : P4Ctx T Mc M H B₀ I X) :
    sOf152 T Mc M B₀ ≤ Subgroup.centralizer (zSOf T Mc M B₀ : Set G) := inf_le_right

theorem X_le_I (c : P4Ctx T Mc M H B₀ I X) : X ≤ I := le_of_mem_cComp c.comp

theorem cases (c : P4Ctx T Mc M H B₀ I X) :
    SBc17.C27Cases I (P4R M I) (M ⊓ I) X (P4V M I X) := by
  have h3 := c.c27.2.2
  rcases h3 with ⟨hb, h1 | h2 | h3 | h4⟩ | hb | hc | hd | he | hf | hg | hh
  · exact Or.inl ⟨hb, h1⟩
  · exact Or.inr (Or.inl ⟨hb, h2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hb, h3⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hb, h4⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hd))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hf))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hg)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hh)))))))))

end P4Ctx

end Ctx

section Front

variable {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I : Subgroup G}

theorem p4Ctx_exists (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (h5 : StageLemma15205) (h159 : StageLemma1519)
    (h8 : StageLemma15208) (h11 : StageLemma15211) (h13 : StageLemma15213)
    (h14 : StageLemma15214)
    (hN : StageNotation15209) (h16 : StageLemma15216) (h17 : StageLemma15217)
    (h18 : StageLemma15218)
    (hs : Setting152 T Mc M) (hH : IsHStar T M H) (hB₀ : IsB0 T Mc M B₀)
    (hI : Hyp15215.Min T Mc M B₀ I) (hchar : CharTwo I)
    (hno : ∀ X : Subgroup G, ¬ IsChiBlock2 I X) (hii : Concl15218ii T Mc M H B₀ I) :
    ∃ X : Subgroup G, P4Ctx T Mc M H B₀ I X := by
  have hD : Inputs152 T Mc M H B₀ I :=
    ⟨h5 G T Mc M hs, h159 G T Mc M hs.qtfe hs.mf hs.ce, h13 G T Mc M hs H hH,
      h14 G T Mc M hs B₀ hB₀, h11 G T Mc M hs H hH, hN G T Mc M hs H hH,
      h16 G T Mc M hs H hH B₀ hB₀ I hI.1, h17 G T Mc M hs B₀ hB₀ I hI.1⟩
  have hOm : Om4FactsStatement := fun _ _ _ _ hX => S152O4.om4_facts hX
  have hyp : HypC23 I (P4R M I) (M ⊓ I) := lemma_15_2_19_two hs hB₀ hI.1 hD hOm hii
  set R := P4R M I with hRdef
  set N := M ⊓ I with hNdef
  have hsyl : IsSylowTwoOf (sOf152 T Mc M B₀) I := (h18 G T Mc M hs H hH B₀ hB₀ I hI.1).sylow
  have hTM : T ≤ M := T_le_M152 hs
  have hSN : sOf152 T Mc M B₀ ≤ N := le_inf (S_le_T152.trans hTM) (S_le_I152 hD)
  have hPN : pCoreOf 2 I ≤ N := hsyl.pCoreOf_le.trans hSN
  have hKI : oTwoUpper H ≤ I := (K_le_inf152 hD).trans inf_le_right
  have hKM : ¬ oTwoUpper H ≤ M := fun h => hH.2.1 (by
    rw [H_eq152 hs hH]; exact sup_le h hTM)
  have hKN : ¬ oTwoUpper H ≤ N := fun h => hKM (h.trans inf_le_left)
  have hFN : oTwoFIn I ≤ N := by
    by_contra hnot
    have hF : CharTwo (oTwoFIn I) :=
      CT.CharTwo.of_normal hchar C2Six.oTwoFIn_le C2Six.normal_oTwoFIn_subgroupOf
    obtain ⟨r, Lb, hLb, hprod⟩ := c2_6_two (hC129 G) hyp hF hnot
    have hr : 0 < r := by
      by_contra hr0
      have hr0' : r = 0 := Nat.eq_zero_of_not_pos hr0
      subst hr0'
      apply hnot
      intro x hx
      obtain ⟨m, hm, y, -, hxy⟩ := hprod x hx
      have hxm : x = m := by simpa using hxy
      rw [hxm]
      exact hm.1
    obtain ⟨hblock, hA3, -⟩ := hLb ⟨0, hr⟩
    exact hno (Lb ⟨0, hr⟩) ⟨isBlock2_of_oTwoFIn hblock, Or.inr ⟨3, by decide, hA3⟩⟩
  have hex : ∃ X : Subgroup G, X ∈ cComp I ∧ CFSG.IsQuasisimple (↥X ⧸ CFSG.pCore 2 ↥X) ∧
      ¬ X ≤ N := by
    by_contra hcon
    push Not at hcon
    have hFs : oTwoFstarIn I ≤ N := oTwoFstarIn_le_of_components1516 hPN hFN hcon
    have h441 := a4_4_1 (pCoreOf_le_oTwoFstarIn I)
      (le_inf (oTwoFstarIn_le I) hFs) (a44Hyp_oTwoFstarIn I)
    rw [inf_eq_right.mpr (inf_le_right : M ⊓ I ≤ I)] at h441
    have hRne : R ≠ ⊥ := hyp.radical.2.1
    have hIR : I ≤ Subgroup.normalizer (R : Set G) := by
      rw [hRdef]
      show I ≤ Subgroup.normalizer ((pCoreOf 2 (M ⊓ I) : Subgroup G) : Set G)
      rw [h441]
      exact le_normalizer_pCoreOf 2 I
    have hIN : I ≤ N :=
      (le_inf le_rfl hIR).trans ((inf_normalizer_le_cgsIn hRne).trans hyp.cgs)
    exact hKN (hKI.trans hIN)
  obtain ⟨X, hX, hXq, hXN⟩ := hex
  have hXI : X ≤ I := le_of_mem_cComp hX
  have hXchar : CharTwo X := charTwo_of_isSubnormal_of_charTwo hchar (subnormal_of_mem_cComp hX)
  have hKX : oTwoUpper H ≤ Subgroup.normalizer (X : Set G) := by
    have hc : (X.subgroupOf I).Normal ∨ (conjSubgroupsBy I X).ncard = 2 :=
      (lemma_1_2_1_three hs.qtfe.qtke hs.qtfe.simple hs.qtfe.nonabelian h37 h38 hI.1.inH.2
        hX).imp id And.left
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    exact odd_mem_normalizer_conjSubgroupsBy1516 hXI hc
      (hKI (mem_oTwoUpper_of_odd hx.1 hx.2)) hx.2 ⟨1, I.one_mem, (conjByElt_one1516 X).symm⟩
  have hRX : R ≤ Subgroup.normalizer (X : Set G) := by
    by_contra hRX
    have hSR : sOf152 T Mc M B₀ ≤ Subgroup.normalizer (R : Set G) :=
      hSN.trans (le_normalizer_pCoreOf 2 N)
    have hS : IsSylowTwoOf (R ⊓ X) X :=
      C2Push.isSylowTwoOf_inf_of_not_le_normalizer hyp.radical hsyl hSR hX hXq hRX
    obtain ⟨hshort, htype, -⟩ := S146zV.exists_block_data_of_asc129 (hC129 G) hchar hyp.sqtk
      hyp.radical hyp.cgs hX hXq hS hXN
    exact hno X ⟨⟨hshort, hXI, (isSubnormal_iff_subgroupOf hXI).mp (subnormal_of_mem_cComp hX)⟩,
      htype.imp id fun h5 => ⟨5, by decide, h5⟩⟩
  exact ⟨X, ⟨hs, hH, hB₀, hI, hchar, hD, h8 G T Mc M hs H hH, hno, hii, hyp, hX, hXq, hXchar, hXN,
    hKX, hRX, hsyl,
    hC27 G I R N X (omegaOneCenterOf (pCoreOf 2 (X ⊔ R))) hyp hX hXq hXchar hXN hRX rfl⟩⟩

end Front

end S15223P4

end CFSG.Quasithin
