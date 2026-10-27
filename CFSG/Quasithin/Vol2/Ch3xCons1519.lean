module

public import CFSG.Quasithin.EmptyFaithful.S1519
public import CFSG.Quasithin.EmptyFaithful.S151cStmt2
public import CFSG.Quasithin.Vol2.Ch3xLem317FE

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem lemma_15_1_9_FE (h14 : StageLemma1414) (h17 : StageLemma1417)
    (h317 : Theorem317StatementFE) (h1413 : StageLemma1413) {T Mc M : Subgroup G}
    (h : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M) (hCE : IsCE1513 T M)
    (h15 : Lemma1515Concl T Mc M)
    (h16 : oTwoUpper (M ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ≤
      Subgroup.centralizer (V154 T Mc M : Set G)) :
    Lemma1519Concl T Mc M := by
  have hJW := thompsonJ_le_centralizer_VZ h17 h hM hCE
  obtain ⟨S, rfl⟩ := h.exists_sylow
  have hMT : InM (S : Subgroup G) M := hM.1.1
  have hTM : (S : Subgroup G) ≤ M := hMT.2
  have hEven := h.qtke.2.1
  have hJT : thompsonJ (S : Subgroup G) ≤ S := thompsonJ_le_self151 _
  have hJM : thompsonJ (S : Subgroup G) ≤
      M ⊓ Subgroup.centralizer (VZ (S : Subgroup G) M : Set G) :=
    le_inf (hJT.trans hTM) hJW
  have hVW := V154_le_VZ (S : Subgroup G) Mc M
  have hJV : thompsonJ (S : Subgroup G) ≤
      M ⊓ Subgroup.centralizer (V154 (S : Subgroup G) Mc M : Set G) :=
    le_inf (hJT.trans hTM) (hJW.trans (Subgroup.centralizer_le hVW))
  have htwo : IsGreatestOrd (S : Subgroup G) M :=
    h14 G S h.simple h.nonabelian h.qtke h.sylow h.faithful_empty M hM.1 hJM
  have hred : IsTwoReducedIn M (V154 (S : Subgroup G) Mc M) := h15.reduced
  have hVne : V154 (S : Subgroup G) Mc M ≠ ⊥ := V154_ne_bot h
  have hgenM : V154 (S : Subgroup G) Mc M =
      conjClosure (quasithinOmegaOneCenter (S : Subgroup G) ⊓ V154 (S : Subgroup G) Mc M) M :=
    V154_eq_conjClosure_M h15.gen
  have hunique : ∀ M' : Subgroup G,
      IsOrdMaximalIn (S : Subgroup G) (InM (S : Subgroup G)) M' → M' = M := fun M' hM' =>
    (hM'.2 M hMT (htwo.2 M' hM'.1)).symm
  have hcase : A57.CaseA (S : Subgroup G) M (V154 (S : Subgroup G) Mc M) ∨
      (V154 (S : Subgroup G) Mc M ≠ ⊥ ∧
        A57.CaseB (S : Subgroup G) M (V154 (S : Subgroup G) Mc M)) :=
    Or.inr ⟨hVne, hgenM, hunique⟩
  obtain ⟨⟨hpc, hchar⟩, hred', hauto, huniq⟩ := A57.main hEven S hM.1 hcase
  have hcomm : ∀ W : Subgroup G, thompsonJ (S : Subgroup G) ≤ Subgroup.centralizer (W : Set G) →
      ⁅W, thompsonJ (S : Subgroup G)⁆ = ⊥ := by
    intro W hW
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact ((Subgroup.mem_centralizer_iff.mp (hW hj)) w hw).symm
  have h14two := lemma_14_1_2_two hEven S hM.1 hred hJV hcase
  have hNS : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ M :=
    (normalizer_le_normalizer_baum (S : Subgroup G)).trans
      ((normalizer_le_cgs (baum_ne_bot h)).trans h14two.2)
  have h3 : ∀ H : Subgroup G, IsHStar (S : Subgroup G) M H →
      H ≤ Subgroup.centralizer (quasithinOmegaOneCenter (S : Subgroup G) : Set G) := by
    intro H hH
    obtain ⟨hbase1, hII1⟩ := lemma_15_1_1_one h hM hH
    obtain ⟨-, -, -, huniq1⟩ := A57.main hEven S hM.1 (Or.inl rfl)
    have hyp1 : Hyp315 (S : Subgroup G) M _ H (VZ (S : Subgroup G) M) :=
      { toHyp315Base := hbase1, «case» := Or.inr hII1 }
    have hJle : thompsonJ (S : Subgroup G) ≤ pCoreOf 2 (M ⊓ Subgroup.normalizer
        (((S : Subgroup G) ⊓ Subgroup.centralizer (VZ (S : Subgroup G) M : Set G) :
          Subgroup G) : Set G)) := by
      rw [hbase1.centralizer]
      exact le_inf hJT hJW
    rcases h317 G S h.simple h.nonabelian h.qtke h.sylow
        (h1413 G S h.simple h.qtke h.sylow h.faithful_empty) M _ H _ hMT hyp1 hJle with
      ⟨hZH, -⟩ | hR0
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact ((Subgroup.mem_centralizer_iff.mp (hZH hz).2) x hx).symm
    · exact absurd hR0 (not_exists_normal_of_isUniqueM huniq1 hH.2.1)
  refine
    { one_commute := hcomm _ (hJV.trans inf_le_right)
      one_commute_VZ := hcomm _ hJW
      one_baum := (lemma_14_1_2_one S hTM hred hJV).2
      one_cgs := h14two.2
      two := htwo
      three := fun H hH => ⟨h3 H hH, h.centralizer_le_mc⟩
      four := fun H hH => ?_
      five := huniq
      six_charTwo := hchar
      six_reduced := hred'
      six_pCore := hpc
      six_autOn := hauto.symm
      six_hyp := fun H hH => ⟨⟨?_, inf_le_left, hH, hred', hpc⟩, inf_le_right.trans hred.2.1⟩
      seven_normalizer := hNS
      seven_minParabolic := fun H hH =>
        IsHStar.mem_uFamHat S hH hTM (hH.not_le_normalizer hNS) }
  · exact (oTwoUpper_mono (le_inf inf_le_right (inf_le_left.trans (h3 H hH)))).trans h16
  · exact le_inf hTM (le_normalizer_inf_centralizer' Subgroup.le_normalizer
      (hTM.trans hred.2.1))

theorem stageLemma1519_of_ce_FE (h14 : StageLemma1414) (h17 : StageLemma1417)
    (h317 : Theorem317StatementFE) (h1413 : StageLemma1413) (h15 : StageLemma1515CE)
    (h16 : StageLemma1516CE) : StageLemma1519 := by
  intro G _ _ T Mc M h hM hCE
  exact lemma_15_1_9_FE h14 h17 h317 h1413 h hM hCE (h15 G T Mc M h hM hCE)
    (h16 G T Mc M h hM hCE)

end CFSG.Quasithin
