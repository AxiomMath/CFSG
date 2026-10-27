module

public import CFSG.Quasithin.Background.SmithC27RCaseIITrans
public import CFSG.Quasithin.Background.SmithC27RCaseIOrd
public import CFSG.Quasithin.Background.SmithC27RTypeRank2
public import CFSG.Quasithin.Background.SmithC27RLieA6
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS
public import CFSG.Quasithin.Background.SmithC27RMS

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {H R M K : Subgroup G}

theorem three_of_caseII_six (hC132 : ASInputs.AS_C_1_32) (h : Hyp27 H R M K)
    (hnS : ¬ IsSylowTwoOf R (K ⊔ R))
    (C : CaseIICtx R K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) 6) :
    C27Three H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) := by
  have hs := h.starHyp
  obtain ⟨T, hT, hTN⟩ := exists_sylow_le_normalizer_six (C.isPGroup_bar_R hs)
    (C.isRadSig_bar_R h.isTwoRadicalIn_sup hs)
  obtain ⟨T', hT', hT'R⟩ := C.exists_sylow_star_of_bar hT hTN
  obtain ⟨e⟩ := C.nonempty_equivK
  obtain ⟨e₀⟩ := hs.nonempty_quotCenterEquiv
  have hr : IsRankTwoLie2Derived
      ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (IsAlt.of_mulEquiv (e₀.trans (quotCenterCongr e)).symm isAlt_alternatingGroup_six)))))
  have hMS := isMSPair_of h hr (exists_sylow_le_normalizer_of_star hs hT' hT'R)
  have hb := blocks_of_alt6 h hs e (hC132 G (K ⊔ R) R K hMS h.mem_cComp_sup h.coe_sup)
  have hP := isParabolic2_MK_of_sylow h hs hT' hT'R (C.self_normalizing_K (Or.inl rfl))
  have hmax : MaxParabolicMaximal (autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) :=
    (maxParabolicMaximal_congr (e.trans Subgroup.topEquiv.symm)).mpr maxParabolicMaximal_alt6
  have hMP := (hmax _ hP (not_isBorelIn_MK h hs hnS) (autOn_MK_ne h hs)).1
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hb, hMP⟩))))

end CFSG.Quasithin.SmithC27
