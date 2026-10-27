module

public import CFSG.Quasithin.EmptyFaithful.S152He4Main

public section

namespace CFSG.Quasithin.S146zX

open CFSG.Open hiding StatedClassicalModel StatedSL
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.He4

theorem insp_of_card'
    {G : Type} [Group G] [Finite G] {T Mc H L : Subgroup G}
    (hT : quasithinIsSylowTwo T) (hTMc : T ≤ Mc) (hTH : T ≤ H)
    (hMcL : Mc ≤ Subgroup.normalizer (L : Set G)) (hKL : oTwoUpper H ≤ L)
    (hHcard : Nat.card H = 72 * Nat.card (pCoreOf 2 H))
    (hlist : CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 3 1 ∨
      Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 3))) ∨
      Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11) ∨
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 4 2 1 ∨
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 5 2 1) :
    ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
      Nonempty (OTwoQuot (L ⊔ T) ≃*
        MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))) := by
  classical
  obtain ⟨P, hY, ⟨φL⟩⟩ := exists_yData hT hTMc hTH hMcL hKL hHcard
  set X : Subgroup G := L ⊔ T with hX
  have hLt : ↥(imageOTwoQuot X L) ≃* (↥L ⧸ CFSG.pCore 2 ↥L) :=
    φL.symm.trans (Der6D.oTwoQuotEquiv L)
  have hO2 := eq_bot_of_normal_isPGroup_two X
  rcases hlist with h | h | h | h | h
  · exfalso
    have hmod : StatedClassicalModel ↥(imageOTwoQuot X L) .PSL 3 3 1 :=
      CFSG.SectionRank.statedClassicalModel_of_mulEquiv hLt h
    exact coreA hY.normal hY.prod hY.sylow hY.le hY.nh hY.nn hY.n2 hY.card hY.ph hY.pl hY.p9
      (smallFacts_l33 (Or.inl hmod) (noInvCommNine_l33 hmod))
  · exfalso
    obtain ⟨e⟩ := h
    have h' : Nonempty (↥(imageOTwoQuot X L) ≃* ↥(StatedSL 3 (ZMod 3))) := ⟨hLt.trans e⟩
    have hmod := statedClassicalModel_of_statedSL_three_three h'
    exact coreA hY.normal hY.prod hY.sylow hY.le hY.nh hY.nn hY.n2 hY.card hY.ph hY.pl hY.p9
      (smallFacts_l33 (Or.inr h') (noInvCommNine_l33 hmod))
  · exfalso
    obtain ⟨e⟩ := h
    have h' : Nonempty (↥(imageOTwoQuot X L) ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11) :=
      ⟨hLt.trans e⟩
    exact coreA hY.normal hY.prod hY.sylow hY.le hY.nh hY.nn hY.n2 hY.card hY.ph hY.pl hY.p9
      (smallFacts_m11 h' (noInvCommNine_m11 h'))
  · have hmod : StatedClassicalModel ↥(imageOTwoQuot X L) .PSL 4 2 1 :=
      CFSG.SectionRank.statedClassicalModel_of_mulEquiv hLt h
    have hm : Nat.card ↥(imageOTwoQuot X L) = 2 ^ (2 * 3) * 315 := by
      rw [F420.card_of_l42 hmod]
      norm_num
    exact ⟨4, Or.inl rfl, nonempty_mulEquiv_mulAut_psl hY (by norm_num) (by norm_num) hm
      (by decide) hO2 hmod (noInvCommNine_l42 hmod)⟩
  · have hmod : StatedClassicalModel ↥(imageOTwoQuot X L) .PSL 5 2 1 :=
      CFSG.SectionRank.statedClassicalModel_of_mulEquiv hLt h
    have hm : Nat.card ↥(imageOTwoQuot X L) = 2 ^ (2 * 5) * 9765 := by
      rw [F420.card_of_l52 hmod]
      norm_num
    exact ⟨5, Or.inr rfl, nonempty_mulEquiv_mulAut_psl hY (by norm_num) (by norm_num) hm
      (by decide) hO2 hmod (noInvCommNine_l52 hmod)⟩

theorem center_specialLinearGroup_zmod_two (n : ℕ) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) = ⊥ := by
  rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center]
  exact CFSG.QuasithinUnique.Setup.Family.scalars_zmod_two n

@[expose] noncomputable def projSpecialLinearEquivSpecialLinearTwo (n : ℕ) :
    Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2) ≃*
      Matrix.SpecialLinearGroup (Fin n) (ZMod 2) :=
  (QuotientGroup.quotientMulEquivOfEq (center_specialLinearGroup_zmod_two n)).trans
    QuotientGroup.quotientBot

theorem insp_of_card
    {G : Type} [Group G] [Finite G] {T Mc H L : Subgroup G}
    (hT : quasithinIsSylowTwo T) (hTMc : T ≤ Mc) (hTH : T ≤ H)
    (hMcL : Mc ≤ Subgroup.normalizer (L : Set G)) (hKL : oTwoUpper H ≤ L)
    (hHcard : Nat.card H = 72 * Nat.card (pCoreOf 2 H))
    (hlist : CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 3 1 ∨
      Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 3))) ∨
      Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11) ∨
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 4 2 1 ∨
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 5 2 1) :
    ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
      Nonempty (OTwoQuot (L ⊔ T) ≃* MulAut (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) := by
  obtain ⟨n, hn, ⟨e⟩⟩ := insp_of_card' hT hTMc hTH hMcL hKL hHcard hlist
  exact ⟨n, hn, ⟨e.trans (MulAut.congr (projSpecialLinearEquivSpecialLinearTwo n))⟩⟩

end CFSG.Quasithin.S146zX
