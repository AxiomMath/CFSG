module

public import CFSG.Quasithin.EmptyFaithful.Der6DMain
public import CFSG.Quasithin.EmptyFaithful.S152He4Groups
public import CFSG.Quasithin.EmptyFaithful.S152He4Inv
public import CFSG.Quasithin.EmptyFaithful.S152He4Quot

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedClassicalModel StatedSL
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.He4

theorem nonempty_mulEquiv_mulAut_psl {Y : Type} [Group Y] [Finite Y] {Lt T H N P : Subgroup Y}
    (hY : YData Lt T H N P) {n j m : ℕ} (hn : 3 ≤ n) (hj : 2 ≤ j)
    (hm : Nat.card ↥Lt = 2 ^ (2 * j) * m) (hodd : Odd m)
    (hO2 : ∀ Q : Subgroup Y, Q.Normal → IsPGroup 2 Q → Q = ⊥)
    (hmod : StatedClassicalModel ↥Lt .PSL n 2 1) (hinv : NoInvCommNine ↥Lt) :
    Nonempty (Y ≃* MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))) := by
  obtain ⟨hZ, hAut⟩ := lnTwo_facts hn hmod
  have hZ' : ∀ z ∈ Lt, (∀ l ∈ Lt, z * l = l * z) → z = 1 := by
    intro z hz hc
    have : (⟨z, hz⟩ : ↥Lt) ∈ Subgroup.center ↥Lt := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hc g g.2).symm
    rw [hZ] at this
    exact congrArg Subtype.val (Subgroup.mem_bot.1 this)
  have hnot := coreB hY.normal hY.prod hY.sylow hY.le hY.nh hY.nn hY.n2 hY.card hY.ph hY.pl hY.p9
    hj hm hodd hinv
  obtain ⟨e⟩ := nonempty_mulEquiv_mulAut hY.normal hY.prod hY.sylow.2.1 hO2 hZ' hAut hnot
  obtain ⟨eP⟩ := nonempty_mulEquiv_psl_zmod_two hmod
  exact ⟨e.trans (MulAut.congr eP)⟩

theorem insp15212_holds :
    Insp15212 := by
  intro G _ _ T Mc M H L hs hH φ hL hMcL hKc hlist
  classical
  have hTsyl : quasithinIsSylowTwo T := hs.qtfe.sylow
  have hTMc : T ≤ Mc := hs.qtfe.t_le_mc
  have hTH : T ≤ H := hH.1.1
  have hKL : oTwoUpper H ≤ L := hKc ▸ le_conjClosure (oTwoUpper H) Mc
  have hHcard : Nat.card H = 72 * Nat.card (pCoreOf 2 H) := by
    obtain ⟨e⟩ := φ
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥H)
    have h2 : Nat.card (OTwoQuot H) = 72 := by
      rw [Nat.card_congr e.toEquiv]
      exact S152N.W3.card_eq
    have h3 : Nat.card (pCoreOf 2 H) = Nat.card (CFSG.Open.pCore 2 ↥H) :=
      Subgroup.card_map_of_injective H.subtype_injective
    rw [h3, h1]
    change Nat.card (OTwoQuot H) * _ = _
    rw [h2]
  obtain ⟨P, hY, ⟨φL⟩⟩ := exists_yData hTsyl hTMc hTH hMcL hKL hHcard
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

end CFSG.Quasithin
