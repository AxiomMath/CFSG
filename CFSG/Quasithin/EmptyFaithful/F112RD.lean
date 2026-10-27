module

public import CFSG.Quasithin.EmptyFaithful.F112RA
public import CFSG.Quasithin.EmptyFaithful.F112RB
public import CFSG.Quasithin.EmptyFaithful.F112RC
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.EmptyFaithful.S151cStmt2
public import CFSG.Quasithin.EmptyFaithful.S152UF112
public import CFSG.Quasithin.EmptyFaithful.S152XC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S152X
open CFSG.Quasithin.He9 (isQuasithinSub_of)

namespace F112RR

variable {G : Type} [Group G] [Finite G]

structure Ctx (T Mc M H Y₁ : Subgroup G) : Prop where
  hs : Setting152 T Mc M
  hH : IsHStar T M H
  c1515 : Lemma1515Concl T Mc M
  c1519 : Lemma1519Concl T Mc M
  hY : IsY1 T Mc M Y₁
  c15207 : Lemma15207Concl T Mc M Y₁

namespace Ctx

variable {T Mc M H Y₁ : Subgroup G} (c : Ctx T Mc M H Y₁)

include c

theorem hT : IsSylowTwoOf T H := S152N.isSylowTwoOf_hStar c.hs c.hH

theorem inM : InM T M := c.hs.mf.1.1

theorem T_le_M : T ≤ M := c.inM.2

theorem T_pgroup : IsPGroup 2 T := (isSylowTwoOf_of_le151 c.hs.qtfe.sylow c.T_le_M).2.1

theorem T_le_H : T ≤ H := c.hH.1.1

theorem rc_le_T : rcOf Mc M ≤ T :=
  F7.isSylowTwoOf_pCoreOf_le
    (isSylowTwoOf_of_le151 c.hs.qtfe.sylow (le_inf c.hs.qtfe.t_le_mc c.T_le_M))

theorem T_le_normalizer_rc : T ≤ Subgroup.normalizer (rcOf Mc M : Set G) :=
  (le_inf c.hs.qtfe.t_le_mc c.T_le_M).trans (le_normalizer_pCoreOf 2 (Mc ⊓ M))

theorem Y₁_le_M : Y₁ ≤ M := le_sup_left.trans c.hY.unique.1.2

theorem L₁_le_M : Y₁ ⊔ rcOf Mc M ≤ M := sup_le c.Y₁_le_M S152X.rcOf_le_M

theorem T_le_normalizer_L₁ : T ≤ Subgroup.normalizer ((Y₁ ⊔ rcOf Mc M : Subgroup G) : Set G) :=
  fun _ hx => Subgroup.inf_normalizer_le_normalizer_sup _ _
    ⟨c.hY.normalized hx, c.T_le_normalizer_rc hx⟩

theorem sylow_L₁ : IsSylowTwoOf (T ⊓ (Y₁ ⊔ rcOf Mc M)) (Y₁ ⊔ rcOf Mc M) :=
  SzN22.isSylowTwoOf_inf_normalized (isSylowTwoOf_of_le151 c.hs.qtfe.sylow c.T_le_M) c.L₁_le_M
    c.T_le_normalizer_L₁

theorem charTwo_M : CharTwo M := by
  obtain ⟨P, hP⟩ := exists_sylow_of_quasithinIsSylowTwo c.hs.qtfe.sylow
  exact c.hs.qtfe.qtke.2.1 M c.inM.1.1 ⟨P, hP ▸ c.T_le_M⟩

theorem charTwo_H : CharTwo H := by
  obtain ⟨P, hP⟩ := exists_sylow_of_quasithinIsSylowTwo c.hs.qtfe.sylow
  subst hP
  exact CFSG.Quasithin.charTwo_of_inH c.hs.qtfe.qtke.2.1 P c.hH.1

theorem hO2 : pCoreOf 2 M ≤ Subgroup.centralizer (V154 T Mc M : Set G) := by
  refine c.c1515.reduced.2.2.2 (pCoreOf 2 M) (pCoreOf_le 2 M) (le_normalizer_pCoreOf 2 M)
    fun d hd => ?_
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 M) ⟨d, hd⟩
  refine ⟨k, ?_⟩
  have : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  rw [this]
  exact Subgroup.one_mem _

theorem O2M_le_rc : pCoreOf 2 M ≤ rcOf Mc M := by
  have hle : pCoreOf 2 M ≤ Mc ⊓ M := le_inf (c.hO2.trans c.c1515.centralizer_le) (pCoreOf_le 2 M)
  exact le_pCoreOf_of_le_normalizer 2 hle (inf_le_right.trans (le_normalizer_pCoreOf 2 M))
    (pCoreOf_isPGroup 2 M)

theorem X_le_M : Y₁ ⊔ T ≤ M := sup_le c.Y₁_le_M c.T_le_M

theorem L₁_sup_T : (Y₁ ⊔ rcOf Mc M) ⊔ T = Y₁ ⊔ T := by
  rw [sup_assoc, sup_eq_right.mpr c.rc_le_T]

theorem charTwo_X : CharTwo (Y₁ ⊔ T) :=
  charTwo_of_pCore_centralizer_le c.charTwo_M c.X_le_M
    (inf_le_left.trans (c.O2M_le_rc.trans (c.rc_le_T.trans le_sup_right)))

theorem o2_eq_bot_X : pCoreOf 2 (H ⊔ (Y₁ ⊔ T)) = ⊥ := by
  by_contra hne
  obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot hne
  have hMM' : M' = M :=
    c.hY.unique.2 M' ⟨hM'.1, (le_sup_right (a := H)).trans hM'.2⟩
  exact c.hH.2.1 ((le_sup_left (b := Y₁ ⊔ T)).trans (hMM' ▸ hM'.2))

section S3

variable (hqH : Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 3)))

include hqH

omit [Finite G] c in
theorem card_quot_H : Nat.card (OTwoQuot H) = 2 ^ 1 * 3 := by
  obtain ⟨e⟩ := hqH
  rw [Nat.card_congr e.toEquiv, card_perm_fin_three]

theorem inf_normalizer_H : H ⊓ Subgroup.normalizer (T : Set G) = T :=
  inf_normalizer_eq_of_card_quot c.hT le_rfl (by norm_num) (by decide) (card_quot_H hqH)

theorem H_inf_M : H ⊓ M = T := by
  have hidx := index_sylow_eq_of_card_quot c.hT (r := 3) (k := 1) (by decide)
    (card_quot_H hqH)
  rcases eq_or_eq_of_le_of_index_prime (le_inf c.T_le_H c.T_le_M) inf_le_left (by norm_num)
    hidx with h | h
  · exact h
  · exact absurd (h ▸ inf_le_right : H ≤ M) c.hH.2.1

theorem H_inf_X : H ⊓ (Y₁ ⊔ T) = T :=
  le_antisymm ((inf_le_inf_left H c.X_le_M).trans (c.H_inf_M hqH).le)
    (le_inf c.T_le_H le_sup_right)

theorem goldschmidtPair (hq₁ : Nonempty (OTwoQuot (Y₁ ⊔ rcOf Mc M) ≃* Equiv.Perm (Fin 3))) :
    F6.IsGoldschmidtVPair H (Y₁ ⊔ T) := by
  obtain ⟨hs, -, -, hq₂⟩ := oTwoQuot_sup_of_perm3 c.T_pgroup c.T_le_normalizer_L₁ c.sylow_L₁ hq₁
  rw [c.L₁_sup_T] at hs hq₂
  refine ⟨hqH, hq₂, ?_, ?_, c.o2_eq_bot_X⟩
  · rw [c.H_inf_X hqH]
    exact c.hT
  · rw [c.H_inf_X hqH]
    exact hs

end S3

end Ctx

end F112RR

theorem input15208F112At_S3_S3_of_gold (hGoldP : F6.GoldschmidtCharTwoLargePair.{0})
    (h1515 : StageLemma1515CE) (h1519 : StageLemma1519) (h15207 : StageLemma15207)
    (h15201 : StageLemma15201) (h15112 : StageLemma15112) :
    Input15208F112At (Equiv.Perm (Fin 3)) (Equiv.Perm (Fin 3)) := by
  intro G _ _ T Mc M hs H hH Y₁ hY₁ hqH hq₁
  have c : F112RR.Ctx T Mc M H Y₁ :=
    ⟨hs, hH, h1515 G T Mc M hs.qtfe hs.mf hs.ce, h1519 G T Mc M hs.qtfe hs.mf hs.ce, hY₁,
      h15207 G T Mc M hs Y₁ hY₁⟩
  obtain ⟨hUab, hUP, hPT, -, hU64⟩ := F112RR.exists_elemAbelian_card_ge hs hH c.c1519
    (h15201 G T Mc M hs) (h15112 G T Mc M hs.qtfe hs.mf hs.ce H hH).1
  have hpair := c.goldschmidtPair hqH hq₁
  have hUT : conjClosure (V154 T Mc M) H ≤ H ⊓ (Y₁ ⊔ T) := by
    rw [c.H_inf_X hqH]
    exact hUP.trans hPT
  have hcard : 32 ≤ Nat.card ↥(H ⊓ (Y₁ ⊔ T)) :=
    (by omega : 32 ≤ 64).trans (hU64.trans (Subgroup.card_le_of_le hUT))
  have hcase := hGoldP G H (Y₁ ⊔ T) hpair c.charTwo_H c.charTwo_X hcard
  rcases F6.isGoldCaseVICat_of_charTwo hcase c.charTwo_H c.charTwo_X with h | h
  · have := F112RR.card_elemAbelian_lt_sixtyFour hpair h hUT hUab
    omega
  · have hUT' : conjClosure (V154 T Mc M) H ≤ (Y₁ ⊔ T) ⊓ H := by rwa [inf_comm]
    have := F112RR.card_elemAbelian_lt_sixtyFour hpair.symm h hUT' hUab
    omega

end CFSG.Quasithin
