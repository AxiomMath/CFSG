module

public import CFSG.Quasithin.H13.L32AC46b
public import CFSG.Quasithin.H13.L32ACSk11
public import CFSG.Quasithin.H13.L32AC46e
public import CFSG.Quasithin.Vol2.Ch11SecQ9aAmVSliceA5
public import CFSG.Quasithin.H13.L32AC46a
public import CFSG.Quasithin.H13.L32ACSk6

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

theorem lemma14_7_46_amalgam_of_A5 (hA5 : CFSG.Quasithin.F112R.F112SliceA5) (h4 : Lemma14_7_4_two_three)
    (hN1 : LieSylowOver3) (h29 : Thm14_7_29) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h30 : Lemma14_7_30)
    (h32 : Lemma14_7_32) (h45 : Lemma14_7_45_A5) : Lemma14_7_46_Amalgam := by
  have hSlice := hA5
  intro G _ _ T L V H S K hK hHeq n hn hLie hl1K V₂ hV2 ho2
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set I₂ := L32A.i2 T V V₂ with hI₂
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  have hTG : T ≤ A6.g1 T V := hTH.trans S.hz.2.1
  have hKH := le_of_mem_cComp hK
  obtain ⟨hq, -, -, hF918⟩ := h30 G T L V H S K hK
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := h32 G T L V H S K hK
  have hKn := le_normalizer_of_setting h37 h38 S hK hTK
  have hHeq' : conjClosure K T ⊔ (l1 T L V ⊔ T) = H := by
    rw [conjClosure_T_eq_self hTK]
    exact hHeq.symm
  rw [hHeq'] at hF918
  have hF := hF918.toHypF98
  have hA5 := h45 G T L V H S K hK hHeq n hn hLie
  have hT := S.hyp.fsu.sylow
  obtain ⟨⟨hI₂N, hNI₂⟩, -, ⟨e3⟩, -, -⟩ := h4 G T L V V₂ S.hyp hV2
  have hTN : T ≤ Subgroup.normalizer (V₂ : Set G) := hV2.2.2.1
  have hTI₂ : T ≤ Subgroup.normalizer (I₂ : Set G) := hTN.trans hNI₂
  have e3' : oTwoQuot ↥I₂ ≃* Equiv.Perm (Fin 3) :=
    (QuotientGroup.quotientMulEquivOfEq (A3.pCore_eq_openCore 2 ↥I₂)).symm.trans e3
  have hSI₂ : IsSylowTwoOf (T ⊓ I₂) I₂ :=
    A4.isSylowTwoOf_inf_normal (isSylowTwoOf_of_quasithinIsSylowTwo hT hTN) hI₂N hNI₂
  have hB₂ : borelOf I₂ T ≤ T := borelOf_le_of_perm3 hSI₂ ⟨e3'⟩
  have hB₁ : borelOf K T ≤ Subgroup.normalizer (V₂ : Set G) :=
    borelOf_le_normalizer_V2 hN1 h29 h1222 h1332 h1334 S hK hq hKn hn hLie hl1K hV2
  obtain ⟨e5⟩ := hA5
  have eK : oTwoQuot ↥K ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.quotientMulEquivOfEq (A3.pCore_eq_openCore 2 ↥K)).symm.trans
      ((cStarEquiv K).symm.trans e5)
  obtain ⟨f5⟩ := He9.nonempty_psl2_gf4_mulEquiv_alternating
  have hUO := fsuU_le_pCoreOf_g1 h1332 h1334 S.hyp
  have hVU : V ≤ fsuU T V := le_conjClosure V _
  have hV₂T : V₂ ≤ T := hV2.2.1.trans (hVU.trans (hUO.trans (L32A.pCoreOf_le_of_le S.hyp hTG)))
  have hV₂I₂ : V₂ ≤ I₂ := hV2.2.1.trans (hVU.trans (hUO.trans (le_conjClosure _ _)))
  have hV₂2 : IsPGroup 2 V₂ := hT.1.to_le hV₂T
  have hO2H : pCoreOf 2 H ≠ ⊥ := S.hz.1.2
  have hch1 : CharTwo (K ⊔ T ⊔ borelOf I₂ T) := by
    rw [sup_eq_left.mpr (hB₂.trans le_sup_right)]
    refine charTwo_of_inH S.hyp.fsu.qtke.2.1 (hT.1.toSylow hT.2)
      ⟨le_sup_right, fun h => hO2H ?_⟩
    have hle : pCoreOf 2 H ≤ pCoreOf 2 (K ⊔ T) :=
      le_pCoreOf_of_le_normalizer 2 ((L32A.pCoreOf_le_of_le S.hyp hTH).trans le_sup_right)
        ((sup_le hKH hTH).trans (le_normalizer_pCoreOf 2 H)) (pCoreOf_isPGroup 2 H)
    rw [h] at hle
    exact le_bot_iff.mp hle
  have hch2 : CharTwo (I₂ ⊔ T ⊔ borelOf K T) := by
    have hX : I₂ ⊔ T ⊔ borelOf K T ≤ Subgroup.normalizer (V₂ : Set G) :=
      sup_le (sup_le hI₂N hTN) hB₁
    have hVO := le_pCoreOf_of_le_normalizer 2 (hV₂T.trans (le_sup_right.trans le_sup_left)) hX hV₂2
    have hV₂1 : V₂ ≠ ⊥ := fun h => by
      have h4 := hV2.2.2.2
      rw [h, Subgroup.card_bot] at h4
      omega
    exact charTwo_of_inH S.hyp.fsu.qtke.2.1 (hT.1.toSylow hT.2)
      ⟨le_sup_right.trans le_sup_left, fun h => hV₂1 (le_bot_iff.mp (h ▸ hVO))⟩
  have hyp : Hyp111 K I₂ T :=
    ⟨⟨inferInstance, hT.1, hTK,
        A4.isSylowTwoOf_inf_normal (isSylowTwoOf_of_quasithinIsSylowTwo hT hTH) hKH hKn,
        Or.inl ⟨2, by norm_num, ⟨eK.trans f5.symm⟩⟩, hB₂.trans hTK, hch1⟩,
      ⟨inferInstance, hT.1, hTI₂, hSI₂, isRankOneListed_perm_three e3', hB₁.trans hNI₂, hch2⟩,
      by rw [sup_comm K I₂]; exact ho2⟩
  have hnorm : (T.subgroupOf (T ⊔ borelOf I₂ T)).Normal := by
    rw [sup_eq_left.mpr hB₂, Subgroup.subgroupOf_self]
    infer_instance
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have hV1c : Nat.card (fsuV1 T V) = 2 := (hMod G T L V S.hyp.hyp S.hyp.fsu).2.2.2.1
  have hV1N : ¬ I₂ ≤ Subgroup.normalizer (fsuV1 T V : Set G) := by
    intro hle
    have hsub : pCoreOf 2 (A6.g1 T V) ≤ pCoreOf 2 I₂ :=
      le_pCoreOf_of_le_normalizer 2 (le_conjClosure _ _)
        (hle.trans (le_normalizer_pCoreOf 2 (A6.g1 T V))) (pCoreOf_isPGroup 2 _)
    have hII : I₂ ≤ pCoreOf 2 I₂ := conjClosure_le fun g hg x hx =>
      (Subgroup.mem_normalizer_iff.mp ((hNI₂.trans (normalizer_le_normalizer_pCoreOf 2 I₂)) hg)
        x).mp (hsub hx)
    have h6 := F112W.relIndex_pCoreOf_eq_six ⟨e3'⟩
    rw [Subgroup.relIndex_eq_one.mpr hII] at h6
    omega
  have hKc : Nat.card (OTwoQuot K) = 60 := card_of_isAlt_five ⟨eK⟩
  have hKns : ¬ Group.IsSolvable ↥K := not_isSolvable_of_mem_cComp hK
  have hS3 : Nonempty (oTwoQuot ↥I₂ ≃* Equiv.Perm (Fin 3)) := ⟨e3'⟩
  have hE16 := sixteen_le_card_commutator hK hF ⟨e5⟩
  have hEP := commutator_le_pCoreOf hKH hKn hF
  have hEU := commutator_le_left_of_le_normalizer (hKH.trans (le_normalizer_conjClosure V H))
  have hBKN : bigB K I₂ T ≤ Subgroup.normalizer (K : Set G) := by
    unfold bigB
    exact sup_le (sup_le ((inf_le_left : borelOf K T ≤ K).trans Subgroup.le_normalizer)
      (hB₂.trans hTK)) hTK
  have hKP : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ bigB K I₂ T) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans le_sup_left)
      ((sup_le Subgroup.le_normalizer hBKN).trans (normalizer_le_normalizer_pCoreOf 2 K))
      (pCoreOf_isPGroup 2 K)
  have hQ8 : ¬ IsQ8D8 ↥(pCoreOf 2 (K ⊔ bigB K I₂ T)) := fun hQ => by
    refine false_of_isQ8D8 hQ
      (E := (⁅conjClosure V H, K⁆ : Subgroup G).subgroupOf (pCoreOf 2 (K ⊔ bigB K I₂ T)))
      (fun x hx => Subtype.ext ?_) ?_
    · have h1 := hF.F911_3.2 x (hEU hx)
      simpa [pow_two] using h1
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hEP.trans hKP)).toEquiv]
      exact hE16
  have hZ : ¬ IsSpecialPow 2 (2 ^ 1) 2 ↥(pCoreOf 2 (I₂ ⊔ bigB I₂ K T)) := by
    intro hsp
    rw [bigB_comm K I₂ T] at hsp
    have hTB : T ≤ bigB K I₂ T := by
      unfold bigB
      exact le_sup_right
    have hBN2 : bigB K I₂ T ≤ Subgroup.normalizer (V₂ : Set G) := by
      unfold bigB
      exact sup_le (sup_le hB₁ (hB₂.trans hTN)) hTN
    have hPN : I₂ ⊔ bigB K I₂ T ≤ Subgroup.normalizer (V₂ : Set G) := sup_le hI₂N hBN2
    have hV2O : V₂ ≤ pCoreOf 2 (I₂ ⊔ bigB K I₂ T) :=
      le_pCoreOf_of_le_normalizer 2 (hV₂I₂.trans le_sup_left) hPN hV₂2
    have hQT : pCoreOf 2 (I₂ ⊔ bigB K I₂ T) ≤ T :=
      pCoreOf_two_le_of_isSylowTwoOf
        (isSylowTwoOf_of_quasithinIsSylowTwo hT (hTB.trans le_sup_right))
    have hZT : fsuV1 T V ≤ Subgroup.centralizer (T : Set G) := fun z hz =>
      (Subgroup.closure_le _).mpr (fun _ hy => (Subgroup.mem_inf.mp hy.1).2) hz.2
    have hZc : fsuV1 T V ≤ Subgroup.centralizer (pCoreOf 2 (I₂ ⊔ bigB K I₂ T) : Set G) :=
      fun z hz => Subgroup.centralizer_le hQT (hZT hz)
    have hZP : fsuV1 T V ≤ pCoreOf 2 (I₂ ⊔ bigB K I₂ T) := hV2.1.trans hV2O
    have hcard : Nat.card (Subgroup.center ↥(pCoreOf 2 (I₂ ⊔ bigB K I₂ T))) = 2 := by
      have h2 := hsp.2.2
      rwa [pow_one] at h2
    exact hV1N (le_sup_left.trans
      (S1421Elim.le_normalizer_of_card_center_eq_two hcard hV1c hZP hZc))
  obtain ⟨L1', L2', hor, -, hlist, -⟩ :=
    hSlice G K I₂ T ⟨hyp, isQuasithinSub_of_qtke S.hyp.fsu.qtke _, Or.inr hnorm⟩
      (Or.inr (Or.inr ⟨CFSG.Quasithin.vA5_of_listed_card_sixty hyp.h1.listed hKc, hS3⟩))
  rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2] at hlist
    exact false_of_F112List_unswapped hKns hKc hS3 hQ8 hlist
  · rw [h1, h2] at hlist
    exact false_of_F112List_swapped hKns hKc hS3 hZ hlist

end CFSG.Quasithin.H13.L32A.C

end
