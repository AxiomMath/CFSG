module

public import CFSG.Quasithin.Vol2.Ch10SecD31B
public import CFSG.Quasithin.Vol2.Ch10SecD31G
public import CFSG.Quasithin.Background.E3Lower
public import CFSG.Quasithin.Vol2.Ch10SecD31A
public import CFSG.Quasithin.Vol2.Ch10SecD31F

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem fsuCVM_eq_bot (hA : FactAParamWreath) (hW : FactSymFiveWrTwo) (h331 : Stmt3_3_1)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hI16 : ASInputs.AS_I_1_6)
    (h1012 : Stmt10_1_2) (h1023 : Stmt10_2_3) (h1028 : Stmt10_2_8) (h1029 : Stmt10_2_9)
    (h10213 : Stmt10_2_13) (h : Hyp10 G T L I) : fsuCVM T L I = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have h3 := (h10213 G T L I h).1
  have hV1 := cV1_ne_bot h37 h38 h hne
  have hCZ := centralizer_Z_le_fsuM h331 h1028 h h3.1 hV1
  have hZL := (h1028 G T L I h h3.1 hV1).1
  obtain ⟨H, hH⟩ := SecB.exists_isHStar h331 h
  have hn := (h10213 G T L I h).2.2 H hH
  obtain ⟨-, -, h3', -⟩ := h1023 G T L I h H hH (by rw [hn]; norm_num)
  obtain ⟨hO2L0, hmaxpar, ⟨e⟩⟩ := h3' h3.1
  have hTH : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hH.1.1
  have hchar : CharTwo H := charTwo_of_le h.fsu.qtke h.fsu.sylow hH.1.1 hH.1.2
  set Z := quasithinOmegaOneCenter T with hZ
  have hred : IsTwoReducedIn H (conjClosure Z H) :=
    isTwoReducedIn_conjClosure_of_sylowIn hTH.1 hTH.2.1 hTH.2.2 hchar le_rfl
  have hU : IsElemAbelian 2 (conjClosure Z H) := hred.2.2.1
  have hZU : Z ≤ conjClosure Z H := le_conjClosure Z H
  have hCM : H ⊓ Subgroup.centralizer (conjClosure Z H : Set G) ≤ fsuM T L :=
    fun x hx => hCZ (Subgroup.centralizer_le hZU hx.2)
  have hC := inf_centralizer_eq_pCoreOf hW e hTH (SecA.le_fsuM T L) hH.2.1 hred hCM
  have hTC : T ≤ Subgroup.centralizer (Z : Set G) := fun s hs =>
    Subgroup.mem_centralizer_iff.mpr fun z hz =>
      (Subgroup.mem_centralizer_singleton_iff.mp (le_centralizer_of_mem_omegaOneCenter hz hs)).symm
  have hLC : L ≤ Subgroup.centralizer (Z : Set G) := by
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at hZL
    exact hZL
  have hL0C : fsuL0 T L ≤ Subgroup.centralizer (Z : Set G) := conjClosure_le fun s hs l hl =>
    (Subgroup.centralizer _).mul_mem ((Subgroup.centralizer _).mul_mem (hTC hs) (hLC hl))
      ((Subgroup.centralizer _).inv_mem (hTC hs))
  have hZY : oTwoUpper (H ⊓ fsuM T L) ⊔ T ≤ Subgroup.centralizer (Z : Set G) :=
    sup_le (hO2L0.trans hL0C) hTC
  have hYH : oTwoUpper (H ⊓ fsuM T L) ⊔ T ≤ H := sup_le ((oTwoUpper_le _).trans inf_le_left) hH.1.1
  have hO2T : pCoreOf 2 H ≤ T := IsSylowTwoOf.pCoreOf_le hTH
  have hHY : ¬ H ≤ (oTwoUpper (H ⊓ fsuM T L) ⊔ T) ⊔ pCoreOf 2 H := fun hle =>
    hH.2.1 (hle.trans (sup_le (sup_le ((oTwoUpper_le _).trans inf_le_right) (SecA.le_fsuM T L))
      (hO2T.trans (SecA.le_fsuM T L))))
  have hYT : ¬ oTwoUpper (H ⊓ fsuM T L) ⊔ T ≤ T ⊔ pCoreOf 2 H := by
    intro hle
    rw [sup_eq_left.mpr hO2T] at hle
    have hO : oTwoUpper (H ⊓ fsuM T L) ≤ T := le_sup_left.trans hle
    exact not_isMaxSubgroupIn_of_le_T h h3 (inf_le_left.trans (sup_le inf_le_left hO))
      inf_le_right (hmaxpar L (Or.inl rfl))
  have ha := aParam_autI_le_one hA hU hred.2.1 hC e hTH le_sup_right hYH hHY hYT hZY rfl
  have hV := SecA.isElemAbelian_fsuVM h
  have hw := (h10213 G T L I h).2.1
  have hW0Q : E3.wClos (fsuVM T L I) 0 T ≤ T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) :=
    E3.wClos_le_of_lt_wParam (by rw [hw]; norm_num)
  have hrkV : 0 < rk ↥(fsuVM T L I) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (SecA.isPGroup_fsuVM h)
    have h16 : 16 ≤ Nat.card ↥(fsuVM T L I) :=
      (card_V1_eq h37 h38 hI16 h h3 hV1).1 ▸ Subgroup.card_le_of_le V1_le_V
    unfold rk
    rw [hk, padicValNat.prime_pow]
    by_contra hk0
    push Not at hk0
    interval_cases k
    rw [pow_zero] at hk
    omega
  have hW01 : E3.wClos (fsuVM T L I) 0 T ≠ ⊥ := E3.wClos_ne_bot hV (SecA.fsuVM_le_T h) hrkV
  have hUniq := (h1012 G T L I h).2.2.2.2.1
  have hST : IsSylowIn 2 T T := ⟨le_rfl, h.fsu.sylow.1, by rw [Subgroup.relIndex_self]; norm_num⟩
  have hNW := (E3.e3_16_one hST inf_le_left (h.fsu.sylow.1.to_le inf_le_left) hW0Q hW01 hUniq).2
  have hne' := commutator_wClos_ne_bot hTH hH.2.1 hC hNW
  have hs : 2 ≤ E3.sParam hV := two_le_sParam h37 h38 hI16 h1029 h h3 hV1
  exact hne' (E3.e3_18_comm hV hTH.1 hred.2.1 hU (i := 0) (by omega))

theorem stmt10_3_1_of (hA : FactAParamWreath) (hW : FactSymFiveWrTwo) (h331 : Stmt3_3_1)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hI16 : ASInputs.AS_I_1_6)
    (h1012 : Stmt10_1_2) (h1023 : Stmt10_2_3) (h1028 : Stmt10_2_8) (h1029 : Stmt10_2_9)
    (h10210 : Stmt10_2_10) (h10213 : Stmt10_2_13) : Stmt10_3_1 := by
  intro G _ _ T L I h
  have hc := fsuCVM_eq_bot hA hW h331 h37 h38 hI16 h1012 h1023 h1028 h1029 h10213 h
  exact ⟨hc, (h10210 G T L I h).2 hc⟩

end CFSG.Quasithin.Vol2.Ch10.SecD
