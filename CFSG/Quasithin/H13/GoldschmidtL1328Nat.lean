module

public import CFSG.Quasithin.H13.GoldschmidtL1328NatK4
public import CFSG.Quasithin.H13.GoldschmidtL1329Five

public section

namespace CFSG.Quasithin.H13.A6

namespace L1328

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem stmt13_2_2_8Nat_holds :
    ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Setting4 G T L V → IsHatA6 L →
      thompsonJ (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) = thompsonJ (pCoreOf 2 (L ⊔ T)) ∧
        baum (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) = baum (pCoreOf 2 (L ⊔ T)) := by
  intro G _ _ T L V S hhat
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) with hRdef
  set Q := pCoreOf 2 (L ⊔ T) with hQdef
  have hRT : R ≤ T := R_le_T S
  have hQ : T ⊓ centralizer (V : Set G) = Q := S.cT
  have hL1L : L₁Of L (fsuV1 T V) ≤ L := S.L1_le_L
  have hQR : Q ≤ R := by
    have hQT : Q ≤ T := hQ ▸ inf_le_left
    exact LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hQT.trans le_sup_right)
      ((sup_le_sup_right hL1L T).trans (LieType.BorelTits.le_normalizer_pCoreOf 2 _))
      (LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hVab := S.elemAbelian_V
  have hVQ : V ≤ Q := by
    rw [← hQ]
    exact le_inf S.V_le_T fun v hv => mem_centralizer_iff.2 fun w hw =>
      congrArg Subtype.val (hVab.1.is_comm.comm ⟨w, hw⟩ ⟨v, hv⟩)
  have hVR : V ≤ R := hVQ.trans hQR
  have hJ : thompsonJ R ≤ R ⊓ centralizer (V : Set G) := by
    refine iSup₂_le fun A hA => le_inf hA.1 ?_
    by_contra hAC
    have hAN : A ≤ normalizer (V : Set G) := hA.1.trans (hRT.trans S.frame.T_le)
    have hle := card_le_relIndex_mul_card hVab hVR hA
    have hlt := s4_relIndex_mul_card_lt S hAN
      (fun a ha => L1328.rho_mem_K4_of_mem_R S hhat a (hA.1 ha)) hAC
    rw [S.card_V] at hle
    omega
  have hRC : R ⊓ centralizer (V : Set G) = Q := by
    refine le_antisymm (fun x hx => ?_) (le_inf hQR (hQ ▸ inf_le_right))
    rw [← hQ]
    exact mem_inf.2 ⟨hRT (mem_inf.1 hx).1, (mem_inf.1 hx).2⟩
  refine ⟨(B6.thompsonJ_eq_of_le (S := R) (R := Q) (hJ.trans hRC.le) hQR).symm, ?_⟩
  rw [baum_eq_baum_centralizer hVab hVR hJ, hRC]

theorem false_of_thompsonJ_le (S : Setting4 G T L V)
    (hhat : IsHatA6 L) {K Y : Subgroup G} (hKM : ¬ K ≤ normalizer (L : Set G))
    (hJY : thompsonJ (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) ≤ Y)
    (hYR : Y ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) (hKY : K ≤ normalizer (Y : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJ := B6.thompsonJ_eq_of_le hJY hYR
  have h8 := (stmt13_2_2_8Nat_holds G T L V S hhat).1
  set X := thompsonJ (pCoreOf 2 (L ⊔ T)) with hX
  have hKX : K ≤ normalizer (X : Set G) := by
    rw [← h8, ← hJ]
    exact hKY.trans (normalizer_le_normalizer_thompsonJ Y)
  have hXT : X ≤ T := by
    refine (iSup₂_le fun A hA => hA.1 : X ≤ pCoreOf 2 (L ⊔ T)).trans ?_
    rw [← S.cT]
    exact inf_le_left
  have hX1 : X ≠ ⊥ := by
    obtain ⟨A, hA⟩ := exists_isMaxElemAbelian (pCoreOf 2 (L ⊔ T))
    intro hX0
    have hAX : A ≤ X := B6.le_thompsonJ hA
    rw [hX0] at hAX
    have hVab := S.elemAbelian_V
    have hVO : V ≤ pCoreOf 2 (L ⊔ T) := by
      rw [← S.cT]
      exact le_inf S.V_le_T fun v hv => mem_centralizer_iff.2 fun w hw =>
        congrArg Subtype.val (hVab.1.is_comm.comm ⟨w, hw⟩ ⟨v, hv⟩)
    have h1 := hA.2.2 V hVO hVab
    rw [le_bot_iff.1 hAX, Subgroup.card_bot, S.card_V] at h1
    omega
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge
    (⟨X, hX1, S.h13.sylow.1.to_le hXT, rfl⟩ : IsTwoLocal (normalizer (X : Set G)))
  have hM := S.uniqueM.2 M' ⟨hM', ((LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)).trans
    (normalizer_le_normalizer_thompsonJ _)).trans hle⟩
  exact hKM (hKX.trans (hM ▸ hle))

theorem normalizer_L1_le_of_hat (S : Setting4 G T L V)
    (hhat : IsHatA6 L) :
    normalizer (L₁Of L (fsuV1 T V) : Set G) ≤ normalizer (L : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L₁ := L₁Of L (fsuV1 T V) with hL₁
  set R := pCoreOf 2 (L₁ ⊔ T) with hR
  set N := normalizer (L₁ : Set G) with hN
  set C := centralizerSection N L₁ (pCoreOf 2 L₁) with hC
  have hTL : T ≤ normalizer (L : Set G) := S.T_le_NL
  have hL1L : L₁ ≤ L := S.L1_le_L
  have hTN : T ≤ N := S.T_le_normalizer_L1
  have hNR : normalizer (R : Set G) ≤ normalizer (L : Set G) := by
    by_contra hK
    exact false_of_thompsonJ_le S hhat hK (iSup₂_le fun A hA => hA.1) le_rfl le_rfl
  have hX : L₁ = oTwoUpper L₁ := by
    have h1 : L₁ ≤ oTwoRes L₁ := U3.oTwoRes_le_oTwoRes _
    rw [oTwoRes_eq_oTwoUpper] at h1
    exact le_antisymm h1 (oTwoUpper_le _)
  have hsub : IsSubnormal L₁ N :=
    A4.subnormal_of_normal Subgroup.le_normalizer (normal_subgroupOf_of_le_normalizer le_rfl)
  have hTsyl : IsSylowTwoOf T (N ⊓ normalizer (L₁ : Set G)) := by
    rw [inf_idem]
    exact A5.isSylowTwoOf_of_le S.h13.sylow hTN
  have hRsyl : IsSylowTwoOf R C := (a4_2_4 hX hsub R).1 (a4_2_5 hX hsub hTsyl)
  have hCnorm : N ≤ normalizer (C : Set G) := fun n hn =>
    A4.mem_normalizer_of_conj_mem fun m hm =>
      conj_mem_centralizerSection (Subgroup.le_normalizer hn) hn
        (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L₁ hn) hm
  have hL : CharTwo L := A5.charTwo_of_faithful S.h13.qtke.2.1 S.h13.sylow S.h13.faithful
  have hCM : C ≤ normalizer (L : Set G) := fun c hc =>
    U3.normalizer_l0_le hhat hL hTL S.uniqueM
      (U3.mem_normalizer_l0_of_mem_centralizerSection S.l0_le_L1 hL1L hc)
  intro n hn
  obtain ⟨c, hc, m, hm, rfl⟩ := U3.exists_mul_normalizer_of_isSylowTwoOf hRsyl (hCnorm hn)
  exact mul_mem (hCM hc) (hNR hm)

end L1328

end CFSG.Quasithin.H13.A6

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6

theorem stmt13_2_2_9L1Nat_holds (h1332 : Stmt13_3_2) :
    Stmt13_2_2_9L1Nat := by
  intro G _ _ T L V hH hV _ hhat hZV
  obtain ⟨S⟩ := exists_setting4_of_1332 h1332 hH hhat.2.2 hV hZV
  exact L1328.normalizer_L1_le_of_hat S hhat

theorem stmt13_2_2_9L1_holds (h1332 : Stmt13_3_2) :
    Stmt13_2_2_9L1 :=
  stmt13_2_2_9L1_of_cases (stmt13_2_2_9L1Nat_holds h1332) (stmt13_2_2_9L1Perm_holds h1332)

end CFSG.Quasithin.H13.U3
