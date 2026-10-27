module

public import CFSG.Quasithin.Vol2.Ch10SecQ4NQ2

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem isPGroup_VK (hyp : Hyp10 G T L I) {K : Subgroup G} (hK : Ch10.IsLi T L K) :
    IsPGroup 2 (⁅fsuVM T L I, K⁆ : Subgroup G) :=
  (SecA.isPGroup_fsuVM hyp).to_le (VK_le_fsuVM hK)

theorem pCoreOf_normalizer_VK_ne_bot (hyp : Hyp10 G T L I) (h2 : Ch10.Case10_1_1Two T L I)
    {K : Subgroup G} (hK : Ch10.IsLi T L K) :
    pCoreOf 2 (Subgroup.normalizer ((⁅fsuVM T L I, K⁆ : Subgroup G) : Set G)) ≠ ⊥ :=
  SecB.pCoreOf_normalizer_ne_bot' (isPGroup_VK hyp hK) (VK_ne_bot hyp h2 hK)

theorem isSylowTwoOf_normalizer_VK
    (h311 : Theorem311Stmt) (h331 : Stmt3_3_1) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hshape : Stmt7_0_1_shape) (hyp : Hyp10 G T L I)
    (h2 : Ch10.Case10_1_1Two T L I) {K : Subgroup G} (hK : Ch10.IsLi T L K) :
    IsSylowTwoOf (Ch10.T1 T L)
      (Subgroup.normalizer ((⁅fsuVM T L I, K⁆ : Subgroup G) : Set G)) := by
  by_contra hns
  obtain ⟨m, hmN, hTm⟩ := exists_conj_of_not_isSylowTwoOf hyp.fsu.sylow inf_le_left
    (SecA.index_T1 h37 h38 hyp) (SecE.le_normalizer_T1 h37 h38 hyp)
    (le_sup_right.trans (le_normalizer_VK h37 h38 hyp hK)) hns
  have hmM : m ∈ fsuM T L :=
    SecE.normalizer_T1_le h311 h331 h37 h38 hshape hyp (Or.inr h2) hmN
  refine not_le_normalizer_conjugate_VK h37 h38 hyp h2 hK ((fsuM T L).inv_mem hmM)
    fun x hx => mem_normalizer_conjugate ?_
  rw [inv_inv]
  exact B6.mem_conjSub.mp (hTm hx)

theorem pCoreOf_fsuM_le_T1' (hyp : Hyp10 G T L I) : pCoreOf 2 (fsuM T L) ≤ Ch10.T1 T L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : IsSylowTwoOf T (fsuM T L) :=
    CFSG.Quasithin.isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow (SecA.le_fsuM T L)
  have hL0TM : fsuL0 T L ⊔ T ≤ fsuM T L := sup_le (SecA.fsuL0_le_fsuM T L) (SecA.le_fsuM T L)
  refine (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hT).trans le_sup_right)
    (hL0TM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)).trans (SecB.pCoreOf_L0T_le_T1 hyp)

theorem oddCoreOf_eq_bot' (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h331 : Stmt3_3_1) (hyp : Hyp10 G T L I) {H : Subgroup G}
    (hL0T1 : fsuL0 T L ⊔ Ch10.T1 T L ≤ H) (hH2 : pCoreOf 2 H ≠ ⊥) : A37.oddCoreOf H = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV := SecA.isElemAbelian_fsuVM hyp
  have hL0H : fsuL0 T L ≤ H := le_sup_left.trans hL0T1
  have hT1H : Ch10.T1 T L ≤ H := le_sup_right.trans hL0T1
  have hVT1 := SecB.fsuVM_le_T1 h37 h38 hyp
  have hVO : fsuVM T L I ≤ Subgroup.centralizer (fusionOddCoreOf H : Set G) :=
    a126_one hL0H (C2Nine.opResidual_eq_of_perfect (SecB.fsuL0_perfect' h37 h38 hyp))
      (hVT1.trans hT1H) (SecA.isPGroup_fsuVM hyp) (SecA.fsuVM_eq_commutator hyp.fsu).symm
      (fun p hp hp2 => (CFSG.SectionRank.pRank_mono hp.one_lt
        (CFSG.LieType.BorelTits.pCoreOf_le p H)).trans
          (pRank_le_two_of_pCoreOf_ne_bot hyp.fsu.qtke hH2 hp hp2))
      (C2Nine.frattiniIn_eq_bot_of_isElemAbelian hV)
  have hOV : A37.oddCoreOf H ≤ Subgroup.centralizer (fsuVM T L I : Set G) :=
    Subgroup.le_centralizer_iff.mp hVO
  have hNV := SecA.normalizer_fsuVM_eq hyp (SecB.fsuM_isMaxTwoLocal h331 hyp)
  have hOM : A37.oddCoreOf H ≤ fsuM T L :=
    hOV.trans ((Subgroup.centralizer_le_normalizer _).trans hNV.le)
  have hPM := pCoreOf_fsuM_le_T1' hyp
  have h1 : ⁅pCoreOf 2 (fsuM T L), A37.oddCoreOf H⁆ ≤ pCoreOf 2 (fsuM T L) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hOM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
  have h2 : ⁅pCoreOf 2 (fsuM T L), A37.oddCoreOf H⁆ ≤ A37.oddCoreOf H := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((hPM.trans hT1H).trans (SecB.le_normalizer_oddCoreOf' H))
  have hinf : pCoreOf 2 (fsuM T L) ⊓ A37.oddCoreOf H = ⊥ :=
    SecB.inf_eq_bot_of_two_odd (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
      (SecB.odd_card_oddCoreOf H)
  have hc : ⁅pCoreOf 2 (fsuM T L), A37.oddCoreOf H⁆ = ⊥ := le_bot_iff.mp (hinf ▸ le_inf h1 h2)
  have hOC : A37.oddCoreOf H ≤ Subgroup.centralizer (pCoreOf 2 (fsuM T L) : Set G) :=
    Subgroup.le_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc)
  have hO2 : A37.oddCoreOf H ≤ pCoreOf 2 (fsuM T L) :=
    fun x hx => SecB.charTwo_fsuM hyp ⟨hOM hx, hOC hx⟩
  exact le_bot_iff.mp (hinf ▸ le_inf hO2 le_rfl)

end CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F
