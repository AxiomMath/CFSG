module

public import CFSG.Quasithin.Background.G64ProofBasic
public import CFSG.Quasithin.Vol2.Ch10SecB6C23

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G]

structure RCtx (T L I R H : Subgroup G) : Prop where
  hyp : Hyp10 G T L I
  two : pCoreOf 2 H ≠ ⊥
  le : fsuL0 T L ⊔ R ≤ H
  sylow : IsSylowTwoOf R H
  le_T1 : R ≤ T1 T L
  pcore : pCoreOf 2 (fsuL0 T L ⊔ T) ≤ R
  not_le : ¬ H ≤ fsuM T L

namespace RCtx

variable {T L I R H : Subgroup G} (c : RCtx T L I R H)
include c

theorem fsuL0_le : fsuL0 T L ≤ H := le_sup_left.trans c.le

theorem R_le : R ≤ H := le_sup_right.trans c.le

theorem R_le_fsuM : R ≤ fsuM T L := c.le_T1.trans (inf_le_left.trans (SecA.le_fsuM T L))

theorem pCoreOf_le_fsuM : pCoreOf 2 H ≤ fsuM T L :=
  (CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf c.sylow).trans c.R_le_fsuM

theorem fsuVM_le : fsuVM T L I ≤ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((SecA.fsuVM_le_T c.hyp).trans le_sup_right) ?_ (SecA.isPGroup_fsuVM c.hyp)).trans c.pcore
  exact sup_le (SecA.fsuL0_le_normalizer_fsuVM T L I) (SecA.le_normalizer_fsuVM T L I)

theorem pCoreOf_fsuM_le : pCoreOf 2 (fsuM T L) ≤ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : IsSylowTwoOf T (fsuM T L) :=
    CFSG.Quasithin.isSylowTwoOf_of_quasithinIsSylowTwo c.hyp.fsu.sylow (SecA.le_fsuM T L)
  have hL0TM : fsuL0 T L ⊔ T ≤ fsuM T L := sup_le (SecA.fsuL0_le_fsuM T L) (SecA.le_fsuM T L)
  exact (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hT).trans le_sup_right)
    (hL0TM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)).trans c.pcore

theorem oddCoreOf_eq_bot (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h331 : Stmt3_3_1) : A37.oddCoreOf H = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := c.hyp
  have hV := SecA.isElemAbelian_fsuVM hyp
  have hVO : fsuVM T L I ≤ Subgroup.centralizer (fusionOddCoreOf H : Set G) :=
    a126_one c.fsuL0_le (C2Nine.opResidual_eq_of_perfect (SecB.fsuL0_perfect' h37 h38 hyp))
      (c.fsuVM_le.trans c.R_le) (SecA.isPGroup_fsuVM hyp)
      (SecA.fsuVM_eq_commutator hyp.fsu).symm
      (fun p hp hp2 => (CFSG.SectionRank.pRank_mono hp.one_lt
        (CFSG.LieType.BorelTits.pCoreOf_le p H)).trans
          (pRank_le_two_of_pCoreOf_ne_bot hyp.fsu.qtke c.two hp hp2))
      (C2Nine.frattiniIn_eq_bot_of_isElemAbelian hV)
  have hOV : A37.oddCoreOf H ≤ Subgroup.centralizer (fsuVM T L I : Set G) :=
    Subgroup.le_centralizer_iff.mp hVO
  have hNV := SecA.normalizer_fsuVM_eq hyp (SecB.fsuM_isMaxTwoLocal h331 hyp)
  have hOM : A37.oddCoreOf H ≤ fsuM T L :=
    hOV.trans ((Subgroup.centralizer_le_normalizer _).trans hNV.le)
  have h1 : ⁅pCoreOf 2 (fsuM T L), A37.oddCoreOf H⁆ ≤ pCoreOf 2 (fsuM T L) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hOM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
  have h2 : ⁅pCoreOf 2 (fsuM T L), A37.oddCoreOf H⁆ ≤ A37.oddCoreOf H := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((c.pCoreOf_fsuM_le.trans c.R_le).trans (SecB.le_normalizer_oddCoreOf' H))
  have hinf : pCoreOf 2 (fsuM T L) ⊓ A37.oddCoreOf H = ⊥ :=
    SecB.inf_eq_bot_of_two_odd (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
      (SecB.odd_card_oddCoreOf H)
  have hc : ⁅pCoreOf 2 (fsuM T L), A37.oddCoreOf H⁆ = ⊥ := le_bot_iff.mp (hinf ▸ le_inf h1 h2)
  have hOC : A37.oddCoreOf H ≤ Subgroup.centralizer (pCoreOf 2 (fsuM T L) : Set G) :=
    Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc)
  have hO2 : A37.oddCoreOf H ≤ pCoreOf 2 (fsuM T L) :=
    fun x hx => SecB.charTwo_fsuM hyp ⟨hOM hx, hOC hx⟩
  exact le_bot_iff.mp (hinf ▸ le_inf hO2 le_rfl)

theorem hypC23Cat (hK : LocalSQTK G) (h331 : Stmt3_3_1) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) :
    EmptyFaithfulMultiple.HypC23Cat H (pCoreOf 2 (fsuL0 T L ⊔ T)) (fsuM T L ⊓ H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := c.hyp
  set Q := pCoreOf 2 (fsuL0 T L ⊔ T) with hQdef
  have hQp : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hQ1 : Q ≠ ⊥ := SecA.pCoreOf_L0T_ne_bot hyp
  have hQH : Q ≤ H := c.pcore.trans c.R_le
  have hL0TN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hNQ := SecB.normalizer_le_fsuM_of_L0T h331 hyp hQp hQ1 hL0TN
  have hT : IsSylowTwoOf T (fsuM T L) :=
    CFSG.Quasithin.isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow (SecA.le_fsuM T L)
  have h427 := a4_2_7 (eq_oTwoUpper_of_perfect (SecB.fsuL0_perfect' h37 h38 hyp))
    (SecA.fsuL0_le_fsuM T L) (Subgroup.normal_subgroupOf_of_le_normalizer le_rfl) hT rfl hNQ
  refine ⟨hK H c.two, ⟨hQH, hQ1, ?_⟩, inf_le_right, ?_, ?_⟩
  ·
    refine le_antisymm (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (le_inf hQH Subgroup.le_normalizer) inf_le_right hQp) ?_
    set P := pCoreOf 2 (H ⊓ Subgroup.normalizer (Q : Set G)) with hPdef
    have hPp : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
    have hPN : H ⊓ Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (P : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
    have hQP : Q ≤ Subgroup.normalizer (P : Set G) :=
      (le_inf hQH Subgroup.le_normalizer).trans hPN
    have hL0N : fsuL0 T L ≤ H ⊓ Subgroup.normalizer (Q : Set G) :=
      le_inf c.fsuL0_le (le_sup_left.trans hL0TN)
    have hsig : IsSignalizer (fsuM T L) (fsuL0 T L) (P ⊔ Q) := by
      refine ⟨sup_le ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (inf_le_right.trans hNQ))
        (c.pcore.trans c.R_le_fsuM), IsPGroup.to_sup_of_normal_left' hPp hQp hQP, ?_⟩
      intro l hl
      have e1 := Subgroup.mem_normalizer_iff_map_conj_eq.mp ((hL0N.trans hPN) hl)
      have e2 := Subgroup.mem_normalizer_iff_map_conj_eq.mp ((le_sup_left.trans hL0TN) hl)
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup, e1, e2]
    have heq := h427.2.2.1.eq_of_le hsig le_sup_right
    exact le_sup_left.trans heq.le
  ·
    refine iSup₂_le fun C hCQ => iSup₂_le fun hC1 hCc => ?_
    have hCN : Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (C : Set G) := by
      have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (H := Q) (C.subgroupOf Q)
      rwa [Subgroup.map_subgroupOf_eq_of_le hCQ] at h
    exact le_inf (inf_le_right.trans (SecB.normalizer_le_fsuM_of_L0T h331 hyp (hQp.to_le hCQ)
      hC1 (hL0TN.trans hCN))) inf_le_left
  ·
    exact B6.isSylowTwoOf_mono h427.2.2.2.2.2 (le_conjClosure Q _)
      (conjClosure_mono le_rfl inf_le_left)

theorem hypC23 (hK : LocalSQTK G) (h331 : Stmt3_3_1) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) :
    HypC23 H (pCoreOf 2 (fsuL0 T L ⊔ T)) (fsuM T L ⊓ H) := by
  have h := c.hypC23Cat hK h331 h37 h38
  exact ⟨G64.sqtkGroup_of_isSQTKCat h.sqtk, h.radical, h.le, h.cgs, h.sylow⟩

end RCtx

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
