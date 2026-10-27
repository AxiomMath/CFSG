module

public import CFSG.Quasithin.EmptyFaithful.S1421QA24Emb
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112Lie
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.GH74.Bender.Suzuki
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryCentralCover

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint

namespace QA24

open Vol2.Ch11.SecA

theorem n_eq_two_of_nonquasi {Q : Type} [Group Q] [Finite Q] {B L : Subgroup Q} {n : ℕ}
    (hD : BarData B n) (hBL : B ≤ L) (h36 : A36Strong L) (h : A312Nonquasi B L) : n = 2 := by
  have hnq := A312.not_quasisimple_of_nonquasi h
  obtain ⟨p₀, hp₀, hp₀3, hΛ⟩ := A312.exists_isSL2_oddCore h36 hnq
  have hr5₀ : 5 ≤ p₀ := A313.five_le_of_prime hp₀ hp₀3
  unfold A312Nonquasi at h
  dsimp only at h
  rcases h with ⟨-, hLB, -⟩ | ⟨-, -, N, hNn, hNeq, hN5⟩
  · have htop : A313.imgOdd (B.subgroupOf L) = ⊤ := (A313.imgOdd_eq_top_iff hBL).mpr hLB
    have hM : IsSL2 p₀ ↥(A313.imgOdd (B.subgroupOf L)) :=
      IsSL2.of_mulEquiv ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).symm hΛ
    have hB := hD.isSL2_of_imgOdd hBL hp₀ hr5₀ hM
    obtain ⟨a, ha⟩ := hD.card
    obtain ⟨-, hn⟩ := eq_five_of_sl2 hp₀ (by omega) hD.two_le (b := a + n) (by omega)
      (by rw [← card_of_isSL2 hp₀ hB, ha])
    exact hn
  · subst hNeq
    have hM : IsSL2 5 ↥(A313.imgOdd (B.subgroupOf L)) :=
      IsSL2.of_mulEquiv (A312.quotEquivImage hBL) hN5
    have hB := hD.isSL2_of_imgOdd hBL Nat.prime_five le_rfl hM
    obtain ⟨a, ha⟩ := hD.card
    obtain ⟨-, hn⟩ := eq_five_of_sl2 Nat.prime_five (by norm_num) hD.two_le (b := a + n)
      (by omega) (by rw [← card_of_isSL2 Nat.prime_five hB, ha])
    exact hn

section Context

variable {G : Type} [Group G] [Finite G] {T M H K1 L M₁ : Subgroup G}

omit [Finite G] in
theorem sl2Equiv_of_isL2Quot {K : Subgroup G} {f : ℕ} (h : IsL2Quot f (OTwoQuot K)) :
    Nonempty (ModO2 K ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) := by
  obtain ⟨e⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨((QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥K 2)).trans e).trans
    ((CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 2
      (GaloisField 2 f)).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSLTwoEquivSL (GaloisField 2 f)))⟩

theorem isL2Quot_two (hSL2 : A312SL2Fact) (h36 : A36ForSQTK)
    (h37 : A37ForSQTK) (c : S1421.Core3Ctx T M H K1 L M₁)
    (hnq : ¬ CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) : IsL2Quot 2 (OTwoQuot K1) := by
  obtain ⟨-, h36', hA⟩ := nonquasi_data hSL2 h36 h37 c hnq
  have l := embLoc h37 c
  obtain ⟨n, hn, hB⟩ := c.st.notation_.bender
  have : Group.IsPerfect ↥K1 :=
    Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp c.st.notation_.cComp_mem)
  have e2 : H13.O2Q K1 ≃* OTwoQuot K1 :=
    QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥K1 2)
  rcases hB with hL2 | ⟨a, hna, ⟨e⟩⟩ | ⟨F, iF, iFin, hF, hU⟩ | ⟨F, iF, iFin, hF, hU⟩
  · obtain ⟨eF⟩ := sl2Equiv_of_isL2Quot hL2
    obtain ⟨eB⟩ := l.bar_equiv
    have hFc : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
    have hD := barData_of_quot_SL2 hn hFc (eB.symm.trans eF)
    have hn2 : n = 2 := n_eq_two_of_nonquasi hD l.bar_lt.le h36' hA
    subst hn2
    exact hL2
  · exfalso
    subst hna
    have ha : 1 ≤ a := by omega
    have hS : SuzukiModel (H13.O2Q K1) 2 (2 * a + 1) :=
      GH74.Bender.suzukiModel_of_mulEquiv_sz ha (e2.trans e)
    have : IsSimpleGroup (H13.O2Q K1) := (CFSG.LieType.Simplicity.fam_2b2_simplicity _ 2 _ hS).2
    have hq : CFSG.IsQuasisimple (H13.O2Q K1) := H13.isQuasisimple_o2q_of_simple
    have hS' : IsSz (2 * a + 1) (H13.O2Q K1) := hS
    exact Vol2.Ch11.SecB.false_of_a312Nonquasi (k := 2 * a + 1)
      (by obtain ⟨-, hk3, -⟩ := Vol2.Ch11.SecB.card_isSz hS'; omega) (Or.inl hS')
      (H13.openQuasisimple_of hq) (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
      l.bar_lt.le (H13.barMap l.le_X) (H13.barMap_surjective _) hA
  · exfalso
    obtain ⟨eX⟩ := hU
    have hadm := CFSG.ShultStronglyClosedTI.unitaryCover_psu_admissible n hn
    have hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
        (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ n) F))
        .PSU 3 2 n := ⟨hadm, F, inferInstance, inferInstance, hF, ⟨MulEquiv.refl _⟩⟩
    have hsimple : IsSimpleGroup
        (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ n) F)) :=
      (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 2 n hmodel).2
    let eXc : H13.O2Q K1 ≃* CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ n) F := e2.trans eX
    have hperfSU : Group.IsPerfect ↥(CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ n) F) :=
      Group.IsPerfect.ofSurjective (f := eXc.toMonoidHom) eXc.surjective
    have hqSU : CFSG.IsQuasisimple ↥(CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ n) F) :=
      CFSG.LieType.Universal.Spin.isQuasisimple_of_isSimpleGroup_statedProj
    have hcen := CFSG.LieType.Universal.Spin.center_eq_statedScalars_subgroupOf
      (H := CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ n) F)
    have hq : CFSG.IsQuasisimple (H13.O2Q K1) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv eXc.symm hqSU
    have eY : (H13.O2Q K1 ⧸ Subgroup.center (H13.O2Q K1)) ≃*
        CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ n) F) :=
      (QuotientGroup.congr _ _ eXc (Subgroup.map_center_eq eXc)).trans
        (QuotientGroup.quotientMulEquivOfEq hcen)
    have hY : IsPSU 3 2 n (H13.O2Q K1 ⧸ Subgroup.center (H13.O2Q K1)) :=
      ⟨hadm, F, inferInstance, inferInstance, hF, ⟨eY⟩⟩
    exact Vol2.Ch11.SecB.false_of_a312Nonquasi (k := n) hn (Or.inr (Or.inl hY))
      (H13.openQuasisimple_of hq)
      ((QuotientGroup.mk' (Subgroup.center (H13.O2Q K1))).comp (QuotientGroup.mk' _))
      ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
      l.bar_lt.le (H13.barMap l.le_X) (H13.barMap_surjective _) hA
  · exfalso
    obtain ⟨eX⟩ := hU
    have hadm := CFSG.ShultStronglyClosedTI.unitaryCover_psu_admissible n hn
    have hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
        (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ n) F))
        .PSU 3 2 n := ⟨hadm, F, inferInstance, inferInstance, hF, ⟨MulEquiv.refl _⟩⟩
    let eXc : H13.O2Q K1 ≃* CFSG.Assembly.LowTwoRank.StatedProj
        (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ n) F) := e2.trans eX
    have hsimple : IsSimpleGroup
        (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ n) F)) :=
      (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 2 n hmodel).2
    have hsX : IsSimpleGroup (H13.O2Q K1) := eXc.isSimpleGroup
    have hq : CFSG.IsQuasisimple (H13.O2Q K1) :=
      H13.isQuasisimple_of_isSimpleGroup_of_isPerfect
    have hnc := Group.IsPerfect.not_isMulCommutative (H13.O2Q K1)
    have hZ : Subgroup.center (H13.O2Q K1) = ⊥ := by
      rcases hsX.eq_bot_or_eq_top_of_normal (Subgroup.center (H13.O2Q K1)) with h | h
      · exact h
      · exact absurd (Subgroup.center_eq_top_iff.mp h) hnc
    have hY : IsPSU 3 2 n (H13.O2Q K1 ⧸ Subgroup.center (H13.O2Q K1)) :=
      ⟨hadm, F, inferInstance, inferInstance, hF,
        ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans eXc⟩⟩
    exact Vol2.Ch11.SecB.false_of_a312Nonquasi (k := n) hn (Or.inr (Or.inl hY))
      (H13.openQuasisimple_of hq)
      ((QuotientGroup.mk' (Subgroup.center (H13.O2Q K1))).comp (QuotientGroup.mk' _))
      ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
      l.bar_lt.le (H13.barMap l.le_X) (H13.barMap_surjective _) hA

end Context

end QA24

end CFSG.Quasithin
