module

public import CFSG.Quasithin.EmptyFaithful.S1421QA22Emb
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112Lie
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.GH74.Bender.Suzuki
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryCentralCover

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint

namespace S1421

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

theorem Core3Ctx.concl_of_l2 (hP : Vol2.Ch11.SecA.FactL2Parabolic)
    (h36 : A36ForSQTK) (h312 : A312ForSQTK) (h37 : A37ForSQTK) (c : Core3Ctx T M H K1 L M₁)
    {n : ℕ} (hn : 2 ≤ n) (hK : IsL2Quot n (OTwoQuot K1)) :
    Vol2.Ch11.SecA.Concl1111 (↥L ⧸ CFSG.pCore 2 ↥L) n := by
  have l := c.embLoc h37
  obtain ⟨eF⟩ := sl2Equiv_of_isL2Quot hK
  obtain ⟨eB⟩ := l.bar_equiv
  obtain ⟨eH⟩ := l.hat_equiv
  have hFc : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have hD := Vol2.Ch11.SecA.barData_of_quot_SL2 hn hFc (eB.symm.trans eF)
  have hconc : Vol2.Ch11.SecA.Concl1111 ↥(modO2Image (g0Of T M H K1) L) n := by
    rcases l.cases h312 with hc | hnq
    · exact Vol2.Ch11.SecA.concl_of_a312Case hP hD hc
    · have hQ := sqtkHyp_quotient_of_pCoreOf_ne_bot l.qtke l.simple l.nonabelian l.pCoreX
      exact Vol2.Ch11.SecA.concl_of_nonquasi hD l.bar_lt.le (h36 _ hQ _ l.hatBar_cComp) hnq
  exact Vol2.Ch11.SecA.Concl1111.of_mulEquiv eH.symm hconc

theorem Core3Ctx.twoF4_of_sz (hM : Vol2.Ch11.SecB.FactMathieuOrders)
    (h312 : A312ForSQTK) (h37 : A37ForSQTK) (c : Core3Ctx T M H K1 L M₁) {a : ℕ} (ha : 1 ≤ a)
    (e : OTwoQuot K1 ≃* ↥(Sz a)) : Is2F4 (2 * a + 1) (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have l := c.embLoc h37
  have e2 : H13.O2Q K1 ≃* OTwoQuot K1 :=
    QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥K1 2)
  have hS : SuzukiModel (H13.O2Q K1) 2 (2 * a + 1) :=
    GH74.Bender.suzukiModel_of_mulEquiv_sz ha (e2.trans e)
  exact l.twoF4_of_suzuki hM h312 hS

theorem Core3Ctx.false_of_unitary
    (hM : Vol2.Ch11.SecB.FactMathieuOrders) (h312 : A312ForSQTK) (h37 : A37ForSQTK)
    (c : Core3Ctx T M H K1 L M₁) {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2)
    (hU : Nonempty (OTwoQuot K1 ≃* CFSG.Open.StatedSU 3 (2 ^ n) F) ∨
      Nonempty (OTwoQuot K1 ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ n) F))) :
    False := by
  have l := c.embLoc h37
  have hadm := CFSG.ShultStronglyClosedTI.unitaryCover_psu_admissible n hn
  have e2 : H13.O2Q K1 ≃* OTwoQuot K1 :=
    QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥K1 2)
  have hperf : Group.IsPerfect ↥K1 := Subgroup.isPerfect_iff.mpr
    (perfect_of_mem_cComp c.st.notation_.cComp_mem)
  have hperfX : Group.IsPerfect (H13.O2Q K1) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K1))
  have hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ n) F))
      .PSU 3 2 n :=
    ⟨hadm, F, inferInstance, inferInstance, hF, ⟨MulEquiv.refl _⟩⟩
  have hsimple : IsSimpleGroup
      (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ n) F)) :=
    (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 2 n hmodel).2
  have hU' : CFSG.IsQuasisimple (H13.O2Q K1) ∧
      LieModel (H13.O2Q K1 ⧸ Subgroup.center (H13.O2Q K1)) .PSU 3 2 n := by
    rcases hU with ⟨⟨eX⟩⟩ | ⟨⟨eX⟩⟩
    ·
      let eXc : H13.O2Q K1 ≃* CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ n) F := e2.trans eX
      have hperfSU : Group.IsPerfect ↥(CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ n) F) :=
        Group.IsPerfect.ofSurjective (f := eXc.toMonoidHom) eXc.surjective
      have hqSU : CFSG.IsQuasisimple ↥(CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ n) F) :=
        CFSG.LieType.Universal.Spin.isQuasisimple_of_isSimpleGroup_statedProj
      have hcen := CFSG.LieType.Universal.Spin.center_eq_statedScalars_subgroupOf
        (H := CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ n) F)
      refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv eXc.symm hqSU, Or.inl ⟨by decide, hadm,
        F, inferInstance, inferInstance, hF, ⟨?_⟩⟩⟩
      exact (QuotientGroup.congr _ _ eXc (Subgroup.map_center_eq eXc)).trans
        (QuotientGroup.quotientMulEquivOfEq hcen)
    ·
      let eXc : H13.O2Q K1 ≃* CFSG.Assembly.LowTwoRank.StatedProj
          (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ n) F) := e2.trans eX
      have hsX : IsSimpleGroup (H13.O2Q K1) := eXc.isSimpleGroup
      have hq : CFSG.IsQuasisimple (H13.O2Q K1) :=
        H13.isQuasisimple_of_isSimpleGroup_of_isPerfect
      have hnc := Group.IsPerfect.not_isMulCommutative (H13.O2Q K1)
      have hZ : Subgroup.center (H13.O2Q K1) = ⊥ := by
        rcases hsX.eq_bot_or_eq_top_of_normal (Subgroup.center (H13.O2Q K1)) with h | h
        · exact h
        · exact absurd (Subgroup.center_eq_top_iff.mp h) hnc
      refine ⟨hq, Or.inl ⟨by decide, hadm, F, inferInstance, inferInstance, hF, ⟨?_⟩⟩⟩
      exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans eXc
  exact l.false_of_unitary hM h312 hn hU'.1 hU'.2

theorem Core3Ctx.bender_cases
    (hM : Vol2.Ch11.SecB.FactMathieuOrders) (hP : Vol2.Ch11.SecA.FactL2Parabolic)
    (h36 : A36ForSQTK) (h312 : A312ForSQTK) (h37 : A37ForSQTK) (c : Core3Ctx T M H K1 L M₁) :
    (∃ n : ℕ, 2 ≤ n ∧ IsL2Quot n (OTwoQuot K1) ∧
        Vol2.Ch11.SecA.Concl1111 (↥L ⧸ CFSG.pCore 2 ↥L) n) ∨
      (∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ ReeTitsModel (↥L ⧸ CFSG.pCore 2 ↥L) .twistedF4 2 f) := by
  obtain ⟨n, hn, hB⟩ := c.st.notation_.bender
  rcases hB with hL2 | ⟨a, hna, ⟨e⟩⟩ | ⟨F, iF, iFin, hF, hU⟩ | ⟨F, iF, iFin, hF, hU⟩
  · exact Or.inl ⟨n, hn, hL2, c.concl_of_l2 hP h36 h312 h37 hn hL2⟩
  · subst hna
    have ha : 1 ≤ a := by omega
    exact Or.inr ⟨2 * a + 1, odd_two_mul_add_one a, by omega,
      c.twoF4_of_sz hM h312 h37 ha e⟩
  · exact (c.false_of_unitary hM h312 h37 hn hF (Or.inl hU)).elim
  · exact (c.false_of_unitary hM h312 h37 hn hF (Or.inr hU)).elim

end S1421

end CFSG.Quasithin
