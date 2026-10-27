module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec8.Hering418ROuter
public import CFSG.RankThree.PartTwo.Sec8.Hering418RSix

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF418
open CFSG.Open (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag

@[expose] def IsMinusPiSix (X : Type) [Group X] : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ Sec8.IsoLThreeMinusPi X 2 (3 * n)

theorem isPGroup_three_closure_pair {M : Type*} [Group M] {s t : M} (hs : s ^ 3 = 1)
    (ht : t ^ 3 = 1) (hst : Commute s t) : IsPGroup 3 (Subgroup.closure ({s, t} : Set M)) := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  obtain ⟨i, j, hij⟩ := (mem_closure_pair_iff hst).mp g.2
  have hs' : Commute (s ^ i) (t ^ j) := (hst.zpow_left i).zpow_right j
  have h1 : (s ^ i) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hs, one_zpow]
  have h2 : (t ^ j) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht, one_zpow]
  rw [pow_one, SubgroupClass.coe_pow, hij, hs'.mul_pow, h1, h2, one_mul]
  exact (OneMemClass.coe_one _).symm

theorem isSimpleGroup_of_isQuasisimple_of_center_bot {X : Type} [Group X]
    (hq : IsQuasisimple X) (hZ : Subgroup.center X = ⊥) : IsSimpleGroup X := by
  haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := hq.2.1
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup

theorem bound_inner_of_hom {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (φ : MulAut X →* MulAut Y) (hφ : Function.Injective φ) (N : Subgroup (MulAut Y))
    (hinn : ∀ x : X, φ (MulAut.conj x) ∈ N)
    (hN : ∀ F : Subgroup (MulAut Y), IsElemAbelian 3 F → F ≤ N → Nat.card F ≤ 9) :
    ∀ F : Subgroup (MulAut X), IsElemAbelian 3 F →
      F ≤ (MulAut.conj : X →* MulAut X).range → Nat.card F ≤ 9 := by
  intro F hF hFi
  have hle : F.map φ ≤ N := by
    rintro _ ⟨σ, hσ, rfl⟩
    obtain ⟨x, rfl⟩ := hFi hσ
    exact hinn x
  have := hN _ (hF.map φ) hle
  rwa [Subgroup.card_map_of_injective hφ] at this

section Minus


theorem bound_inner_isoLThreeMinusPi {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 1 ≤ n)
    (hX : Sec8.IsoLThreeMinusPi X 2 (3 * n)) :
    ∀ F : Subgroup (MulAut X), IsElemAbelian 3 F →
      F ≤ (MulAut.conj : X →* MulAut X).range → Nat.card F ≤ 9 := by
  rcases hX with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
  ·
    have hU := Sec4.unitaryFieldData_galoisField 2 (3 * n) (by omega)
    have := hU.finite
    have h3 : (3 : GaloisField 2 (2 * (3 * n))) ≠ 0 :=
      Sec4.three_ne_zero_of_card Nat.prime_two (by norm_num)
        (GaloisField.card 2 (2 * (3 * n)) (by omega))
    let e' : X ≃* unitaryPSU hU 3 := φ.trans (Sec4.projSUEquivUnitaryPSU 2 (3 * n) hU)
    refine bound_inner_of_hom (MulAut.congr e').toMonoidHom (MulAut.congr e').injective
      (KFacts.psuConj hU).range ?_ ?_
    · intro x
      rw [MulEquiv.coe_toMonoidHom, KFacts.congr_mulAutConj]
      exact (KFacts.stdPinnedPSU3 hU).inn_le ⟨e' x, rfl⟩
    · intro F' hF' hFN
      exact Sec21.Item223CensusProof.card_le_nine_of_le_psuConj_range h3 F' hF' hFN
  ·
    set F := GaloisField 2 (3 * n) with hFdef
    have hFcard : Nat.card F = 2 ^ (3 * n) := GaloisField.card 2 (3 * n) (by omega)
    have h3 : (3 : F) ≠ 0 := Sec4.three_ne_zero_of_card Nat.prime_two (by norm_num) hFcard
    let e' : X ≃* projectiveSL 3 F := φ.trans (Sec4.projSLEquivProjectiveSL 3 F)
    refine bound_inner_of_hom (MulAut.congr e').toMonoidHom (MulAut.congr e').injective
      (linearAutGroup 3 F) ?_ ?_
    · intro x
      rw [MulEquiv.coe_toMonoidHom, KFacts.congr_mulAutConj]
      exact KFacts.innAut_le_linearAutGroup 3 F ⟨e' x, rfl⟩
    · intro F' hF' hFN
      have := Sec4.card_inf_linearAutGroup_three_le h3 hF'
      rwa [inf_eq_left.mpr hFN] at this

theorem inducesStdKind_field_of_isoLThreeMinusPi {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {n : ℕ} (hn : 1 ≤ n) (hX : Sec8.IsoLThreeMinusPi (L ⧸ aschbacherSolvableCore 3 L) 2 (3 * n))
    {x : G} (hx3 : x ^ 3 = 1) (hout : Sec4.InducesOuterTheta x L) :
    KFacts.InducesStdKind L x .field := by
  obtain ⟨hx, -⟩ := id hout
  rcases hX with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
  ·
    have hU := Sec4.unitaryFieldData_galoisField 2 (3 * n) (by omega)
    have hq2 : 2 < 2 ^ (3 * n) :=
      lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ 3 * n))
    let e' : L ⧸ aschbacherSolvableCore 3 L ≃* unitaryPSU hU 3 :=
      φ.trans (Sec4.projSUEquivUnitaryPSU 2 (3 * n) hU)
    have hτ3 := KFacts.inducedAutHom_pow_eq_one L e' hx hx3
    have hτout := (KFacts.not_isInnerAut_inducedAutHom_iff L e' hx).mpr hout
    have hD : KFacts.inducedAutHom L e' ⟨x, hx⟩ ∉ (KFacts.psuConj hU).range := fun hm =>
      hτout (KFacts.isInnerAut_of_mem_psuConj_range hU hq hm)
    exact KFacts.InducesStdKind.psu3 hU hq2
      ⟨e', hx, KFacts.isField_psu3_of_pow_three_eq_one hq2 hτ3 hD⟩
  ·
    set F := GaloisField 2 (3 * n) with hFdef
    have hFcard : Nat.card F = 2 ^ (3 * n) := GaloisField.card 2 (3 * n) (by omega)
    have hFmod : Nat.card F % 3 = 2 := by rw [hFcard]; exact hq
    let e' : L ⧸ aschbacherSolvableCore 3 L ≃* projectiveSL 3 F :=
      φ.trans (Sec4.projSLEquivProjectiveSL 3 F)
    have hτ3 := KFacts.inducedAutHom_pow_eq_one L e' hx hx3
    have hτout := (KFacts.not_isInnerAut_inducedAutHom_iff L e' hx).mpr hout
    have hD : KFacts.inducedAutHom L e' ⟨x, hx⟩ ∉ linearAutGroup 3 F := fun hm =>
      hτout (KFacts.isInnerAut_of_mem_linearAutGroup hFmod hm)
    exact KFacts.InducesStdKind.psl 3 F le_rfl
      ⟨e', hx, KFacts.isField_of_pow_three_eq_one le_rfl hτ3 hD⟩

theorem kF418OuterOn_minusPiSix : KF418OuterOn (fun X _ => IsMinusPiSix X) := by
  intro G _ _ L hL hl a b ha3 hb3 hab hb1 habz haN hbN hbC haC K hK n hn htype hKa hbk
  obtain ⟨m, hm, hX⟩ := hl
  have c := Cfg.of_model hK ha3 hb3 hab haN hbN hbC haC hKa
  have hKq := Sec6.isQuasisimple_of_mem_thetaComponentsIn hK
  have hβ : Sec4.InducesOuterTheta b L := by
    rcases hbk with h | h
    · exact KFacts.InducesStdKind.inducesOuterTheta (k := .field) L h (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta (k := .graphField) L h (by decide)
  have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
    KFacts.center_eq_bot_of_isoLThreeMinusPi hm hX
  have hβout : ¬ KFacts.IsInnerAut c.beta := hβ.2
  obtain ⟨hZC, hQC, -⟩ := KFacts.fixedPoints_facts_of_isoLThreeMinusPi hm hX c.beta_pow_three hβout
  have hCeq : Sec8.barCentralizer (Subgroup.zpowers b) L =
      c.beta.toMonoidHom.eqLocus (MonoidHom.id _) := by
    ext y
    exact KFacts.mem_barCentralizer_zpowers_iff c.hbL y
  have hsimple : IsSimpleGroup ↥(Sec8.barCentralizer (Subgroup.zpowers b) L) := by
    rw [hCeq]
    exact isSimpleGroup_of_isQuasisimple_of_center_bot hQC hZC
  have hC := barCentralizer_le_imageModTheta_of_simple c.hbL hb3 hK hsimple
    (imageModTheta_ne_bot c.hKL hKq)
  have hinn : ∃ j : ℕ, c.alpha * c.beta ^ j ∈ innBar L := by
    obtain ⟨i, hi⟩ := KFacts.exists_pow_mul_isInnerAut_of_isoLThreeMinusPi hm hX
      (P := Subgroup.closure ({c.beta, c.alpha} : Set _))
      (isPGroup_three_closure_pair c.beta_pow_three c.alpha_pow_three c.alpha_mul_beta.symm)
      (Subgroup.subset_closure (Set.mem_insert _ _))
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)) c.beta_pow_three hβout
      c.alpha_pow_three
    refine ⟨i, ?_⟩
    have hcab : Commute c.alpha c.beta := c.alpha_mul_beta
    have hcomm : Commute c.alpha (c.beta ^ i) := hcab.pow_right i
    rw [hcomm.eq]
    exact hi
  exact c.false_of_outer_core hZ hinn hC

theorem kF418ModelOn_minusPiSix : KF418ModelOn (fun X _ => IsMinusPiSix X) :=
  kF418ModelOn_of_outer
    (fun X _ _ ⟨n, hn, hX⟩ => bound_inner_isoLThreeMinusPi hn hX)
    (fun G _ _ L hL ⟨n, hn, hX⟩ x hx3 hout =>
      Or.inl (inducesStdKind_field_of_isoLThreeMinusPi hn hX hx3 hout))
    kF418OuterOn_minusPiSix

end Minus

end CFSG.RankThree.PartTwo.Sec8.Hering418
