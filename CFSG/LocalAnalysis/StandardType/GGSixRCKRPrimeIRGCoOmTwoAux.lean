module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGCoSl2Gen
public import CFSG.LocalAnalysis.StandardType.GGRankOneSl2
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalOmegaMinusModel
public import CFSG.Timmesfeld.RankTwo.LevisMinusN
public import CFSG.LieType.Universal.Spin.Twisted.Unipotent
public import CFSG.LieType.Universal.Spin.Twisted.Generation
public import CFSG.LieType.Universal.SpinOmega.Kernel
public import CFSG.LieType.Universal.SpinOmega.Products
public import CFSG.ClassicalGroups.Orthogonal.Derived
public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import CFSG.ClassicalGroups.Orthogonal.RootGroupStabilizerFour
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
public import CFSG.RankThree.OrthogonalInvolutions.Dickson
public import CFSG.RankThree.OrthogonalInvolutions.DicksonReflect
public import CFSG.RankThree.GF2n.Smith81.OrthE2Natural
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusFour
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesOrders
public import CFSG.Dihedral.GorensteinWalter.FieldTransport
public import CFSG.ClassicalGroups.SpecialLinear.InvariantForms
public import CFSG.ClassicalGroups.SpecialLinear.NaturalDualSum
public import CFSG.GroupTheory.HuppertProduct.Quotient
public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassical
public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalRows
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.SpTwo
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Glue
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294KDOutTwE6
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualFRHigher
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviGlue
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotUniqueGen
public import CFSG.RankThree.GF2n.Smith81.EStmt
public import CFSG.RankThree.GF2n.Smith81.OrthStmt
public import CFSG.RankThree.GF2n.Smith81.Sec2FStar
public import CFSG.RankThree.GF2n.Smith81.Sec2Stmt
public import CFSG.RankThree.GF2n.Smith81.TiLane
public import CFSG.RankThree.GF2n.Smith81.TiLemmaC
public import CFSG.RankThree.GF2n.Stroth80.Consumers
public import CFSG.RankThree.GF2n.Stroth80.Sec12CaseVIEquiv
public import CFSG.RankThree.GF2n.Stroth80.Sec12Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec310Main
public import CFSG.RankThree.GF2n.Stroth80.Sec45
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaPoints
public import CFSG.RankThree.GF2n.Stroth80.Sec6Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec7EndDefs
public import CFSG.RankThree.GF2n.Stroth80.Sec7OmegaSign
public import CFSG.RankThree.GF2n.SupIndepDecomp
public import CFSG.RankThree.GF2n.Tim79CentC
public import CFSG.RankThree.GF2n.Tim79CentL
public import CFSG.RankThree.GF2n.Tim79Mod
public import Certificates.Certificate9530

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)
open CFSG.Open
open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.OrthogonalInvolutions
open CFSG.Timmesfeld.RankTwo CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
open scoped commutatorElement

theorem irgOm2_card_omegaGroup
    {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card (omegaGroup (quadMinus 2 K b c)
      (nondegenerate_polarBilin_quadMinus_of_finite 2 K hirr)) =
      Nat.card K ^ 2 * (Nat.card K ^ 4 - 1) := by
  let Q := quadMinus 2 K b c
  let hQ := nondegenerate_polarBilin_quadMinus_of_finite 2 K hirr
  let O := TauCeti.QuadraticMap.orthogonalGroup Q
  let W := omegaGroup Q hQ
  have hWle : W ≤ O := omegaGroup_le Q hQ
  have hWcard : Nat.card W * 2 = Nat.card O := by
    have hcard := Subgroup.card_mul_index (W.subgroupOf O)
    rw [show (W.subgroupOf O).index = 2 from relIndex_omegaGroup Q hQ] at hcard
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWle).toEquiv] at hcard
  have hOcard : Nat.card O = 2 * Nat.card
      (CFSG.RankThree.Classical2.orthDerived Q) := by
    simpa [Q, O, CFSG.RankThree.Classical2.orthDerived] using
      CFSG.RankThree.GF2n.Smith81.card_orth_two_minus (K := K) (b := b) (c := c) hirr
  have hW_eq_derived : Nat.card W = Nat.card (CFSG.RankThree.Classical2.orthDerived Q) := by
    have := hWcard
    omega
  have hD_eq : CFSG.RankThree.Classical2.orthDerived Q = elementaryGroup Q := by
    simpa [Q] using
      commutator_orthogonalGroup_quadMinus_of_two_le (K := K) (n := 2) (le_refl 2) hirr
  have hS_eq : StatedOmega (StatedQuadMinus 2 K b c) =
      (elementaryGroup Q).map
        (toLinEquiv (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K).symm.toMonoidHom :=
    statedOmega_quadMinus_eq_map_of_two_le (n := 2) (le_refl 2) hirr
  have hS_card : Nat.card (StatedOmega (StatedQuadMinus 2 K b c)) =
      Nat.card (elementaryGroup Q) := by
    rw [hS_eq, Subgroup.card_map_of_injective (MulEquiv.injective _)]
  have hEcard : Nat.card (elementaryGroup Q) = Nat.card K ^ 2 * (Nat.card K ^ 4 - 1) := by
    rw [← hS_card, CFSG.SeitzReduction.F4Pilot.natCard_statedOmega_quadMinus_two hirr,
      CFSG.SeitzReduction.F4Pilot.ordSL_two]
    ring_nf
  rw [hW_eq_derived, hD_eq, hEcard]

theorem irgOm2_card_shortField
    {K : Type*} [Field K] [Finite K] {b c : K} :
    Nat.card (ShortField b c) = Nat.card K ^ 2 := by
  rw [Nat.card_congr (QuadraticAlgebra.equivProd (-c) b), Nat.card_prod, sq]

theorem irgOm2_card_sl2_shortField
    {K : Type} [Field K] [Finite K] {b c : K}
    [Fact (∀ r : K, r ^ 2 ≠ -c + b * r)] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ShortField b c)) =
      Nat.card K ^ 2 * (Nat.card K ^ 4 - 1) := by
  haveI : Finite (ShortField b c) := finite_shortField (K := K) (b := b) (c := c)
  rw [CFSG.RankThree.PartOne.KCOrthogonal.card_sl2, irgOm2_card_shortField]
  ring_nf


theorem irgOm2_shortPos_eq_minusXS
    {K : Type} [Field K] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (a : Fin 2 → K) :
    shortPosHom 2 hirr 0 (.ofAdd a) = minusXS 2 hirr (Pi.single 0 1) a := by
  rw [minusXS_eq hirr (0 : Fin 1) true (toStdB_single_of_not_lt' 2 (by decide))]
  rfl

theorem irgOm2_shortNeg_eq_minusXS
    {K : Type} [Field K] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (a : Fin 2 → K) :
    shortNegHom 2 hirr 0 (.ofAdd a) = minusXS 2 hirr (-Pi.single 0 1) a := by
  rw [minusXS_eq hirr (0 : Fin 1) false (toStdB_neg_single_of_not_lt' 2 (by decide))]
  rfl


theorem irgOm2_roots_two
    {K : Type} [Field K] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {β : Fin (2 - 1) → ℤ} :
    β ∈ (minusDatum 2 hirr).roots ↔
      β = Pi.single (0 : Fin (2 - 1)) 1 ∨
        β = -Pi.single (0 : Fin (2 - 1)) 1 := by
  rw [minusDatum_roots]
  constructor
  · intro hβ
    rcases exists_toStdB_eq_of_mem_roots (n := 2) hβ with
      ⟨i, j, hij, s, t, _⟩ | ⟨i, s, h⟩
    · exact absurd (Fin.ext (by omega)) hij
    · fin_cases i
      cases s
      · right
        have h1 : toStdB (2 - 1) β =
            toStdB (2 - 1) (-Pi.single (0 : Fin (2 - 1)) (1 : ℤ)) := by
          rw [h, toStdB_neg, toStdB_single_of_not_lt (n := 2 - 1) (k := 0) (by omega)]
          change (Pi.single (0 : Fin (2 - 1)) (-1 : ℤ) : Fin (2 - 1) → ℤ) =
            -Pi.single (0 : Fin (2 - 1)) (1 : ℤ)
          rw [show (-1 : ℤ) = -(1 : ℤ) by norm_num, Pi.single_neg]
        exact toStdB_injective (2 - 1) h1
      · left
        have h1 : toStdB (2 - 1) β =
            toStdB (2 - 1) (Pi.single (0 : Fin (2 - 1)) (1 : ℤ)) := by
          rw [h, toStdB_single_of_not_lt (n := 2 - 1) (k := 0) (by omega)]
          change (Pi.single (0 : Fin (2 - 1)) (1 : ℤ) : Fin (2 - 1) → ℤ) =
            Pi.single (0 : Fin (2 - 1)) (1 : ℤ)
          rfl
        exact toStdB_injective (2 - 1) h1
  · rintro (rfl | rfl)
    · exact mem_roots_of_toStdB_eq_short (n := 2) (i := 0) true (by
        rw [toStdB_single_of_not_lt' 2 (by decide)])
    · exact mem_roots_of_toStdB_eq_short (n := 2) (i := 0) false (by
        rw [toStdB_neg_single_of_not_lt' 2 (by decide)])

theorem irgOm2_rootGroup_card
    {K : Type} [Field K] [Finite K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {β : Fin (2 - 1) → ℤ}
    (hβ : β ∈ (minusDatum 2 hirr).roots) :
    Nat.card ((minusDatum 2 hirr).rootGroup β) = Nat.card K ^ 2 := by
  rcases (irgOm2_roots_two hirr).mp hβ with rfl | rfl
  · change Nat.card ↥(minusRootGroup 2 hirr (Pi.single (0 : Fin (2 - 1)) 1)) =
      Nat.card K ^ 2
    rw [minusRootGroup_single_of_not_lt (n := 2) (k := (0 : Fin (2 - 1))) hirr (by decide),
      ← twShortRoot_true]
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective
      (twShortRoot_injective 2 hirr 0 true), Subgroup.card_top]
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin]
  · change Nat.card ↥(minusRootGroup 2 hirr (-Pi.single (0 : Fin (2 - 1)) 1)) =
      Nat.card K ^ 2
    rw [minusRootGroup_neg_single_of_not_lt (n := 2) (k := (0 : Fin (2 - 1))) hirr (by decide),
      ← twShortRoot_false]
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective
      (twShortRoot_injective 2 hirr 0 false), Subgroup.card_top]
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin]

theorem irgOm2_short_inf
    {K : Type} [Field K] [Finite K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (shortPosHom 2 hirr 0).range ⊓ (shortNegHom 2 hirr 0).range = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxpos, hxneg⟩
  obtain ⟨p, hp⟩ := hxpos
  obtain ⟨q, hq⟩ := hxneg
  subst hp
  have hfix : spinAction (quadMinus 2 K b c) (shortPosHom 2 hirr 0 p)
      (fVec 2 (0 : Fin (2 - 1))) = fVec 2 (0 : Fin (2 - 1)) := by
    rw [← hq]
    exact spinAction_shortNegHom_fVec (n := 2) (i := 0) (a := q) (j := 0) hirr
  rw [show fVec 2 (0 : Fin (2 - 1)) = wVec 2 0 (0 : K) (0 : Fin 2 → K) (1 : K) by
      rw [wVec_fVec]] at hfix
  rw [show p = Multiplicative.ofAdd p.toAdd from (ofAdd_toAdd p).symm] at hfix
  rw [spinAction_shortPosHom_wVec (n := 2) (i := 0) (a := p.toAdd) (l := 0)
    (w := (0 : Fin 2 → K)) (m := 1) hirr] at hfix
  rw [wVec_eq_iff] at hfix
  have hp0 : p.toAdd = 0 := by
    simpa using hfix.2.1
  rw [show p = 1 by rw [← ofAdd_toAdd p, hp0, ofAdd_zero]]
  simp

theorem irgOm2_root_pair_eps
    {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card ((minusDatum 2 hirr).rootGroup (Pi.single (0 : Fin (2 - 1)) 1)) =
        Nat.card K ^ 2 ∧
      Nat.card ((minusDatum 2 hirr).rootGroup (-Pi.single (0 : Fin (2 - 1)) 1)) =
        Nat.card K ^ 2 ∧
        ((minusDatum 2 hirr).rootGroup (Pi.single (0 : Fin (2 - 1)) 1) ⊓
          (minusDatum 2 hirr).rootGroup (-Pi.single (0 : Fin (2 - 1)) 1)) = ⊥ := by
  have hε : Pi.single (0 : Fin (2 - 1)) (1 : ℤ) ∈ (minusDatum 2 hirr).roots :=
    (irgOm2_roots_two hirr).mpr (Or.inl rfl)
  have hneg : -Pi.single (0 : Fin (2 - 1)) (1 : ℤ) ∈ (minusDatum 2 hirr).roots :=
    (irgOm2_roots_two hirr).mpr (Or.inr rfl)
  refine ⟨irgOm2_rootGroup_card hirr hε, irgOm2_rootGroup_card hirr hneg, ?_⟩
  change minusRootGroup 2 hirr (Pi.single (0 : Fin (2 - 1)) 1) ⊓
    minusRootGroup 2 hirr (-Pi.single (0 : Fin (2 - 1)) 1) = ⊥
  rw [minusRootGroup_single_of_not_lt (n := 2) (k := (0 : Fin (2 - 1))) hirr (by decide),
    minusRootGroup_neg_single_of_not_lt (n := 2) (k := (0 : Fin (2 - 1))) hirr (by decide)]
  exact irgOm2_short_inf hirr

theorem irgOm2_root_pair
    {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {β : Fin (2 - 1) → ℤ}
    (hβ : β ∈ (minusDatum 2 hirr).roots) :
    Nat.card ((minusDatum 2 hirr).rootGroup β) = Nat.card K ^ 2 ∧
      Nat.card ((minusDatum 2 hirr).rootGroup (-β)) = Nat.card K ^ 2 ∧
        ((minusDatum 2 hirr).rootGroup β ⊓ (minusDatum 2 hirr).rootGroup (-β)) = ⊥ := by
  rcases (irgOm2_roots_two hirr).mp hβ with rfl | rfl
  · exact irgOm2_root_pair_eps hirr
  · have h := irgOm2_root_pair_eps (K := K) (b := b) (c := c) hirr
    rw [neg_neg]
    exact ⟨h.2.1, h.1, by rw [inf_comm]; exact h.2.2⟩

theorem irgOm2_rankOne_eq_top
    {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    [Fact (∀ r : K, r ^ 2 ≠ -c + b * r)]
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    rankOne (minusDatum 2 hirr).rootGroup (0 : Fin (2 - 1)) = ⊤ := by
  let Q := quadMinus 2 K b c
  let hQ := nondegenerate_polarBilin_quadMinus_of_finite 2 K hirr
  let L := rankOne (minusDatum 2 hirr).rootGroup (0 : Fin (2 - 1))
  have hLdef : L = (shortPosHom 2 hirr 0).range ⊔ (shortNegHom 2 hirr 0).range := by
    change rankOne (minusRootGroup 2 hirr) 0 = _
    exact rankOne_minusRootGroup_of_not_lt 2 hirr (k := 0) (by decide)
  haveI : Finite (spinGroup (quadMinus 2 K b c)) :=
    GGOppRadOmega.finite_spinGroup_quadMinus hirr
  haveI : Finite ↥L := Finite.of_injective (Subtype.val) Subtype.val_injective
  have hinj : Function.Injective (spinAction Q) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← ker_spinMatrix,
      ker_spinMatrix_quadMinus_eq_bot hirr CharTwo.two_eq_zero]
  have hLmap_le : L.map (spinAction Q) ≤ omegaGroup Q hQ := by
    rw [hLdef, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨p, rfl⟩ := hx
      have h1 : spinAction Q (shortPosHom 2 hirr 0 p) =
          eichler Q (minusVec 2 0 true) (planeVec 2 p.toAdd) := by
        rw [← twShortRoot_true]
        exact spinAction_twShortRoot_eq_eichler 2 hirr 0 true p.toAdd
      rw [h1]
      exact elementaryGroup_le_omegaGroup hQ (eichler_mem_elementaryGroup Q _ _)
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨p, rfl⟩ := hx
      have h1 : spinAction Q (shortNegHom 2 hirr 0 p) =
          eichler Q (minusVec 2 0 false) (planeVec 2 p.toAdd) := by
        rw [← twShortRoot_false]
        exact spinAction_twShortRoot_eq_eichler 2 hirr 0 false p.toAdd
      rw [h1]
      exact elementaryGroup_le_omegaGroup hQ (eichler_mem_elementaryGroup Q _ _)
  obtain ⟨φ, hφinj, hφU, hφL⟩ :=
    exists_sl2_minusXS (n := 2) (hirr := hirr) (k := (0 : Fin 1)) (by norm_num)
  have hφ_range_le_L : φ.range ≤ L := by
    rw [MonoidHom.range_eq_map,
      ← CFSG.StandardType.RankOneXfer.closure_sl2Upper_sl2Lower_eq_top (k := ShortField b c),
      MonoidHom.map_closure]
    rw [Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    rw [hLdef]
    rcases hg with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · rw [hφU a]
      refine Subgroup.mem_sup_left ?_
      rw [← minusRootGroup_single_of_not_lt (n := 2) (k := (0 : Fin 1)) hirr (by decide)]
      exact minusXS_mem hirr (minusShort_single (n := 2) (k := (0 : Fin 1)) (by norm_num)) _
    · rw [hφL a]
      refine Subgroup.mem_sup_right ?_
      rw [← minusRootGroup_neg_single_of_not_lt (n := 2) (k := (0 : Fin 1)) hirr (by decide)]
      exact minusXS_mem hirr (minusShort_neg_single (n := 2) (k := (0 : Fin 1)) (by norm_num)) _
  have hcard_phi_le : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ShortField b c)) ≤
      Nat.card L := by
    refine Nat.card_le_card_of_injective
      (fun x => (⟨φ x, hφ_range_le_L ⟨x, rfl⟩⟩ : L)) ?_
    intro x y hxy
    exact hφinj (Subtype.ext_iff.mp hxy)
  have hcardL_ge : Nat.card K ^ 2 * (Nat.card K ^ 4 - 1) ≤ Nat.card L := by
    rw [← irgOm2_card_sl2_shortField (K := K) (b := b) (c := c)]
    exact hcard_phi_le
  have hcardL_le : Nat.card L ≤ Nat.card K ^ 2 * (Nat.card K ^ 4 - 1) := by
    calc Nat.card L = Nat.card (L.map (spinAction Q)) :=
          (Subgroup.card_map_of_injective hinj).symm
      _ ≤ Nat.card (omegaGroup Q hQ) :=
          Nat.card_le_card_of_injective (Subgroup.inclusion hLmap_le)
            (Subgroup.inclusion_injective hLmap_le)
      _ = Nat.card K ^ 2 * (Nat.card K ^ 4 - 1) :=
          irgOm2_card_omegaGroup (K := K) (b := b) (c := c) hirr
  have hcardL : Nat.card L = Nat.card K ^ 2 * (Nat.card K ^ 4 - 1) :=
    le_antisymm hcardL_le hcardL_ge
  have hmap_eq : L.map (spinAction Q) = omegaGroup Q hQ := by
    refine Subgroup.eq_of_le_of_card_ge hLmap_le ?_
    rw [Subgroup.card_map_of_injective hinj, hcardL,
      irgOm2_card_omegaGroup (K := K) (b := b) (c := c) hirr]
  have hspin_le_omega : (spinAction Q).range ≤ omegaGroup Q hQ := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨l, hl, hev, -, hx⟩ := exists_list_of_spinGroup x
    rw [hx]
    exact prod_reflect_mem_omegaGroup Q hQ l hl hev
  have hrange_eq : (spinAction Q).range = L.map (spinAction Q) := by
    refine le_antisymm ?_ (Subgroup.map_le_range _ _)
    rw [hmap_eq]
    exact hspin_le_omega
  have hmap_top : L.map (spinAction Q) =
      (⊤ : Subgroup (spinGroup Q)).map (spinAction Q) := by
    rw [← MonoidHom.range_eq_map, hrange_eq]
  exact Subgroup.map_injective hinj hmap_top

theorem irgOm2_exists_spinEquivSL2
    {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    [Fact (∀ r : K, r ^ 2 ≠ -c + b * r)]
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nonempty (spinGroup (quadMinus 2 K b c) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ShortField b c)) := by
  let L := rankOne (minusDatum 2 hirr).rootGroup (0 : Fin (2 - 1))
  have hLtop : L = ⊤ := irgOm2_rankOne_eq_top hirr
  obtain ⟨φ, hφinj, hφU, hφL⟩ :=
    exists_sl2_minusXS (n := 2) (hirr := hirr) (k := (0 : Fin 1)) (by norm_num)
  have hφ_range_le_L : φ.range ≤ L := by
    let Q := quadMinus 2 K b c
    have hLdef : L = (shortPosHom 2 hirr 0).range ⊔ (shortNegHom 2 hirr 0).range := by
      change rankOne (minusRootGroup 2 hirr) 0 = _
      exact rankOne_minusRootGroup_of_not_lt 2 hirr (k := 0) (by decide)
    rw [MonoidHom.range_eq_map,
      ← CFSG.StandardType.RankOneXfer.closure_sl2Upper_sl2Lower_eq_top (k := ShortField b c),
      MonoidHom.map_closure]
    rw [Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    rw [hLdef]
    rcases hg with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · rw [hφU a]
      refine Subgroup.mem_sup_left ?_
      rw [← minusRootGroup_single_of_not_lt (n := 2) (k := (0 : Fin 1)) hirr (by decide)]
      exact minusXS_mem hirr (minusShort_single (n := 2) (k := (0 : Fin 1)) (by norm_num)) _
    · rw [hφL a]
      refine Subgroup.mem_sup_right ?_
      rw [← minusRootGroup_neg_single_of_not_lt (n := 2) (k := (0 : Fin 1)) hirr (by decide)]
      exact minusXS_mem hirr (minusShort_neg_single (n := 2) (k := (0 : Fin 1)) (by norm_num)) _
  have hL_le_phi : L ≤ φ.range := by
    let Q := quadMinus 2 K b c
    have hLdef : L = (shortPosHom 2 hirr 0).range ⊔ (shortNegHom 2 hirr 0).range := by
      change rankOne (minusRootGroup 2 hirr) 0 = _
      exact rankOne_minusRootGroup_of_not_lt 2 hirr (k := 0) (by decide)
    rw [hLdef]
    refine sup_le ?_ ?_
    · rintro _ ⟨p, rfl⟩
      obtain ⟨a, hpa⟩ := exists_fieldCoord_eq (b := b) (c := c) p.toAdd
      have hp : p = Multiplicative.ofAdd (fieldCoord a) := by rw [hpa, ofAdd_toAdd]
      rw [hp, irgOm2_shortPos_eq_minusXS hirr (fieldCoord a), ← hφU a]
      exact ⟨sl2Upper a, rfl⟩
    · rintro _ ⟨p, rfl⟩
      obtain ⟨a, hpa⟩ := exists_starCoord_eq (b := b) (c := c) p.toAdd
      have hp : p = Multiplicative.ofAdd (starCoord a) := by rw [hpa, ofAdd_toAdd]
      rw [hp, irgOm2_shortNeg_eq_minusXS hirr (starCoord a), ← hφL a]
      exact ⟨sl2Lower a, rfl⟩
  have hsurj : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hLtop]
    exact hL_le_phi
  exact ⟨(MulEquiv.ofBijective φ ⟨hφinj, hsurj⟩).symm⟩

end CFSG.StandardType.RCKRP
