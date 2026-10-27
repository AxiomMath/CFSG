module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenLongCentralizer
public import CFSG.RankThree.GF2n.Smith81.LinSmallG2
public import CFSG.Timmesfeld.RootSubgroupBasic
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenInvolutions
import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
import CFSG.LocalAnalysis.EvenBN.G2.Data
public import CFSG.Assembly.QuasithinDefs
public import CFSG.CGT.Timmesfeld75.Forms
public import CFSG.ClassicalGroups.SpecialLinear.InvariantForms
public import CFSG.ClassicalGroups.SpecialLinear.NaturalDualSum
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.Uniqueness.Bender.OddCentralizer
public import CFSG.GH74.Uniqueness.Bender.Unitary
public import CFSG.GroupTheory.HuppertProduct.Quotient
public import CFSG.GroupTheory.ThompsonIndexTwo
public import CFSG.LargeExtraspecial.S8CorBStatement
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderUnitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Monster.Code.Weights
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.Module
public import CFSG.RankThree.GF2n.Smith81.InspKFacts
public import CFSG.RankThree.GF2n.Smith81.LinOddBasic
public import CFSG.RankThree.GF2n.Smith81.LinRank
public import CFSG.RankThree.GF2n.Smith81.Sec220Defs
public import CFSG.RankThree.GF2n.Smith81.Sec2FStar
public import CFSG.RankThree.GF2n.Smith81.Sec2Stmt
public import CFSG.RankThree.GF2n.Stroth80.Consumers
public import CFSG.RankThree.GF2n.Stroth80.GlobalModel
public import CFSG.RankThree.GF2n.Stroth80.Sec3Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec5Comm
public import CFSG.RankThree.GF2n.SupIndepDecomp
public import CFSG.RankThree.GF2n.Tim79CentC
public import CFSG.RankThree.GF2n.Tim79CentL
public import CFSG.RankThree.GF2n.Tim79Mod
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Defs
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Th.Max3.Involutions
public import Certificates.Certificate10089Base
public import Certificates.Certificate10091Base

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.KG2

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Timmesfeld
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.SeitzReduction.F4Pilot (ordSL)
open scoped Pointwise

@[expose] def longRootElt (K : Type) [Field K] :
    ↥(adjointGroup .G2 K) :=
  ⟨pinnedX .G2 K g2c 1, pinnedX_mem_adjointGroup g2c 1⟩

variable {K : Type} [Field K] [Finite K] [CharP K 2]

local notation "X" => pinnedX Tag.G2 K

theorem coe_longRootElt : (longRootElt K : ModGL .G2 K) = X g2c 1 := rfl

theorem longRootElt_ne_one : longRootElt K ≠ 1 := by
  intro h
  have h1 : X g2c (1 : K) = X g2c 0 := by
    rw [pinnedX_zero]
    exact congrArg Subtype.val h
  exact one_ne_zero (pinnedX_injective .G2 K g2c h1)

@[expose] def uElt : ModGL .G2 K := g2N 0 0 1 0 0 0

@[expose] def vElt : ModGL .G2 K := g2N 0 0 0 1 0 0

@[expose] def xElt : ModGL .G2 K := uElt * vElt

theorem uElt_eq_pinnedX : uElt (K := K) = X g2u 1 := (pinnedX_u_eq_g2N 1).symm

theorem vElt_eq_pinnedX : vElt (K := K) = X g2v 1 := (pinnedX_v_eq_g2N 1).symm

theorem uElt_mem : uElt (K := K) ∈ adjointGroup .G2 K := by
  rw [uElt_eq_pinnedX]
  exact pinnedX_mem_adjointGroup _ _

theorem vElt_mem : vElt (K := K) ∈ adjointGroup .G2 K := by
  rw [vElt_eq_pinnedX]
  exact pinnedX_mem_adjointGroup _ _

theorem xElt_eq : xElt (K := K) = g2N 0 0 1 1 0 0 := by
  rw [xElt, uElt, vElt, g2N_zero_mul_g2N_zero]
  refine g2N_eq_g2N rfl (by ring) (by ring) (by ring) (by ring) (by ring)

theorem xElt_sq : xElt (K := K) * xElt = (longRootElt K : ModGL .G2 K) := by
  rw [xElt_eq, g2N_zero_mul_g2N_zero, coe_longRootElt, pinnedX_c_eq_g2N]
  refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> char2_ring

theorem xElt_pow_four : xElt (K := K) ^ 4 = 1 := by
  have h : xElt (K := K) ^ 4 = (xElt * xElt) * (xElt * xElt) := by
    rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, pow_two]
  rw [h, xElt_sq, coe_longRootElt, pinnedX_mul_self]

theorem orderOf_xElt : orderOf (xElt (K := K)) = 4 := by
  have h2 : xElt (K := K) ^ 2 ≠ 1 := by
    rw [pow_two, xElt_sq]
    exact fun h => longRootElt_ne_one (K := K) (Subtype.ext h)
  have hfin : xElt (K := K) ^ 2 ^ (1 + 1) = 1 := by
    rw [show 2 ^ (1 + 1) = 4 by norm_num]
    exact xElt_pow_four
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := xElt (K := K)) (by simpa using h2)
    hfin
  simpa using h

@[expose] def uY : ↥(adjointGroup .G2 K) := ⟨uElt, uElt_mem⟩

@[expose] def vY : ↥(adjointGroup .G2 K) := ⟨vElt, vElt_mem⟩

@[expose] def xY : ↥(adjointGroup .G2 K) := uY * vY

theorem coe_uY : (uY (K := K) : ModGL .G2 K) = uElt := rfl

theorem coe_vY : (vY (K := K) : ModGL .G2 K) = vElt := rfl

theorem coe_xY : (xY (K := K) : ModGL .G2 K) = xElt := rfl

theorem xY_sq : xY (K := K) * xY = longRootElt K := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, coe_xY, xElt_sq]

theorem orderOf_xY : orderOf (xY (K := K)) = 4 := by
  rw [← Subgroup.orderOf_coe (xY (K := K)), coe_xY, orderOf_xElt]

theorem weylElt_conj_uElt :
    weylElt .G2 K g2ir 1 * uElt * (weylElt .G2 K g2ir 1)⁻¹ = vElt (K := K) := by
  rw [uElt, vElt, weylElt_r_conj_g2N]
  refine g2N_eq_g2N rfl (by ring) (by ring) (by ring) (by ring) (by ring)

theorem isConj_uY_vY : IsConj (uY (K := K)) (vY (K := K)) := by
  refine isConj_iff.mpr ⟨⟨weylElt .G2 K g2ir 1, weylElt_mem_adjointGroup g2ir 1⟩, ?_⟩
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_uY, coe_vY]
  exact weylElt_conj_uElt

theorem vY_eq_rootC : vY (K := K) =
    ⟨X g2v 1, pinnedX_mem_adjointGroup g2v 1⟩ :=
  Subtype.ext vElt_eq_pinnedX

theorem isConj_longRootElt_of_mulEquiv {Y : Type} [Group Y]
    (e : Y ≃* ↥(adjointGroup .G2 K)) {D : Set Y}
    (hcls : ∃ d₀ : Y, D = {g | IsConj d₀ g})
    (hroot : IsRootInvolutionSet D) {d : Y} (hd : d ∈ D) :
    IsConj (e d) (longRootElt K) := by
  obtain ⟨d₀, rfl⟩ := hcls
  have hd' : IsConj d₀ d := hd
  have hz : orderOf (e d) = 2 := by
    rw [MulEquiv.orderOf_eq, hroot.1 d hd]
  rcases even_G2_involutions_conjugate_to_root_elements (K := K)
    (ringChar.eq_iff.2 (inferInstance : CharP K 2)) (e d) hz with h | h
  · exact h
  · rw [← vY_eq_rootC] at h
    have hvd : IsConj d (e.symm (vY (K := K))) := by
      obtain ⟨g, hg⟩ := isConj_iff.mp h
      refine isConj_iff.mpr ⟨e.symm g, ?_⟩
      have := congrArg e.symm hg
      simpa using this
    have hvD : e.symm (vY (K := K)) ∈ {g : Y | IsConj d₀ g} := hd'.trans hvd
    have huv : IsConj (e.symm (uY (K := K))) (e.symm (vY (K := K))) := by
      obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_uY_vY (K := K))
      refine isConj_iff.mpr ⟨e.symm g, ?_⟩
      have := congrArg e.symm hg
      simpa using this
    have huD : e.symm (uY (K := K)) ∈ {g : Y | IsConj d₀ g} :=
      hd'.trans (hvd.trans huv.symm)
    have h4 : orderOf (e.symm (uY (K := K)) * e.symm (vY (K := K))) = 4 := by
      rw [← map_mul, MulEquiv.orderOf_eq]
      exact orderOf_xY
    have hsqD : (e.symm (uY (K := K)) * e.symm (vY (K := K))) ^ 2 ∈
        {g : Y | IsConj d₀ g} := hroot.2.2 _ huD _ hvD h4
    have heq : (e.symm (uY (K := K)) * e.symm (vY (K := K))) ^ 2 =
        e.symm (longRootElt K) := by
      have h : (uY (K := K) * vY (K := K)) ^ 2 = longRootElt K := by
        rw [pow_two]
        exact xY_sq
      rw [← map_mul, ← map_pow, h]
    have heD : e.symm (longRootElt K) ∈ {g : Y | IsConj d₀ g} := heq ▸ hsqD
    have hlast : IsConj d (e.symm (longRootElt K)) :=
      isConj_of_isClass ⟨d₀, rfl⟩ hd heD
    obtain ⟨g, hg⟩ := isConj_iff.mp hlast
    refine isConj_iff.mpr ⟨e g, ?_⟩
    have := congrArg e hg
    simpa using this

theorem card_g2RankOne : Nat.card (g2RankOne K g2ir) = Nat.card (SL2 K) := by
  obtain ⟨ρ, -, -, -, -, hrange, hinj, -, -⟩ := g2_rank_one (K := K) g2ir
  let f : SL2 K → g2RankOne K g2ir := fun g =>
    ⟨ρ g, hrange ▸ MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro g g' h
      exact hinj (Subtype.ext_iff.mp h)
    · intro l
      have hl : (l : ModGL .G2 K) ∈ ρ.range := by
        rw [hrange]
        exact l.2
      obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hl
      exact ⟨g, Subtype.ext hg⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem exists_mul_of_mem_sup {g : ModGL .G2 K}
    (hg : g ∈ g2LongRadical K ⊔ g2RankOne K g2ir) :
    ∃ q ∈ g2LongRadical K, ∃ l ∈ g2RankOne K g2ir, g = q * l := by
  obtain ⟨-, -, -, hCeq, hset, -, -, -⟩ := even_G2_highest_long_root_centralizer K
  have hset' : ((g2LongRadical K ⊔ g2RankOne K g2ir : Subgroup (ModGL .G2 K)) :
      Set (ModGL .G2 K)) = (g2LongRadical K : Set (ModGL .G2 K)) *
        (g2RankOne K g2ir : Set (ModGL .G2 K)) := by
    rw [← hCeq]
    exact hset
  have : g ∈ (g2LongRadical K : Set (ModGL .G2 K)) *
      (g2RankOne K g2ir : Set (ModGL .G2 K)) := by
    rw [← hset']
    exact hg
  obtain ⟨q, hq, l, hl, hql⟩ := this
  exact ⟨q, hq, l, hl, hql.symm⟩

theorem card_sup_g2LongRadical_g2RankOne :
    Nat.card (g2LongRadical K ⊔ g2RankOne K g2ir : Subgroup (ModGL .G2 K)) =
      Nat.card (g2LongRadical K) * Nat.card (g2RankOne K g2ir) := by
  obtain ⟨-, -, -, hCeq, hset, hLnorm, hdisj, -⟩ :=
    even_G2_highest_long_root_centralizer K
  set Q := g2LongRadical K
  set L := g2RankOne K g2ir
  set M := Q ⊔ L
  have hset' : ((M : Subgroup (ModGL .G2 K)) : Set (ModGL .G2 K)) =
      (Q : Set (ModGL .G2 K)) * (L : Set (ModGL .G2 K)) := by
    rw [← hCeq]
    exact hset
  have hinf : Q.subgroupOf M ⊓ L.subgroupOf M = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_inf] at hy
    have hyQ : (y : ModGL .G2 K) ∈ Q := Subgroup.mem_subgroupOf.mp hy.1
    have hyL : (y : ModGL .G2 K) ∈ L := Subgroup.mem_subgroupOf.mp hy.2
    have hmem : (y : ModGL .G2 K) ∈ Q ⊓ L := Subgroup.mem_inf.mpr ⟨hyQ, hyL⟩
    rw [hdisj, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (Subtype.ext hmem)
  have hsup : Q.subgroupOf M ⊔ L.subgroupOf M = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (le_sup_left : Q ≤ M) (le_sup_right : L ≤ M)]
    exact Subgroup.subgroupOf_self M
  have hdisjD : Disjoint (Q.subgroupOf M) (L.subgroupOf M) := by
    rw [Subgroup.disjoint_def]
    intro y hyQ hyL
    have hmem : y ∈ Q.subgroupOf M ⊓ L.subgroupOf M := Subgroup.mem_inf.mpr ⟨hyQ, hyL⟩
    rw [hinf] at hmem
    simpa using hmem
  have hMul : (↑(Q.subgroupOf M) * ↑(L.subgroupOf M) : Set ↥M) = Set.univ := by
    ext y
    refine ⟨fun _ => Set.mem_univ _, fun _ => ?_⟩
    have hy : (y : ModGL .G2 K) ∈ (Q : Set (ModGL .G2 K)) * (L : Set (ModGL .G2 K)) := by
      rw [← hset']
      exact y.2
    obtain ⟨q, hq, l, hl, hql⟩ := hy
    have hq' : (⟨q, Subgroup.mem_sup_left hq⟩ : ↥M) ∈ Q.subgroupOf M :=
      Subgroup.mem_subgroupOf.mpr hq
    have hl' : (⟨l, Subgroup.mem_sup_right hl⟩ : ↥M) ∈ L.subgroupOf M :=
      Subgroup.mem_subgroupOf.mpr hl
    have heq : (⟨q, Subgroup.mem_sup_left hq⟩ : ↥M) * ⟨l, Subgroup.mem_sup_right hl⟩ = y :=
      Subtype.ext hql
    rw [← heq]
    exact Set.mul_mem_mul hq' hl'
  have hcompl : (Q.subgroupOf M).IsComplement' (L.subgroupOf M) :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisjD hMul
  have hQcard : Nat.card (Q.subgroupOf M) = Nat.card Q :=
    Nat.card_congr ((Subgroup.subgroupOfEquivOfLe (le_sup_left : Q ≤ M)).toEquiv)
  have hLcard : Nat.card (L.subgroupOf M) = Nat.card L :=
    Nat.card_congr ((Subgroup.subgroupOfEquivOfLe (le_sup_right : L ≤ M)).toEquiv)
  rw [← hQcard, ← hLcard]
  exact hcompl.card_mul.symm

theorem centralizer_map_subtype :
    (Subgroup.centralizer ({longRootElt K} : Set ↥(adjointGroup .G2 K))).map
        (adjointGroup .G2 K).subtype =
      adjointGroup .G2 K ⊓ Subgroup.centralizer {pinnedX .G2 K g2c 1} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
    change y ∈ Subgroup.centralizer {longRootElt K} at hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    exact congrArg Subtype.val hy
  · intro hx
    obtain ⟨hxC, hxcomm⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hxC⟩, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hxcomm ⊢
    exact Subtype.ext hxcomm

theorem centralizerY_eq_subgroupOf :
    (adjointGroup .G2 K ⊓ Subgroup.centralizer {pinnedX .G2 K g2c 1}).subgroupOf
        (adjointGroup .G2 K) =
      Subgroup.centralizer ({longRootElt K} : Set ↥(adjointGroup .G2 K)) := by
  ext y
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨-, hcomm⟩
    exact Subtype.ext hcomm
  · intro hcomm
    exact ⟨y.2, congrArg Subtype.val hcomm⟩

theorem card_centralizer_longRootElt :
    Nat.card (Subgroup.centralizer ({longRootElt K} : Set ↥(adjointGroup .G2 K))) =
      Nat.card K ^ 5 * Nat.card (SL2 K) := by
  obtain ⟨-, -, -, hCeq, -, -, -, -, -, -, -, -⟩ :=
    even_G2_highest_long_root_centralizer K
  calc
    Nat.card (Subgroup.centralizer ({longRootElt K} : Set ↥(adjointGroup .G2 K))) =
        Nat.card ((Subgroup.centralizer ({longRootElt K} :
          Set ↥(adjointGroup .G2 K))).map (adjointGroup .G2 K).subtype) :=
      (Subgroup.card_map_of_injective
        (Subgroup.subtype_injective (adjointGroup .G2 K))).symm
    _ = Nat.card (adjointGroup .G2 K ⊓
          Subgroup.centralizer {pinnedX .G2 K g2c 1} : Subgroup (ModGL .G2 K)) := by
      rw [centralizer_map_subtype]
    _ = Nat.card (g2LongRadical K ⊔ g2RankOne K g2ir : Subgroup (ModGL .G2 K)) := by
      rw [hCeq]
    _ = Nat.card (g2LongRadical K) * Nat.card (g2RankOne K g2ir) :=
      card_sup_g2LongRadical_g2RankOne
    _ = Nat.card K ^ 5 * Nat.card (SL2 K) := by
      rw [CFSG.LocalAnalysis.EvenBN.G2.Model.card_D, card_g2RankOne]

@[expose] def tElt : ModGL .G2 K := X g2r 1 * X g2nr 1

theorem tElt_mem : tElt (K := K) ∈ adjointGroup .G2 K :=
  mul_mem (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _)

theorem tElt_mem_g2RankOne : tElt (K := K) ∈ g2RankOne K g2ir := by
  rw [tElt, ← xUnit_g2ir (K := K) 1, ← yUnit_g2ir (K := K) 1]
  exact mul_mem (xUnit_mem_g2RankOne g2ir 1) (yUnit_mem_g2RankOne g2ir 1)

theorem commute_tElt_longRootElt : Commute (tElt (K := K)) (longRootElt K : ModGL .G2 K) := by
  rw [tElt, coe_longRootElt]
  exact commute_of_mem_g2RankOne_r tElt_mem_g2RankOne 1

theorem coe_uSL_mul_vSL :
    ((uSL (1 : K) * vSL 1 : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 1] := by
  apply Matrix.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;>
    simp [uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two] <;> char2_ring

theorem orderOf_uSL_mul_vSL : orderOf (uSL (1 : K) * vSL 1) = 3 := by
  have hA3mat : (((uSL (1 : K) * vSL 1 : SL2 K) : Matrix (Fin 2) (Fin 2) K)) ^ 3 = 1 := by
    rw [coe_uSL_mul_vSL]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_succ, pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
        char2_ring
  have hA3 : (uSL (1 : K) * vSL 1) ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    exact hA3mat
  have hAne : uSL (1 : K) * vSL 1 ≠ 1 := by
    intro h
    have h00 := congrArg (fun g : SL2 K => ((g : Matrix (Fin 2) (Fin 2) K) 0 0)) h
    rw [coe_uSL_mul_vSL, Matrix.SpecialLinearGroup.coe_one] at h00
    simpa using h00
  exact orderOf_eq_prime hA3 hAne

theorem orderOf_tElt : orderOf (tElt (K := K)) = 3 := by
  obtain ⟨ρ, hu, hv, -, -, -, hinj, -, -⟩ := g2_rank_one (K := K) g2ir
  have ht : tElt (K := K) = ρ (uSL 1 * vSL 1) := by
    rw [tElt, ← xUnit_g2ir (K := K) 1, ← yUnit_g2ir (K := K) 1, ← hu 1, ← hv 1,
      ← map_mul]
  rw [ht, orderOf_injective ρ hinj]
  exact orderOf_uSL_mul_vSL

theorem commute_pinnedX_c_of_mem_sup (c : K) {g : ModGL .G2 K}
    (hg : g ∈ g2LongRadical K ⊔ g2RankOne K g2ir) :
    Commute (X g2c c) g := by
  obtain ⟨q, hq, l, hl, rfl⟩ := exists_mul_of_mem_sup hg
  have hq' : Commute (X g2c c) q := by
    obtain ⟨B, C, D, E, F, rfl⟩ := hq
    exact commute_pinnedX_c_g2N c 0 B C D E F
  have hl' : Commute (X g2c c) l := (commute_of_mem_g2RankOne_r hl c).symm
  exact hq'.mul_right hl'

theorem xElt_mem_g2LongRadical : xElt (K := K) ∈ g2LongRadical K := by
  rw [xElt_eq]
  exact g2N_mem_g2LongRadical _ _ _ _ _

theorem g2LongRadical_le_pCoreOf_centralizer :
    g2LongRadical K ≤ CFSG.Open.pCoreOf 2
      (adjointGroup .G2 K ⊓ Subgroup.centralizer {pinnedX .G2 K g2c 1}) := by
  obtain ⟨-, hQle, hQp, hCeq, -, hLnorm, -, -⟩ :=
    even_G2_highest_long_root_centralizer K
  set Q := g2LongRadical K
  set L := g2RankOne K g2ir
  set Cz := adjointGroup .G2 K ⊓ Subgroup.centralizer {pinnedX .G2 K g2c 1}
  have hQCz : Q ≤ Cz := by
    intro q hq
    obtain ⟨B, C, D, E, F, rfl⟩ := hq
    refine Subgroup.mem_inf.mpr ⟨hQle (g2N_mem_g2LongRadical B C D E F), ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (commute_pinnedX_c_g2N 1 0 B C D E F).symm.eq
  have hCznorm : Cz ≤ Subgroup.normalizer (Q : Set (ModGL .G2 K)) := by
    rw [hCeq]
    exact sup_le Subgroup.le_normalizer hLnorm
  have hQnorm : (Q.subgroupOf Cz).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQCz).mpr hCznorm
  have hQp' : IsPGroup 2 (Q.subgroupOf Cz) :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQCz).symm
  have hleCore : Q.subgroupOf Cz ≤ CFSG.pCore 2 Cz := by
    rw [CFSG.pCore_eq_iSup]
    exact le_iSup_of_le (Q.subgroupOf Cz)
      (le_iSup_of_le hQnorm (le_iSup_of_le hQp' le_rfl))
  have hmap : Q ≤ (CFSG.pCore 2 Cz).map Cz.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hQCz]
    exact Subgroup.map_mono hleCore
  simpa only [CFSG.Open.pCoreOf] using hmap

theorem xY_mem_pCoreOf_centralizer :
    xY (K := K) ∈ CFSG.Open.pCoreOf 2
      (Subgroup.centralizer ({longRootElt K} : Set ↥(adjointGroup .G2 K))) := by
  have hQCz := g2LongRadical_le_pCoreOf_centralizer (K := K)
  have hxCz : xElt (K := K) ∈ CFSG.Open.pCoreOf 2
      (adjointGroup .G2 K ⊓ Subgroup.centralizer {pinnedX .G2 K g2c 1}) :=
    hQCz xElt_mem_g2LongRadical
  have hmapCore : (CFSG.Open.pCoreOf 2
        (Subgroup.centralizer ({longRootElt K} : Set ↥(adjointGroup .G2 K)))).map
        (adjointGroup .G2 K).subtype =
      CFSG.Open.pCoreOf 2
        (adjointGroup .G2 K ⊓ Subgroup.centralizer {pinnedX .G2 K g2c 1}) := by
    rw [← centralizerY_eq_subgroupOf]
    exact CFSG.ABGLocalTools.map_pCore_subgroupOf (p := 2)
      (M := adjointGroup .G2 K ⊓ Subgroup.centralizer {pinnedX .G2 K g2c 1})
      (H := adjointGroup .G2 K) inf_le_left
  have hmem : ((xY (K := K) : ↥(adjointGroup .G2 K)) : ModGL .G2 K) ∈
      (CFSG.Open.pCoreOf 2
        (Subgroup.centralizer ({longRootElt K} : Set ↥(adjointGroup .G2 K)))).map
        (adjointGroup .G2 K).subtype := by
    rw [hmapCore]
    exact hxCz
  obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.mp hmem
  have : u = xY (K := K) := Subtype.ext hux
  rwa [this] at hu

theorem isConj_longRootElt_rootC {c : K} (hc : c ≠ 0) :
    IsConj (longRootElt K) ⟨X g2c c, pinnedX_mem_adjointGroup g2c c⟩ := by
  obtain ⟨g, hgC, hg⟩ := G2Conj.c_one hc
  refine isConj_iff.mpr ⟨⟨g⁻¹, inv_mem hgC⟩, ?_⟩
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_longRootElt, inv_inv]
  have h2 : g⁻¹ * X g2c 1 * g = X g2c c := by
    rw [← hg]
    group
  exact h2

theorem rootSubgroup_subgroupOf_le_rootGroup :
    (rootSubgroup .G2 K g2c).subgroupOf (adjointGroup .G2 K) ≤
      rootGroup {g : ↥(adjointGroup .G2 K) | IsConj (longRootElt K) g}
        (longRootElt K) := by
  intro y hy
  obtain ⟨c, hc⟩ := (mem_rootSubgroup (τ := .G2) (R := K)).mp (Subgroup.mem_subgroupOf.mp hy)
  by_cases hc0 : c = 0
  · have hy1 : y = 1 := Subtype.ext (by rw [← hc, hc0, pinnedX_zero]; rfl)
    rw [hy1]
    exact Subgroup.one_mem _
  · obtain ⟨-, -, -, hCeq, -, -, -, -, -, -, -⟩ :=
      even_G2_highest_long_root_centralizer K
    have hyy' : y = ⟨X g2c c, pinnedX_mem_adjointGroup g2c c⟩ := Subtype.ext hc.symm
    rw [hyy']
    refine Subgroup.subset_closure ?_
    rw [mem_rootSet_iff ⟨longRootElt K, rfl⟩ (IsConj.refl (longRootElt K))]
    refine ⟨isConj_longRootElt_rootC hc0, ?_, ?_⟩
    · apply Subtype.ext
      change X g2c 1 * X g2c c = X g2c c * X g2c 1
      rw [← pinnedX_add, ← pinnedX_add, add_comm]
    · intro f hfD hzf
      have hzf' : (X g2c 1) * (f : ModGL .G2 K) =
          (f : ModGL .G2 K) * X g2c 1 := by
        have := congrArg Subtype.val hzf.eq
        simpa [coe_longRootElt] using this
      have hfCz : (f : ModGL .G2 K) ∈
          adjointGroup .G2 K ⊓ Subgroup.centralizer {pinnedX .G2 K g2c 1} :=
        Subgroup.mem_inf.mpr ⟨f.2,
          Subgroup.mem_centralizer_singleton_iff.mpr hzf'.symm⟩
      have hfsup : (f : ModGL .G2 K) ∈ g2LongRadical K ⊔ g2RankOne K g2ir := by
        rw [← hCeq]
        exact hfCz
      have hcomm := commute_pinnedX_c_of_mem_sup c hfsup
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact hcomm.eq

theorem rootGroup_longRootElt_eq {n : ℕ} (hK : Nat.card K = n)
    (hroot : Nat.card (rootGroup {g : ↥(adjointGroup .G2 K) | IsConj (longRootElt K) g}
      (longRootElt K)) = n) :
    rootGroup {g : ↥(adjointGroup .G2 K) | IsConj (longRootElt K) g} (longRootElt K) =
      (rootSubgroup .G2 K g2c).subgroupOf (adjointGroup .G2 K) := by
  have hXD : Nat.card ((rootSubgroup .G2 K g2c).subgroupOf (adjointGroup .G2 K)) =
      Nat.card K := by
    calc Nat.card ((rootSubgroup .G2 K g2c).subgroupOf (adjointGroup .G2 K)) =
          Nat.card (rootSubgroup .G2 K g2c) :=
        Nat.card_congr ((Subgroup.subgroupOfEquivOfLe
          (rootSubgroup_le_adjointGroup g2c)).toEquiv)
      _ = Nat.card K := card_rootSubgroup (τ := .G2) (α := g2c)
  have hcard : Nat.card (rootGroup {g : ↥(adjointGroup .G2 K) |
      IsConj (longRootElt K) g} (longRootElt K)) ≤
      Nat.card ((rootSubgroup .G2 K g2c).subgroupOf (adjointGroup .G2 K)) := by
    rw [hroot, hXD, hK]
  exact (Subgroup.eq_of_le_of_card_ge rootSubgroup_subgroupOf_le_rootGroup hcard).symm

theorem xElt_not_mem_rootSubgroup : xElt (K := K) ∉ rootSubgroup .G2 K g2c := by
  intro hx
  obtain ⟨c, hc⟩ := (mem_rootSubgroup (τ := .G2) (R := K)).mp hx
  rw [pinnedX_c_eq_g2N, xElt_eq] at hc
  obtain ⟨-, -, hC, -, -, -⟩ := g2N_injective hc
  exact one_ne_zero hC.symm

theorem xY_not_mem_rootGroup
    (hrootEq : rootGroup {g : ↥(adjointGroup .G2 K) | IsConj (longRootElt K) g}
      (longRootElt K) = (rootSubgroup .G2 K g2c).subgroupOf (adjointGroup .G2 K)) :
    xY (K := K) ∉ rootGroup {g : ↥(adjointGroup .G2 K) | IsConj (longRootElt K) g}
      (longRootElt K) := by
  rw [hrootEq]
  intro hx
  exact xElt_not_mem_rootSubgroup (by
    simpa [coe_xY] using Subgroup.mem_subgroupOf.mp hx)

theorem radAction_t_fixes_x :
    ((radMr (1 : K) ∘ₗ (radSwap ∘ₗ radMr (1 : K) ∘ₗ radSwap)) ![0, 1, 1, 0]) =
      ![0, 1, 1, 0] := by
  funext i
  fin_cases i <;> simp [radMr, radSwap] <;> char2_ring

theorem commutator_tElt_xElt_mem_rootSubgroup :
    tElt (K := K) * xElt * (tElt (K := K))⁻¹ * (xElt (K := K))⁻¹ ∈
      rootSubgroup .G2 K g2c := by
  have hact : ActsOnRadical (tElt (K := K))
      (radMr (1 : K) ∘ₗ (radSwap ∘ₗ radMr (1 : K) ∘ₗ radSwap)) := by
    rw [tElt]
    exact (actsOnRadical_pinnedX_r (1 : K)).mul (actsOnRadical_pinnedX_nr (1 : K))
  obtain ⟨F', hF'⟩ := hact.2 ![0, 1, 1, 0] 0
  rw [radAction_t_fixes_x] at hF'
  have hxinv : (xElt (K := K))⁻¹ = g2N 0 0 1 1 0 1 := by
    rw [xElt_eq, g2N_zero_inv]
    exact g2N_eq_g2N rfl rfl rfl rfl rfl (by ring)
  simp at hF'
  rw [hxinv, xElt_eq, hF', g2N_zero_mul_g2N_zero]
  refine (mem_rootSubgroup (τ := .G2) (R := K)).mpr ⟨F', ?_⟩
  rw [pinnedX_c_eq_g2N]
  exact g2N_eq_g2N rfl (by char2_ring) (by char2_ring) (by char2_ring) (by char2_ring)
    (by char2_ring)

@[expose] def tY : ↥(adjointGroup .G2 K) := ⟨tElt, tElt_mem⟩

theorem coe_tY : (tY (K := K) : ModGL .G2 K) = tElt := rfl

theorem tY_mem_centralizer :
    tY (K := K) ∈ Subgroup.centralizer
      ({longRootElt K} : Set ↥(adjointGroup .G2 K)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_tY, coe_longRootElt]
  exact commute_tElt_longRootElt.eq

theorem orderOf_tY : orderOf (tY (K := K)) = 3 := by
  rw [← Subgroup.orderOf_coe (tY (K := K)), coe_tY, orderOf_tElt]

theorem commutator_tY_xY_mem_rootGroup
    (hrootEq : rootGroup {g : ↥(adjointGroup .G2 K) | IsConj (longRootElt K) g}
      (longRootElt K) = (rootSubgroup .G2 K g2c).subgroupOf (adjointGroup .G2 K)) :
    tY (K := K) * xY * (tY (K := K))⁻¹ * (xY (K := K))⁻¹ ∈
      rootGroup {g : ↥(adjointGroup .G2 K) | IsConj (longRootElt K) g}
        (longRootElt K) := by
  rw [hrootEq, Subgroup.mem_subgroupOf]
  have h : ((tY (K := K) * xY * (tY (K := K))⁻¹ * (xY (K := K))⁻¹ :
      ↥(adjointGroup .G2 K)) : ModGL .G2 K) =
      tElt * xElt * (tElt (K := K))⁻¹ * (xElt (K := K))⁻¹ := by
    simp [Subgroup.coe_mul, Subgroup.coe_inv, coe_tY, coe_xY]
  rw [h]
  exact commutator_tElt_xElt_mem_rootSubgroup

theorem kG2Concl_longRootElt {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hroot : Nat.card (rootGroup {g : ↥(adjointGroup .G2 K) | IsConj (longRootElt K) g}
      (longRootElt K)) = 2 ^ f) :
    CFSG.RankThree.GF2n.Smith81.Insp.KG2Concl
      {g : ↥(adjointGroup .G2 K) | IsConj (longRootElt K) g} f (longRootElt K) := by
  have hSLK : Nat.card (SL2 K) = ordSL 2 (Nat.card K) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (n := 2) (by norm_num)]
    rfl
  have hcard : Nat.card (Subgroup.centralizer
      ({longRootElt K} : Set ↥(adjointGroup .G2 K))) =
      (2 ^ f) ^ 5 * ordSL 2 (2 ^ f) := by
    rw [card_centralizer_longRootElt, hK, hSLK, hK]
  have hrootEq := rootGroup_longRootElt_eq (n := 2 ^ f) hK hroot
  refine ⟨?_, tY, tY_mem_centralizer, orderOf_tY, xY, xY_mem_pCoreOf_centralizer, ?_, ?_⟩
  · rw [hcard]
  · exact xY_not_mem_rootGroup hrootEq
  · exact commutator_tY_xY_mem_rootGroup hrootEq

end CFSG.RankThree.GF2n.Smith81.KG2
