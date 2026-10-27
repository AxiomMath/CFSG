module

public import CFSG.Monster.B.CTIB.FourClasses
public import CFSG.Monster.B.CTIB.Component
public import CFSG.Monster.B.E6.StandardSimple
public import CFSG.Monster.B.TwoA.Amalgam.DerivedCoverMain
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3011
public import Certificates.Certificate3012
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3041
public import Certificates.Certificate3042
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3054
public import Certificates.Certificate3055
public import Certificates.Certificate3056
public import Certificates.Certificate3057
public import Certificates.Certificate3058
public import Certificates.Certificate3060
public import Certificates.Certificate3061
public import Certificates.Certificate3062
public import Certificates.Certificate3063
public import Certificates.Certificate3072
public import Certificates.Certificate3073
public import Certificates.Certificate3074
public import Certificates.Certificate3075
public import Certificates.Certificate3076
public import Certificates.Certificate3077
public import Certificates.Certificate3078
public import Certificates.Certificate3098
public import Certificates.Certificate3099
public import Certificates.Certificate3100
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3110
public import Certificates.Certificate3111
public import Certificates.Certificate3114
public import Certificates.Certificate3115
public import Certificates.Certificate3116
public import Certificates.Certificate3117
public import Certificates.Certificate3118
public import Certificates.Certificate3175
public import Certificates.Certificate16001
public import Certificates.Certificate16015
public import Certificates.Certificate16016
public import Certificates.Certificate16021
public import Certificates.Certificate16022
public import Certificates.Certificate16028
public import Certificates.Certificate16033
public import Certificates.Certificate16035
public import Certificates.Certificate16040
public import Certificates.Certificate3027
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate16951
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.C2E6D4NaturalOrthogonal
public import CFSG.LieType.Chevalley.C2E6ExactRootRestrictions
public import CFSG.LieType.Chevalley.C2E6FieldExtensionResidueActions
public import CFSG.LieType.Chevalley.C2E6FirstResidueUnitarySix
public import CFSG.LieType.Chevalley.C2E6FourthResidueMinusEight
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Steinberg.G2
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointIsometryPoints
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailPolar
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Monster.B.E6.StdF4Root
public import CFSG.Monster.B.TwoA.Amalgam.StdIso
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open MulOpposite CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.Bin Native Matrix
  CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.TwoA.Amalgam
  CFSG.LieType.Chevalley.C2E6Std
open CFSG.Sporadic.Co2Inv (co2_involution_input)

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

@[expose] def CentralizerInput :
    Prop :=
  ∀ (v : CVert) (s : Shat), (s : Dfull) * clabel v = clabel v * s ↔ cvMul v s = v

theorem derivedCoverInput_holds :
    (commutator Eam).index = 2 ∧ Group.IsPerfect (commutator Eam) ∧
      Subgroup.center Eam = Subgroup.zpowers cE' ∧
      (Subgroup.center (commutator Eam)).map (commutator Eam).subtype = Subgroup.zpowers cE' ∧
      Nat.card (Subgroup.zpowers cE') = 2 ∧
      Nonempty (commutator Eam ⧸ (Subgroup.zpowers cE').subgroupOf (commutator Eam) ≃*
        stdGroup) ∧
      (¬ ∃ L : Subgroup Eam, L ≤ commutator Eam ∧ Subgroup.zpowers cE' ⊓ L = ⊥ ∧
        Subgroup.zpowers cE' ⊔ L = commutator Eam) ∧
      Nat.card (commutator Eam) = 153064959367549707878400 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, -, -⟩ := short_F4_derived_standard_perfect_cover
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

@[expose] noncomputable def centralizerEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (a : G) : Subgroup.centralizer {a} ≃* Subgroup.centralizer {e a} where
  toFun x := ⟨e x.1, Subgroup.mem_centralizer_singleton_iff.2 (by
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 x.2])⟩
  invFun y := ⟨e.symm y.1, Subgroup.mem_centralizer_singleton_iff.2 (by
    have h := Subgroup.mem_centralizer_singleton_iff.1 y.2
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, h])⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.1)
  right_inv y := Subtype.ext (e.apply_symm_apply y.1)
  map_mul' x y := Subtype.ext (map_mul e x.1 y.1)

theorem centralizer_inv {G : Type*} [Group G] (a : G) :
    Subgroup.centralizer {a⁻¹} = Subgroup.centralizer {a} := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc x * a = a * (a⁻¹ * x) * a := by group
      _ = a * (x * a⁻¹) * a := by rw [h]
      _ = a * x := by group
  · intro h
    calc x * a⁻¹ = a⁻¹ * (a * x) * a⁻¹ := by group
      _ = a⁻¹ * (x * a) * a⁻¹ := by rw [h]
      _ = a⁻¹ * x := by group

@[expose] noncomputable def sHom : Sbp →* Shat where
  toFun u := (toShat u)⁻¹
  map_one' := by
    apply Subtype.ext
    show (iotaD (1 : Sbp).unop)⁻¹ = 1
    rw [unop_one, map_one, inv_one]
  map_mul' u v := by
    apply Subtype.ext
    show (iotaD (u * v).unop)⁻¹ = (iotaD u.unop)⁻¹ * (iotaD v.unop)⁻¹
    rw [unop_mul, map_mul, _root_.mul_inv_rev]

theorem sHom_bijective : Function.Bijective sHom := by
  constructor
  · intro u v h
    have h' : iotaD u.unop = iotaD v.unop := by
      have := congrArg (fun x : Shat => ((x⁻¹ : Shat) : Dfull)) h
      simpa [sHom, toShat] using this
    exact unop_injective (iotaD_injective h')
  · intro y
    obtain ⟨c, hc⟩ := y.2
    refine ⟨op c⁻¹, Subtype.ext ?_⟩
    show (iotaD (op c⁻¹).unop)⁻¹ = (y : Dfull)
    rw [unop_op, map_inv, inv_inv, hc]

@[expose] noncomputable def sEquiv : Sbp ≃* Shat := MulEquiv.ofBijective sHom sHom_bijective

@[expose] noncomputable def cS : Shat := ⟨cQ, cQ_mem_Shat⟩

theorem sEquiv_labelS : sEquiv labelS = cS⁻¹ := by
  apply Subtype.ext
  show (iotaD labelS.unop)⁻¹ = ((cS⁻¹ : Shat) : Dfull)
  rw [iotaD_labelS]
  rfl

theorem centralizer_cS
    (hC : CentralizerInput) :
    Subgroup.centralizer {cS} = Eam.subgroupOf Shat := by
  ext s
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf]
  have h := hC cv0 s
  rw [clabel_cv0, cv0, cvMul_cvOf, cvOf_eq_iff, one_mul, one_mul] at h
  constructor
  · intro hs
    have h1 := h.1 (by
      have := congrArg Subtype.val hs
      simpa [cS] using this)
    simpa using Eam.inv_mem h1
  · intro hs
    have h1 := h.2 (by simpa using Eam.inv_mem hs)
    apply Subtype.ext
    simpa [cS] using h1

theorem centralizer_equiv_Eam
    (hC : CentralizerInput) {s : Sbp} (hs : IsConj s labelS) :
    Nonempty (Subgroup.centralizer {s} ≃* Eam) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hs
  have e1 : (MulAut.conj c) s = labelS := by rw [MulAut.conj_apply, hc]
  have e2 : (sEquiv) labelS = cS⁻¹ := sEquiv_labelS
  refine ⟨(((centralizerEquiv (MulAut.conj c) s).trans (MulEquiv.subgroupCongr
    (by rw [e1]))).trans ((centralizerEquiv sEquiv labelS).trans (MulEquiv.subgroupCongr
    (by rw [e2, centralizer_inv, centralizer_cS hC])))).trans
    (Subgroup.subgroupOfEquivOfLe Eam_le_Shat)⟩

section Generic

variable {E C : Type*} [Group E] [Group C]

theorem center_commutator_eq {c : E}
    (hcen : (Subgroup.center (commutator E)).map (commutator E).subtype = Subgroup.zpowers c) :
    Subgroup.center (commutator E) = (Subgroup.zpowers c).subgroupOf (commutator E) := by
  rw [Subgroup.subgroupOf, ← hcen, Subgroup.comap_map_eq_self_of_injective
    (commutator E).subtype_injective]

theorem card_center_commutator {c : E}
    (hcen : (Subgroup.center (commutator E)).map (commutator E).subtype = Subgroup.zpowers c)
    (hc2 : Nat.card (Subgroup.zpowers c) = 2) : Nat.card (Subgroup.center (commutator E)) = 2 := by
  rw [← hc2, ← hcen, Subgroup.card_map_of_injective (commutator E).subtype_injective]

theorem isQuasisimple_of_cover {c : E} [((Subgroup.zpowers c).subgroupOf (commutator E)).Normal]
    (hperf : Group.IsPerfect (commutator E))
    (hcen : (Subgroup.center (commutator E)).map (commutator E).subtype = Subgroup.zpowers c)
    (hc2 : Nat.card (Subgroup.zpowers c) = 2)
    (hs : IsSimpleGroup (commutator E ⧸ (Subgroup.zpowers c).subgroupOf (commutator E)))
    (hN : Nat.card (commutator E) ≠ 2) : CFSG.IsQuasisimple (commutator E) := by
  have θ' : commutator E ⧸ Subgroup.center (commutator E) ≃*
      commutator E ⧸ (Subgroup.zpowers c).subgroupOf (commutator E) :=
    QuotientGroup.quotientMulEquivOfEq (center_commutator_eq hcen)
  refine ⟨hperf, θ'.isSimpleGroup, ?_⟩
  by_contra hcomm
  push Not at hcomm
  have hle : commutator (commutator E) ≤ Subgroup.center (commutator E) := by
    rw [show commutator (commutator E) = ⁅(⊤ : Subgroup (commutator E)), ⊤⁆ from rfl,
      Subgroup.commutator_le]
    intro g _ h _
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm, hcomm]
  rw [Group.isPerfect_def.1 hperf] at hle
  have hc := card_center_commutator hcen hc2
  rw [top_le_iff.1 hle, Subgroup.card_top] at hc
  exact hN hc

theorem unique_component_of_cover [Finite E] {c : E}
    [((Subgroup.zpowers c).subgroupOf (commutator E)).Normal]
    (hperf : Group.IsPerfect (commutator E))
    (hcen : (Subgroup.center (commutator E)).map (commutator E).subtype = Subgroup.zpowers c)
    (hc2 : Nat.card (Subgroup.zpowers c) = 2)
    (hs : IsSimpleGroup (commutator E ⧸ (Subgroup.zpowers c).subgroupOf (commutator E)))
    (hN : Nat.card (commutator E) ≠ 2) (Ψ : C ≃* E) :
    ∃ K : Subgroup C, CFSG.IsComponent K ∧ (∀ K' : Subgroup C, CFSG.IsComponent K' → K' = K) ∧
      CFSG.IsQuasisimple K ∧ Nat.card (Subgroup.center K) = 2 ∧
      Nonempty (K ⧸ Subgroup.center K ≃*
        commutator E ⧸ (Subgroup.zpowers c).subgroupOf (commutator E)) ∧
      Nat.card (K ⧸ Subgroup.center K) * 2 = Nat.card (commutator E) := by
  have hq := isQuasisimple_of_cover hperf hcen hc2 hs hN
  have hU := unique_component_of_quasisimple_commutator hq
  have hcz := card_center_commutator hcen hc2
  set K := (commutator E).map Ψ.symm.toMonoidHom with hKdef
  have eK : commutator E ≃* K :=
    (commutator E).equivMapOfInjective Ψ.symm.toMonoidHom Ψ.symm.injective
  have eQ : K ⧸ Subgroup.center K ≃* commutator E ⧸ Subgroup.center (commutator E) :=
    QuotientGroup.congr _ _ eK.symm (Subgroup.map_center_eq eK.symm)
  refine ⟨K, CFSG.LocalCores.isComponent_map_mulEquiv Ψ.symm hU.1, fun K' hK' => ?_,
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eK hq, ?_,
    ⟨eQ.trans (QuotientGroup.quotientMulEquivOfEq (center_commutator_eq hcen))⟩, ?_⟩
  · have h := hU.2 _ (CFSG.LocalCores.isComponent_map_mulEquiv Ψ hK')
    rw [hKdef, ← h, CFSG.LocalCores.map_map_symm]
  · rw [← hcz]
    exact Nat.card_congr (Subgroup.centerCongr eK).symm.toEquiv
  · have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (commutator E))
    rw [hcz] at h
    rw [Nat.card_congr eQ.toEquiv, h]

end Generic

theorem stdGroup_simple :
    IsSimpleGroup stdGroup :=
  CFSG.Monster.B.E6.standard_twisted_e6_group_simple.2.2

theorem isConj_labelS_of_rank
    {s : Sbp} (hs : orderOf s = 2)
    (hr : ((βr s) - 1).rank = 1860) : IsConj s labelS := by
  obtain ⟨i, ⟨hi, hc⟩, -⟩ := four_classes co2_involution_input hs
  have e := rank_beta_conj hc
  obtain ⟨h1, h0, h5, h3⟩ := rank_four
  have hi1 : i = 1 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> omega
  subst hi1
  obtain ⟨g, -, hg⟩ := labelS_mem_jClass
  refine hc.trans (isConj_iff.2 ⟨g⁻¹, ?_⟩)
  rw [rs1_eq, hg]
  group

theorem native_rank_1860_unique_component
    (hC : CentralizerInput) :
    ∀ s : Sbp, orderOf s = 2 → ((βr s) - 1).rank = 1860 →
      ∃ K : Subgroup (Subgroup.centralizer {s}), CFSG.IsComponent K ∧
        (∀ K' : Subgroup (Subgroup.centralizer {s}), CFSG.IsComponent K' → K' = K) ∧
        CFSG.IsQuasisimple K ∧ Nat.card (Subgroup.center K) = 2 ∧
        Nonempty (K ⧸ Subgroup.center K ≃* stdGroup) ∧
        Nat.card (K ⧸ Subgroup.center K) = 76532479683774853939200 ∧
        17 ∣ Nat.card (K ⧸ Subgroup.center K) := by
  intro s hs hr
  have hE := derivedCoverInput_holds
  have hΨ := centralizer_equiv_Eam hC (isConj_labelS_of_rank hs hr)
  have hperf := hE.2.1
  have hcen := hE.2.2.2.1
  have hc2 := hE.2.2.2.2.1
  have hθ := hE.2.2.2.2.2.1
  have hcard := hE.2.2.2.2.2.2.2
  obtain ⟨Ψ⟩ := hΨ
  obtain ⟨θ⟩ := hθ
  have hs' := @MulEquiv.isSimpleGroup _ _ _ _ stdGroup_simple θ
  have hU := unique_component_of_cover hperf hcen hc2 hs' (by rw [hcard]; norm_num) Ψ
  obtain ⟨K, hK, huniq, hq, hz, ⟨eQ⟩, hk⟩ := hU
  have hk' : Nat.card (K ⧸ Subgroup.center K) = 76532479683774853939200 := by
    rw [hcard] at hk
    omega
  exact ⟨K, hK, huniq, hq, hz, ⟨eQ.trans θ⟩, hk', by rw [hk']; norm_num⟩

end CFSG.Monster.B.CTIB
