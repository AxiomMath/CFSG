module

public import CFSG.RankThree.PartOne.S11b.Sec11Indeed
public import CFSG.RankThree.PartOne.S11d.Sec11Common
public import CFSG.RankThree.PartOne.S11d.SitSwap
public import CFSG.RankThree.PartOne.S11d.FourClaimAux
public import CFSG.RankThree.PartOne.S11d.FiveClaimAux
public import CFSG.RankThree.PartOne.S11d.ThetaCalc
public import CFSG.RankThree.PartOne.S11d.FixedRes
public import CFSG.RankThree.PartOne.S11d.Facts5
public import CFSG.RankThree.PartOne.S11d.FactsFinal
public import CFSG.RankThree.PartOne.S11d.FinalSylow
public import CFSG.RankThree.PartOne.S11d.FinalOrders
public import CFSG.RankThree.PartOne.S11d.PElements
public import CFSG.RankThree.PartOne.S11d.Transvection
public import CFSG.RankThree.PartOne.S11d.ThreeAux
import CFSG.RankThree.Coprime.ThompsonElementaryComplement
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
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
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import CFSG.Assembly.QuasithinDefs
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBMResidualCommonPlaneSylowTwo
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_4
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection5.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.Defs

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.Blueprint CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement Pointwise

namespace Sec11Indeed

variable {G : Type} [Group G] [Finite G]

structure FinalSetup (p : ℕ) (A : Subgroup G) (c : G) (L : Subgroup G) (a d : G) (K : Subgroup G)
    (x y : G) : Prop where
  sit : Sit p A c L a d
  sit' : Sit p A a K c d
  E_le : inSubgroup perfectResidual (L ⊓ centralizer ({a} : Set G)) ≤ K
  AL_le : A ⊓ L ≤ K
  rank : CFSG.pRank p ↥L = 1
  rankK : CFSG.pRank p ↥K = 1
  hx : Transvection p A K d x c
  hy : Transvection p A L d y a

namespace FinalSetup

variable {p : ℕ} {A : Subgroup G} {c : G} {L : Subgroup G} {a d : G} {K : Subgroup G} {x y : G}

theorem prime (h : FinalSetup p A c L a d K x y) : p.Prime := h.sit.prime

theorem p_ne_two (h : FinalSetup p A c L a d K x y) : p ≠ 2 := by
  have := h.sit.five_le
  omega

theorem a_ne_one (h : FinalSetup p A c L a d K x y) : a ≠ 1 := by
  intro ha
  have := h.sit.a_field.2.1
  rw [ha] at this
  exact this (Subgroup.mem_sup_left L.one_mem)

theorem evenRank_le (h : FinalSetup p A c L a d K x y) : evenRank G ≤ 3 :=
  (sectionTenSetup_evenRank_eq h.sit.setup).le

theorem A_le_normalizer_L (h : FinalSetup p A c L a d K x y) : A ≤ normalizer (L : Set G) := by
  have hLF : L ∈ thetaComponentFamily p A :=
    mem_thetaComponentFamily_iff.mpr ⟨c, h.sit.c_mem, h.sit.c_ne_one, h.sit.L_mem.2⟩
  exact selected_prime_elements_normalize_theta_components.2 G h.evenRank_le p h.sit.prime
    h.sit.three_lt A h.sit.A_elem L hLF

theorem A_le_normalizer_K (h : FinalSetup p A c L a d K x y) : A ≤ normalizer (K : Set G) := by
  have hKF : K ∈ thetaComponentFamily p A :=
    mem_thetaComponentFamily_iff.mpr ⟨a, h.sit.a_mem, h.a_ne_one, h.sit'.L_mem.2⟩
  exact selected_prime_elements_normalize_theta_components.2 G h.evenRank_le p h.sit.prime
    h.sit.three_lt A h.sit.A_elem K hKF

theorem K_le_centralizer_a (h : FinalSetup p A c L a d K x y) : K ≤ centralizer ({a} : Set G) :=
  (mem_thetaComponentsAt_iff.mp h.sit'.L_mem.2).1

theorem pRank_K (h : FinalSetup p A c L a d K x y) : CFSG.pRank p ↥K = 1 := h.rankK

theorem coprime_of_mem_center (h : FinalSetup p A c L a d K x y) :
    ∀ z ∈ L, z ∈ centralizer (L : Set G) → Nat.Coprime (orderOf z) p := by
  intro z hz hzC
  have hzc : (⟨z, hz⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := mem_centralizer_iff.mp hzC g g.2
    exact Subtype.ext this
  have h1 : orderOf (⟨⟨z, hz⟩, hzc⟩ : ↥(Subgroup.center ↥L)) ∣ Nat.card (Subgroup.center ↥L) :=
    orderOf_dvd_natCard _
  have h2 : orderOf z = orderOf (⟨⟨z, hz⟩, hzc⟩ : ↥(Subgroup.center ↥L)) := by
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
  rw [h2]
  have hpc : Nat.Coprime p (Nat.card (Subgroup.center ↥L)) :=
    (Nat.Prime.coprime_iff_not_dvd h.sit.prime).mpr h.sit.p_ndvd
  exact (Nat.Coprime.coprime_dvd_left h1 hpc.symm)

theorem isTransv_y (h : FinalSetup p A c L a d K x y) : Transv.IsTransv A d y where
  norm := by
    refine mem_normalizer_of_conj_subset fun e he => ?_
    have := h.hy.comm_mem e he
    have h2 : y * e * y⁻¹ = (y * e * y⁻¹ * e⁻¹) * e := by group
    rw [h2]
    exact mul_mem ((zpowers_le.mpr h.sit.d_mem) this) he
  cent := by
    have := h.hy.cent_d
    calc y * d = (y * d * y⁻¹) * y := by group
      _ = d * y := by rw [this]
  comm e he := h.hy.comm_mem e he

theorem isTransv_x (h : FinalSetup p A c L a d K x y) : Transv.IsTransv A d x where
  norm := by
    refine mem_normalizer_of_conj_subset fun e he => ?_
    have := h.hx.comm_mem e he
    have h2 : x * e * x⁻¹ = (x * e * x⁻¹ * e⁻¹) * e := by group
    rw [h2]
    exact mul_mem ((zpowers_le.mpr h.sit.d_mem) this) he
  cent := by
    have := h.hx.cent_d
    calc x * d = (x * d * x⁻¹) * x := by group
      _ = d * x := by rw [this]
  comm e he := h.hx.comm_mem e he

theorem sylow_L (h : FinalSetup p A c L a d K x y) :
    ∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p S L ∧ IsCyclic S ∧ A ⊓ L ≤ S ∧
      A ≤ normalizer (S : Set G) ∧
      zpowers y = S ∧ orderOf y = p ^ (Nat.card ↥L).factorization p ∧
      2 ≤ (Nat.card ↥L).factorization p := by
  have : IsElementaryAbelian p A := h.sit.A_elem
  refine exists_sylow_of_transvection h.prime h.p_ne_two h.rank.le h.A_le_normalizer_L
    (IsElementaryAbelian.isPGroup p A) h.hy.mem h.hy.pElt h.isTransv_y.norm h.sit.a_mem
    (h.sit.pow_eq_one h.sit.a_mem) ?_
  intro heq
  apply h.hy.moves
  have : a * y = y * a := by
    calc a * y = (a * y * a⁻¹) * a := by group
      _ = y * a := by rw [heq]
  calc y * a * y⁻¹ = a * y * y⁻¹ := by rw [this]
    _ = a := by group

theorem sylow_K (h : FinalSetup p A c L a d K x y) :
    ∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p S K ∧ IsCyclic S ∧ A ⊓ K ≤ S ∧
      A ≤ normalizer (S : Set G) ∧
      zpowers x = S ∧ orderOf x = p ^ (Nat.card ↥K).factorization p ∧
      2 ≤ (Nat.card ↥K).factorization p := by
  have : IsElementaryAbelian p A := h.sit.A_elem
  exact exists_sylow_of_transvection h.prime h.p_ne_two h.pRank_K.le h.A_le_normalizer_K
    (IsElementaryAbelian.isPGroup p A) h.hx.mem h.hx.pElt h.isTransv_x.norm h.sit.c_mem
    (h.sit.pow_eq_one h.sit.c_mem) (fun heq => by
      apply h.hx.moves
      have : c * x = x * c := by
        calc c * x = (c * x * c⁻¹) * c := by group
          _ = x * c := by rw [heq]
      calc x * c * x⁻¹ = c * x * x⁻¹ := by rw [this]
        _ = c := by group)

theorem zeta_mem_centralizer (h : FinalSetup p A c L a d K x y) :
    y ^ p ∈ centralizer (A : Set G) :=
  Transv.pow_mem_centralizer (h.sit.pow_eq_one h.sit.d_mem) h.isTransv_y

theorem zeta_comm (h : FinalSetup p A c L a d K x y) {e : G} (he : e ∈ A) :
    e * y ^ p = y ^ p * e :=
  mem_centralizer_iff.mp h.zeta_mem_centralizer e he

theorem zeta_mem_L (h : FinalSetup p A c L a d K x y) : y ^ p ∈ L :=
  L.pow_mem h.hy.mem p

theorem mem_zpowers_c_of_cent_L (h : FinalSetup p A c L a d K x y) {e : G} (heA : e ∈ A)
    (heC : e ∈ centralizer (L : Set G)) : e ∈ zpowers c := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hap : a ^ p = 1 := h.sit.pow_eq_one h.sit.a_mem
  obtain ⟨i, j, k, rfl⟩ := h.sit.exists_zpow_coords heA
  have hcj : c ^ j ∈ centralizer (L : Set G) := h.sit.zpow_c_mem_centralizer j
  have h1 : a ^ i * d ^ k ∈ centralizer (L : Set G) := by
    have : a ^ i * d ^ k = (a ^ i * c ^ j * d ^ k) * (c ^ j)⁻¹ := by
      have hcd : Commute (c ^ j) (d ^ k) := (h.sit.A_comm h.sit.c_mem h.sit.d_mem |> fun hh =>
        (show Commute c d from hh).zpow_zpow j k)
      have hac : Commute (a ^ i) (c ^ j) := (show Commute a c from
        h.sit.A_comm h.sit.a_mem h.sit.c_mem).zpow_zpow i j
      calc a ^ i * d ^ k = a ^ i * (c ^ j * (c ^ j)⁻¹) * d ^ k := by group
        _ = a ^ i * c ^ j * ((c ^ j)⁻¹ * d ^ k) := by group
        _ = a ^ i * c ^ j * (d ^ k * (c ^ j)⁻¹) := by rw [hcd.inv_left.eq]
        _ = (a ^ i * c ^ j * d ^ k) * (c ^ j)⁻¹ := by group
    rw [this]
    exact mul_mem heC (inv_mem hcj)
  by_cases hi : (p : ℤ) ∣ i
  · have hai : a ^ i = 1 := by
      obtain ⟨t, rfl⟩ := hi
      rw [zpow_mul, zpow_natCast, hap, one_zpow]
    rw [hai, one_mul] at h1
    have hdkL : d ^ k ∈ L := zpow_mem h.sit.d_mem_L k
    have hcop := h.coprime_of_mem_center _ hdkL h1
    have hdkp : (d ^ k) ^ p = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        h.sit.pow_eq_one h.sit.d_mem, one_zpow]
    have hdk1 : d ^ k = 1 := by
      have hdvd : orderOf (d ^ k) ∣ p := orderOf_dvd_of_pow_eq_one hdkp
      have : orderOf (d ^ k) = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd
      exact orderOf_eq_one_iff.mp this
    rw [hai, hdk1, one_mul, mul_one]
    exact zpow_mem (mem_zpowers c) j
  · exfalso
    obtain ⟨m, hm⟩ := exists_nat_pow_zpow_eq_self hap hi
    have hcomm : Commute (a ^ i) (d ^ k) := (show Commute a d from
      h.sit.A_comm h.sit.a_mem h.sit.d_mem).zpow_zpow i k
    have h2 : (a ^ i * d ^ k) ^ m = a * (d ^ k) ^ m := by
      rw [hcomm.mul_pow, ← zpow_natCast (a ^ i) m, hm]
    have h3 : a * (d ^ k) ^ m ∈ centralizer (L : Set G) := by
      rw [← h2]
      exact (centralizer (L : Set G)).pow_mem h1 m
    have h4 : a ∈ L ⊔ centralizer (L : Set G) := by
      have hdkm : (d ^ k) ^ m ∈ L := L.pow_mem (zpow_mem h.sit.d_mem_L k) m
      have : a = (a * (d ^ k) ^ m) * ((d ^ k) ^ m)⁻¹ := by group
      rw [this]
      exact mul_mem (mem_sup_right h3) (inv_mem (mem_sup_left hdkm))
    exact h.sit.a_field.2.1 h4

theorem orderOf_zeta (h : FinalSetup p A c L a d K x y) :
    orderOf (y ^ p) = p ^ ((Nat.card ↥L).factorization p - 1) := by
  obtain ⟨S, -, -, -, -, -, hyord, hn2⟩ := h.sylow_L
  exact orderOf_pow_prime_of_eq h.prime (by omega) hyord

theorem d_mem_zpowers_zeta (h : FinalSetup p A c L a d K x y) : d ∈ zpowers (y ^ p) := by
  obtain ⟨S, -, -, hALS, -, hygen, hyord, hn2⟩ := h.sylow_L
  have hdS : d ∈ S := hALS ⟨h.sit.d_mem, h.sit.d_mem_L⟩
  rw [← hygen] at hdS
  exact mem_zpowers_pow_of_pow_eq_one h.prime hn2 hyord hdS (h.sit.pow_eq_one h.sit.d_mem)

theorem vp (hFix : FieldFixedPElements)
    (h : FinalSetup p A c L a d K x y) :
    (Nat.card ↥K).factorization p = (Nat.card ↥L).factorization p := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hcA := h.sit.c_mem
  have haA := h.sit.a_mem
  obtain ⟨SL, hSL, -, -, hASL, hyL, -, -⟩ := h.sylow_L
  obtain ⟨SK, hSK, -, -, hASK, hxK, -, -⟩ := h.sylow_K
  set E := inSubgroup perfectResidual (L ⊓ centralizer ({a} : Set G)) with hE
  have hEL : E ≤ L := (inSubgroup_perfectResidual_le _).trans inf_le_left
  have hEa : E ≤ centralizer ({a} : Set G) := (inSubgroup_perfectResidual_le _).trans inf_le_right
  have hKE : inSubgroup perfectResidual (K ⊓ centralizer ({c} : Set G)) = E :=
    fixedRes_eq_of_field h.sit.L_mem.2 h.sit.a_field h.sit'.a_field h.E_le h.K_le_centralizer_a
  have hxA : x ^ p ∈ centralizer (A : Set G) :=
    Transv.pow_mem_centralizer (h.sit.pow_eq_one h.sit.d_mem) h.isTransv_x
  have hxc : x ^ p ∈ centralizer ({c} : Set G) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hxA c hcA).symm
  have hξE : x ^ p ∈ E := by
    rw [← hKE]
    exact hFix G p K c (h.sit'.fieldAutSetting h.sit'.a_field) (h.sit'.pow_eq_one hcA)
      (h.sit'.fieldAutRank hcA) (x ^ p) ⟨K.pow_mem h.hx.mem p, hxc⟩ (pElement_pow hp h.hx.pElt p)
  have hζE : y ^ p ∈ E :=
    hFix G p L a (h.sit.fieldAutSetting h.sit.a_field) (h.sit.pow_eq_one haA)
      (h.sit.fieldAutRank haA) (y ^ p)
      ⟨h.zeta_mem_L, mem_centralizer_singleton_iff.mpr (h.zeta_comm haA).symm⟩
      ⟨_, h.orderOf_zeta⟩
  have hSL' : CFSG.ABGLocalTools.IsSylowOf p (zpowers y) L := by
    rw [hyL]
    exact hSL
  have hSK' : CFSG.ABGLocalTools.IsSylowOf p (zpowers x) K := by
    rw [hxK]
    exact hSK
  have hmoveL : a * y * a⁻¹ ≠ y := by
    intro heq
    apply h.hy.moves
    have : a * y = y * a := by
      calc a * y = (a * y * a⁻¹) * a := by group
        _ = y * a := by rw [heq]
    calc y * a * y⁻¹ = a * y * y⁻¹ := by rw [this]
      _ = a := by group
  have hmoveK : c * x * c⁻¹ ≠ x := by
    intro heq
    apply h.hx.moves
    have : c * x = x * c := by
      calc c * x = (c * x * c⁻¹) * c := by group
        _ = x * c := by rw [heq]
    calc x * c * x⁻¹ = c * x * x⁻¹ := by rw [this]
      _ = c := by group
  exact (factorization_eq_of_common_fixed hSL' hSK' h.sit.a_field.1 h.sit'.a_field.1
    (by rw [hyL]; exact hASL haA) (by rw [hxK]; exact hASK hcA) (h.sit.pow_eq_one haA)
    (h.sit'.pow_eq_one hcA) hmoveL hmoveK hEL h.E_le
    (fun e he => by rw [← mem_centralizer_singleton_iff.mp (hEa he)]; group)
    (fun e he => by rw [← h.sit.comm_c_L (hEL he)]; group) hζE hξE).symm

theorem mem_zpowers_c_of_cent (hFix : FieldFixedPElements) (hKO : OutPCyclic)
    (h : FinalSetup p A c L a d K x y) {z : G} (hzL : z ∈ centralizer (L : Set G))
    (hzA : z ∈ centralizer (A : Set G)) (hzp : ∃ k : ℕ, orderOf z = p ^ k) : z ∈ zpowers c := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hcA := h.sit.c_mem
  have hcp : c ^ p = 1 := h.sit.pow_eq_one hcA
  have hc1 : orderOf c = p := orderOf_eq_prime hcp h.sit.c_ne_one
  have hcz : c * z = z * c := (mem_centralizer_iff.mp hzA c hcA)
  have hcC : c ∈ centralizer (zpowers z : Set G) := by
    rw [mem_centralizer_iff]
    intro t ht
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp ht
    exact ((show Commute z c from hcz.symm).zpow_left m).eq
  have hzc : zpowers c ≤ normalizer (zpowers z : Set G) :=
    zpowers_le.mpr (centralizer_le_normalizer _ hcC)
  have hcpg : IsPGroup p (zpowers c) := isPGroup_zpowers_of_orderOf ⟨1, by rw [pow_one]; exact hc1⟩
  have hPp : IsPGroup p (zpowers c ⊔ zpowers z : Subgroup G) :=
    hcpg.to_sup_of_normal_right' (isPGroup_zpowers_of_orderOf hzp) hzc
  have hcCL : c ∈ centralizer (L : Set G) :=
    mem_centralizer_iff.mpr fun g hg => h.sit.comm_c_L hg
  have hcCA : c ∈ centralizer (A : Set G) :=
    mem_centralizer_iff.mpr fun g hg => h.sit.A_comm hg hcA
  have hPC : zpowers c ⊔ zpowers z ≤ centralizer (L : Set G) :=
    sup_le (zpowers_le.mpr hcCL) (zpowers_le.mpr hzL)
  have hPA : zpowers c ⊔ zpowers z ≤ centralizer (A : Set G) :=
    sup_le (zpowers_le.mpr hcCA) (zpowers_le.mpr hzA)
  have hPcyc : IsCyclic (zpowers c ⊔ zpowers z : Subgroup G) := by
    by_contra hnc
    have : Fact (IsPGroup p (zpowers c ⊔ zpowers z : Subgroup G)) := ⟨hPp⟩
    obtain ⟨E₂, -, hE₂card, hE₂el⟩ := CFSG.lemma_4_5_a h.p_ne_two hnc
    have hEel : IsElementaryAbelian p (E₂.map (zpowers c ⊔ zpowers z : Subgroup G).subtype) :=
      CFSG.IsElementaryAbelian.map_subtype
    have hEcard : Nat.card (E₂.map (zpowers c ⊔ zpowers z : Subgroup G).subtype) = p ^ 2 := by
      rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hE₂card]
    have hEP : E₂.map (zpowers c ⊔ zpowers z : Subgroup G).subtype ≤ zpowers c ⊔ zpowers z :=
      Subgroup.map_subtype_le _
    obtain ⟨e, heE, heA⟩ : ∃ e ∈ E₂.map (zpowers c ⊔ zpowers z : Subgroup G).subtype, e ∉ A := by
      by_contra hno
      push Not at hno
      have hEc : E₂.map (zpowers c ⊔ zpowers z : Subgroup G).subtype ≤ zpowers c :=
        fun e he => h.mem_zpowers_c_of_cent_L (hno e he) (hPC (hEP he))
      have := Subgroup.card_le_of_le hEc
      rw [hEcard, Nat.card_zpowers, hc1] at this
      have h2 : p ^ 2 = p * p := by ring
      have := hp.one_lt
      nlinarith
    have hep : e ^ p = 1 := by
      have : IsElementaryAbelian p (E₂.map (zpowers c ⊔ zpowers z : Subgroup G).subtype) := hEel
      exact elemPow_eq_one_of_isElementaryAbelian (p := p) e heE
    obtain ⟨-, S₂, hS₂L, hS₂1, hS₂2, hAS₂, -⟩ := h.sit.L_mem.1.1.1
    have heS₂ : e ∈ normalizer (S₂ : Set G) := by
      refine centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun s hs => ?_)
      exact mem_centralizer_iff.mp (hPC (hEP heE)) s (hS₂L hs)
    exact false_of_rank_four_of_normalizes h.evenRank_le hp h.p_ne_two h.sit.A_elem
      h.sit.setup.2.2.2.2.2.2.2.1 hS₂1 hS₂2 hAS₂ heA hep
      (fun x hx => mem_centralizer_iff.mp (hPA (hEP heE)) x hx) heS₂
  by_contra hzc'
  obtain ⟨g, hg⟩ := hPcyc.exists_generator
  set v : G := (g : G) with hv
  have hvgen : ∀ t ∈ (zpowers c ⊔ zpowers z : Subgroup G), t ∈ zpowers v := by
    intro t ht
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp (hg ⟨t, ht⟩)
    exact mem_zpowers_iff.mpr ⟨m, by simpa [hv] using congrArg Subtype.val hm⟩
  have hvP : v ∈ zpowers c ⊔ zpowers z := g.2
  have hvord : orderOf v = Nat.card (zpowers c ⊔ zpowers z : Subgroup G) := by
    rw [hv, Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg]
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hPp
  have hvk : orderOf v = p ^ k := hvord.trans hk
  have hk2 : 2 ≤ k := by
    by_contra hlt
    push Not at hlt
    have hle : zpowers c ≤ zpowers c ⊔ zpowers z := le_sup_left
    have hcard : Nat.card (zpowers c ⊔ zpowers z : Subgroup G) ≤ Nat.card (zpowers c) := by
      rw [hk, Nat.card_zpowers, hc1]
      calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
        _ = p := pow_one p
    have heq := Subgroup.eq_of_le_of_card_ge hle hcard
    exact hzc' (by rw [heq]; exact mem_sup_right (mem_zpowers z))
  have hcv : c ∈ zpowers v := hvgen c (mem_sup_left (mem_zpowers c))
  obtain ⟨s, hs⟩ := mem_zpowers_iff.mp (mem_zpowers_pow_of_pow_eq_one hp hk2 hvk hcv hcp)
  have hup : (v ^ s) ^ p = c := by
    rw [← hs, ← zpow_natCast (v ^ s) p, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
  have huP : v ^ s ∈ zpowers c ⊔ zpowers z := zpow_mem hvP s
  have huC : v ^ s ∈ centralizer (L : Set G) := hPC huP
  have huA : v ^ s ∈ centralizer (A : Set G) := hPA huP
  have hup' : ∃ j : ℕ, orderOf (v ^ s) = p ^ j := pElement_zpow hp ⟨k, hvk⟩ s
  have hua : v ^ s ∈ centralizer ({a} : Set G) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp huA a h.sit.a_mem).symm
  have huK : v ^ s ∈ normalizer (K : Set G) :=
    pElement_normalizes_thetaComponentsAt h.evenRank_le hp h.sit.three_lt hua hup' h.sit'.L_mem.2
  have hζE : y ^ p ∈ inSubgroup perfectResidual (L ⊓ centralizer ({a} : Set G)) :=
    hFix G p L a (h.sit.fieldAutSetting h.sit.a_field) (h.sit.pow_eq_one h.sit.a_mem)
      (h.sit.fieldAutRank h.sit.a_mem) (y ^ p)
      ⟨h.zeta_mem_L, mem_centralizer_singleton_iff.mpr (h.zeta_comm h.sit.a_mem).symm⟩
      ⟨_, h.orderOf_zeta⟩
  have hζK : y ^ p ∈ K := h.E_le hζE
  obtain ⟨S, hSK, -, -, hASK, hxgen, -, hn2K⟩ := h.sylow_K
  have hvp := h.vp hFix
  have hn2 : 2 ≤ (Nat.card ↥L).factorization p := by
    rw [← hvp]
    exact hn2K
  have hset : FieldAutSetting p K c := h.sit'.fieldAutSetting h.sit'.a_field
  have hKO' : ∀ w : G, w ∈ normalizer (K : Set G) → (∃ j : ℕ, orderOf w = p ^ j) →
      c * w = w * c → c ∈ zpowers w ⊔ (K ⊔ centralizer (K : Set G)) ∨
        w ∈ zpowers c ⊔ (K ⊔ centralizer (K : Set G)) := fun w hw hwp hcw =>
    hKO G p K c hset h.pRank_K.le c w (h.A_le_normalizer_K hcA) hw hcw
      ⟨1, by rw [pow_one]; exact hc1⟩ hwp
  have hZcard : Nat.card (zpowers (y ^ p)) * p = p ^ (Nat.card ↥K).factorization p := by
    rw [Nat.card_zpowers, h.orderOf_zeta, hvp, ← pow_succ]
    congr 1
    omega
  have hres := mem_sup_of_out_centralizes (J := K) hp h.p_ne_two h.pRank_K.le
    (a := c) (w := v ^ s) (h.A_le_normalizer_K hcA) huK hcp hup' (mem_centralizer_iff.mp huA c hcA)
    hKO' ⟨S, hSK, hASK hcA, x, by rw [← hxgen]; exact mem_zpowers x, fun heq => by
      apply h.hx.moves
      have : c * x = x * c := by
        calc c * x = (c * x * c⁻¹) * c := by group
          _ = x * c := by rw [heq]
      calc x * c * x⁻¹ = c * x * x⁻¹ := by rw [this]
        _ = c := by group⟩
    (Z := zpowers (y ^ p)) (zpowers_le.mpr hζK)
    (isPGroup_zpowers_of_orderOf ⟨_, h.orderOf_zeta⟩)
    (fun t ht => by
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp ht
      exact (Commute.zpow_right (h.zeta_comm hcA : c * y ^ p = y ^ p * c) m).eq)
    (fun t ht => by
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp ht
      have hh : (v ^ s) * y ^ p = y ^ p * (v ^ s) :=
        (mem_centralizer_iff.mp huC (y ^ p) h.zeta_mem_L).symm
      exact (Commute.zpow_right hh m).eq)
    hZcard (by rw [hvp]; exact hn2)
  have hcK' : c ∈ normalizer ((K ⊔ centralizer (K : Set G) : Subgroup G) : Set G) :=
    mem_normalizer_sup_centralizer (h.A_le_normalizer_K hcA)
  have hz' : zpowers c ≤ normalizer ((K ⊔ centralizer (K : Set G) : Subgroup G) : Set G) :=
    zpowers_le.mpr hcK'
  have hcoe := coe_mul_of_left_le_normalizer_right (zpowers c) (K ⊔ centralizer (K : Set G)) hz'
  have hmem : v ^ s ∈ ((zpowers c : Subgroup G) : Set G) *
      ((K ⊔ centralizer (K : Set G) : Subgroup G) : Set G) := by
    rw [← hcoe]
    exact hres
  obtain ⟨t, ht, n', hn', htn⟩ := Set.mem_mul.mp hmem
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ht
  have hcu : c * (v ^ s) = (v ^ s) * c := mem_centralizer_iff.mp huA c hcA
  have hcn : Commute (c ^ i) n' := by
    have h1 : n' = (c ^ i)⁻¹ * (v ^ s) := by rw [← htn]; group
    rw [h1]
    exact ((Commute.refl (c ^ i)).inv_right).mul_right
      ((Commute.zpow_left (show Commute c (v ^ s) from hcu) i))
  have hcipow : (c ^ i) ^ p = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hcp, one_zpow]
  have hcpn : c = n' ^ p := by
    calc c = (v ^ s) ^ p := hup.symm
      _ = (c ^ i * n') ^ p := by rw [htn]
      _ = n' ^ p := by rw [hcn.mul_pow, hcipow, one_mul]
  have hcN : c ∈ K ⊔ centralizer (K : Set G) := by
    rw [hcpn]
    exact (K ⊔ centralizer (K : Set G)).pow_mem hn' p
  exact h.sit'.a_field.2.1 hcN

theorem pElement_mem_A_zeta (hFix : FieldFixedPElements) (hKO : OutPCyclic)
    (h : FinalSetup p A c L a d K x y) {w : G} (hwA : ∀ e ∈ A, w * e = e * w)
    (hwζ : w * y ^ p = y ^ p * w) (hwp : ∃ k : ℕ, orderOf w = p ^ k) :
    ∃ α ∈ A, ∃ e : ℤ, w = α * (y ^ p) ^ e := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hcA := h.sit.c_mem
  have haA := h.sit.a_mem
  have hap : a ^ p = 1 := h.sit.pow_eq_one haA
  have ha1 : orderOf a = p := orderOf_eq_prime hap h.a_ne_one
  have hapg : ∃ j : ℕ, orderOf a = p ^ j := ⟨1, by rw [pow_one]; exact ha1⟩
  have hwc : w ∈ centralizer ({c} : Set G) :=
    mem_centralizer_singleton_iff.mpr (hwA c hcA)
  have hwL : w ∈ normalizer (L : Set G) :=
    pElement_normalizes_thetaComponentsAt h.evenRank_le hp h.sit.three_lt hwc hwp h.sit.L_mem.2
  have hset : FieldAutSetting p L a := h.sit.fieldAutSetting h.sit.a_field
  obtain ⟨S, hSL, hScyc, hALS, hAS, hygen, hyord, hn2⟩ := h.sylow_L
  have hZcard : Nat.card (zpowers (y ^ p)) * p = p ^ (Nat.card ↥L).factorization p := by
    rw [Nat.card_zpowers, h.orderOf_zeta, ← pow_succ]
    congr 1
    omega
  have hZc : ∀ t ∈ zpowers (y ^ p), ∀ e ∈ A, e * t = t * e := by
    intro t ht e he
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp ht
    exact (Commute.zpow_right (h.zeta_comm he : e * y ^ p = y ^ p * e) m).eq
  have hKO' : ∀ v : G, v ∈ normalizer (L : Set G) → (∃ j : ℕ, orderOf v = p ^ j) →
      a * v = v * a → a ∈ zpowers v ⊔ (L ⊔ centralizer (L : Set G)) ∨
        v ∈ zpowers a ⊔ (L ⊔ centralizer (L : Set G)) := fun v hv hvp hav =>
    hKO G p L a hset h.rank.le a v (h.A_le_normalizer_L haA) hv hav hapg hvp
  have hres := mem_sup_of_out_centralizes (J := L) hp h.p_ne_two h.rank.le (a := a) (w := w)
    (h.A_le_normalizer_L haA) hwL hap hwp (hwA a haA).symm hKO'
    ⟨S, hSL, hAS haA, y, by rw [← hygen]; exact mem_zpowers y, fun heq => by
      apply h.hy.moves
      have : a * y = y * a := by
        calc a * y = (a * y * a⁻¹) * a := by group
          _ = y * a := by rw [heq]
      calc y * a * y⁻¹ = a * y * y⁻¹ := by rw [this]
        _ = a := by group⟩
    (Z := zpowers (y ^ p)) (zpowers_le.mpr h.zeta_mem_L)
    (isPGroup_zpowers_of_orderOf ⟨_, h.orderOf_zeta⟩) (fun t ht => hZc t ht a haA)
    (fun t ht => by
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp ht
      exact (Commute.zpow_right (hwζ : w * y ^ p = y ^ p * w) m).eq)
    hZcard hn2
  have haN : a ∈ normalizer ((L ⊔ centralizer (L : Set G) : Subgroup G) : Set G) :=
    mem_normalizer_sup_centralizer (h.A_le_normalizer_L haA)
  have hcoe := coe_mul_of_left_le_normalizer_right (zpowers a) (L ⊔ centralizer (L : Set G))
    (zpowers_le.mpr haN)
  have hw' : w ∈ ((zpowers a : Subgroup G) : Set G) *
      ((L ⊔ centralizer (L : Set G) : Subgroup G) : Set G) := by
    rw [← hcoe]
    exact hres
  obtain ⟨t, ht, n', hn', hwtn⟩ := Set.mem_mul.mp hw'
  have hcoe2 := coe_mul_of_right_le_normalizer_left L (centralizer (L : Set G))
    (centralizer_le_normalizer _)
  have hn'' : n' ∈ (L : Set G) * (centralizer (L : Set G) : Set G) := by
    rw [← hcoe2]
    exact hn'
  obtain ⟨ℓ, hℓ, z, hz, hℓz⟩ := Set.mem_mul.mp hn''
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ht
  have hwe : w = a ^ i * (ℓ * z) := by rw [hℓz, hwtn]
  have hai_mem : a ^ i ∈ A := zpow_mem haA i
  have hu₀ : ℓ * z = (a ^ i)⁻¹ * w := by rw [hwe]; group
  have hc_aiw : Commute (a ^ i)⁻¹ w :=
    ((show Commute w (a ^ i) from hwA _ hai_mem).symm).inv_left
  have hu₀p : ∃ k : ℕ, orderOf (ℓ * z) = p ^ k := by
    rw [hu₀]
    exact pElement_mul_of_commute hp hc_aiw (pElement_inv (pElement_zpow hp hapg i)) hwp
  obtain ⟨ℓ', hℓ', z', hz', hdec, hℓ'p, hz'p⟩ :=
    exists_pElement_decomp hp h.coprime_of_mem_center hℓ hz hu₀p
  have hℓ'A : ∀ e ∈ A, e * ℓ' = ℓ' * e := by
    intro e he
    have heL : e ∈ normalizer (L : Set G) := h.A_le_normalizer_L he
    have hc1 : Commute e (a ^ i)⁻¹ :=
      (show Commute e (a ^ i) from h.sit.A_comm he hai_mem).inv_right
    have hc2 : Commute e w := (show Commute w e from hwA e he).symm
    have hu₀e : e * (ℓ' * z') = (ℓ' * z') * e := by
      rw [← hdec, hu₀]
      exact (hc1.mul_right hc2).eq
    have hXY : (e * ℓ' * e⁻¹) * (e * z' * e⁻¹) = ℓ' * z' := by
      calc (e * ℓ' * e⁻¹) * (e * z' * e⁻¹) = e * (ℓ' * z') * e⁻¹ := by group
        _ = ℓ' * z' := by rw [hu₀e]; group
    have hXL : e * ℓ' * e⁻¹ ∈ L := (mem_normalizer_iff.mp heL ℓ').mp hℓ'
    have hYC : e * z' * e⁻¹ ∈ centralizer (L : Set G) := conj_mem_centralizer heL hz'
    set ξ : G := ℓ'⁻¹ * (e * ℓ' * e⁻¹) with hξ
    have hξ' : ξ = z' * (e * z' * e⁻¹)⁻¹ := by
      calc ξ = ℓ'⁻¹ * ((e * ℓ' * e⁻¹) * (e * z' * e⁻¹)) * (e * z' * e⁻¹)⁻¹ := by rw [hξ]; group
        _ = z' * (e * z' * e⁻¹)⁻¹ := by rw [hXY]; group
    have hξL : ξ ∈ L := mul_mem (inv_mem hℓ') hXL
    have hξC : ξ ∈ centralizer (L : Set G) := by
      rw [hξ']
      exact mul_mem hz' (inv_mem hYC)
    have hXξ : e * ℓ' * e⁻¹ = ℓ' * ξ := by rw [hξ]; group
    have hℓ'ξ : Commute ℓ' ξ := mem_centralizer_iff.mp hξC ℓ' hℓ'
    have hXp : ∃ k : ℕ, orderOf (e * ℓ' * e⁻¹) = p ^ k := by
      obtain ⟨k, hk⟩ := hℓ'p
      refine ⟨k, ?_⟩
      have := CFSG.RankThree.PGroups.orderOf_inv_mul_mul e⁻¹ ℓ'
      simpa [hk] using this
    have hξp : ∃ k : ℕ, orderOf ξ = p ^ k := by
      have hcomm : Commute ℓ'⁻¹ (e * ℓ' * e⁻¹) := by
        rw [hXξ]
        exact (Commute.mul_right (Commute.refl ℓ') hℓ'ξ).inv_left
      exact pElement_mul_of_commute hp hcomm (pElement_inv hℓ'p) hXp
    have hξ1 : ξ = 1 :=
      eq_one_of_pPart_coprime hp hξp (h.coprime_of_mem_center ξ hξL hξC)
    have : e * ℓ' * e⁻¹ = ℓ' := by rw [hXξ, hξ1, mul_one]
    calc e * ℓ' = (e * ℓ' * e⁻¹) * e := by group
      _ = ℓ' * e := by rw [this]
  have hℓ'E : ℓ' ∈ inSubgroup perfectResidual (L ⊓ centralizer ({a} : Set G)) :=
    hFix G p L a hset (h.sit.pow_eq_one h.sit.a_mem) (h.sit.fieldAutRank h.sit.a_mem) ℓ'
      ⟨hℓ', mem_centralizer_singleton_iff.mpr (hℓ'A a haA).symm⟩ hℓ'p
  have hℓ'ζ : ℓ' * y ^ p = y ^ p * ℓ' := by
    have c1 : Commute (a ^ i)⁻¹ (y ^ p) :=
      (show Commute (a ^ i) (y ^ p) from h.zeta_comm hai_mem).inv_left
    have c2 : Commute w (y ^ p) := hwζ
    have h1 : Commute (ℓ' * z') (y ^ p) := by
      rw [← hdec, hu₀]
      exact c1.mul_left c2
    have h2 : Commute z' (y ^ p) := (mem_centralizer_iff.mp hz' (y ^ p) h.zeta_mem_L).symm
    have : ℓ' = (ℓ' * z') * z'⁻¹ := by group
    rw [this]
    exact (h1.mul_left h2.inv_left).eq
  set n := (Nat.card ↥L).factorization p with hn
  have hZcard' : Nat.card (zpowers (y ^ p)) = p ^ (n - 1) := by
    rw [Nat.card_zpowers, h.orderOf_zeta]
  have hℓ'Z : ℓ' ∈ zpowers (y ^ p) := by
    have hzN : zpowers ℓ' ≤ normalizer (zpowers (y ^ p) : Set G) := by
      refine zpowers_le.mpr (centralizer_le_normalizer _ ?_)
      rw [mem_centralizer_iff]
      intro t ht
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp ht
      exact ((show Commute ℓ' (y ^ p) from hℓ'ζ).zpow_right m).eq.symm
    have hP₁p : IsPGroup p (zpowers ℓ' ⊔ zpowers (y ^ p) : Subgroup G) :=
      (isPGroup_zpowers_of_orderOf hℓ'p).to_sup_of_normal_right'
        (isPGroup_zpowers_of_orderOf ⟨_, h.orderOf_zeta⟩) hzN
    have hP₁L : zpowers ℓ' ⊔ zpowers (y ^ p) ≤ L :=
      sup_le (zpowers_le.mpr hℓ') (zpowers_le.mpr h.zeta_mem_L)
    have hZP₁ : zpowers (y ^ p) ≤ zpowers ℓ' ⊔ zpowers (y ^ p) := le_sup_right
    obtain ⟨k₁, hk₁⟩ := IsPGroup.iff_card.mp hP₁p
    have h1 : p ^ (n - 1) ∣ p ^ k₁ := by
      rw [← hk₁, ← hZcard']
      exact Subgroup.card_dvd_of_le hZP₁
    have h1' : n - 1 ≤ k₁ := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h1
    have h2 : p ^ k₁ ∣ Nat.card ↥L := by
      rw [← hk₁]
      exact Subgroup.card_dvd_of_le hP₁L
    have h2' : k₁ ≤ n :=
      (Nat.Prime.pow_dvd_iff_le_factorization hp Nat.card_pos.ne').mp h2
    by_cases hk : k₁ = n
    · exfalso
      have hSyl : CFSG.ABGLocalTools.IsSylowOf p (zpowers ℓ' ⊔ zpowers (y ^ p)) L :=
        CFSG.ABGLocalTools.isSylowOf_of_card hP₁L (by rw [hk₁, hk])
      have hSc : ∀ x ∈ S, ∀ y' ∈ S, x * y' = y' * x := fun x hx y' hy' =>
        congrArg Subtype.val ((IsCyclic.isMulCommutative (α := S)).is_comm.comm ⟨x, hx⟩ ⟨y', hy'⟩)
      refine not_centralizes_sylow hSL hSyl hSc (h.A_le_normalizer_L haA) (hAS haA) hap
        ⟨y, by rw [← hygen]; exact mem_zpowers y, fun heq => by
          apply h.hy.moves
          have : a * y = y * a := by
            calc a * y = (a * y * a⁻¹) * a := by group
              _ = y * a := by rw [heq]
          calc y * a * y⁻¹ = a * y * y⁻¹ := by rw [this]
            _ = a := by group⟩ ?_
      intro t ht
      have hac : ∀ t ∈ zpowers ℓ' ⊔ zpowers (y ^ p), a * t = t * a := by
        have hle : zpowers ℓ' ⊔ zpowers (y ^ p) ≤ centralizer ({a} : Set G) := by
          refine sup_le ?_ ?_
          · rw [zpowers_le]
            exact mem_centralizer_singleton_iff.mpr (hℓ'A a haA).symm
          · rw [zpowers_le]
            exact mem_centralizer_singleton_iff.mpr (h.zeta_comm haA).symm
        intro t ht
        exact (mem_centralizer_singleton_iff.mp (hle ht)).symm
      calc a * t * a⁻¹ = (t * a) * a⁻¹ := by rw [hac t ht]
        _ = t := by group
    · have hk' : k₁ = n - 1 := by omega
      have heq : zpowers (y ^ p) = zpowers ℓ' ⊔ zpowers (y ^ p) :=
        Subgroup.eq_of_le_of_card_ge hZP₁ (by rw [hk₁, hZcard', hk'])
      rw [heq]
      exact mem_sup_left (mem_zpowers ℓ')
  have hℓ'C : ℓ' ∈ centralizer (A : Set G) := mem_centralizer_iff.mpr hℓ'A
  have hwC : w ∈ centralizer (A : Set G) := mem_centralizer_iff.mpr fun e he => (hwA e he).symm
  have hz'A : z' ∈ centralizer (A : Set G) := by
    have : z' = ℓ'⁻¹ * ((a ^ i)⁻¹ * w) := by rw [← hu₀, hdec]; group
    rw [this]
    refine mul_mem (inv_mem hℓ'C) (mul_mem (inv_mem ?_) hwC)
    exact mem_centralizer_iff.mpr fun e he => h.sit.A_comm he hai_mem
  have hz'c : z' ∈ zpowers c := h.mem_zpowers_c_of_cent hFix hKO hz' hz'A hz'p
  obtain ⟨e, he⟩ := mem_zpowers_iff.mp hℓ'Z
  obtain ⟨t', ht'⟩ := mem_zpowers_iff.mp hz'c
  refine ⟨a ^ i * c ^ t', mul_mem hai_mem (zpow_mem hcA t'), e, ?_⟩
  have hcom : c ^ t' * (y ^ p) ^ e = (y ^ p) ^ e * c ^ t' :=
    (Commute.zpow_zpow (show Commute c (y ^ p) from h.zeta_comm hcA) t' e).eq
  calc w = a ^ i * (ℓ * z) := hwe
    _ = a ^ i * (ℓ' * z') := by rw [hdec]
    _ = a ^ i * ((y ^ p) ^ e * c ^ t') := by rw [← he, ← ht']
    _ = a ^ i * (c ^ t' * (y ^ p) ^ e) := by rw [hcom]
    _ = a ^ i * c ^ t' * (y ^ p) ^ e := by group

end FinalSetup

end Sec11Indeed

end CFSG.RankThree.PartOne
