module

public import CFSG.RankThree.PartOne.S11d.Facts3
public import CFSG.RankThree.PartOne.S11d.SitSwap
public import CFSG.RankThree.PartOne.S11d.FiveClaimAux
import CFSG.RankThree.Coprime.InvolutionFixedRankBound
import CFSG.RankThree.Coprime.ThompsonElementaryComplement
import CFSG.RankThree.PartOne.S10.AmbientTheta
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
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.Blueprint CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement
open CFSG.Assembly.RankThreeEven (localRank)

namespace Sec11Indeed

variable {G : Type} [Group G] [Finite G]

theorem one_le_pRank_of_mem {p : ℕ} (hp : p.Prime) {X : Subgroup G} {x : G} (hx : x ∈ X)
    (hx1 : x ≠ 1) (hxp : x ^ p = 1) : 1 ≤ CFSG.pRank p ↥X := by
  have : Fact p.Prime := ⟨hp⟩
  set x' : ↥X := ⟨x, hx⟩
  have hx'p : x' ^ p = 1 := Subtype.ext (by simpa using hxp)
  have hx'1 : x' ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hel : IsElementaryAbelian p (zpowers x') := IsElementaryAbelian.zpowers_of_pow_eq_one hx'p
  have hcard : Nat.card (zpowers x') = p ^ 1 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx'p hx'1, pow_one]
  exact CFSG.RankThree.Coprime.le_pRank_of_isElementaryAbelian hp.one_lt hel hcard

theorem threeClaim_of (hS : SchreierFor InCatalog) (h112 : InSec11Two) (h114 : FourClaim)
    (hT : ThreeComponents) (hP4a : FieldOnComponentOuter)
    (hP4b : OutPCyclicTheta) : ThreeClaim := by
  intro G _ _ p A c L a d sit
  classical
  by_contra hne
  have hp := sit.prime
  have : Fact p.Prime := ⟨hp⟩
  have hcA := sit.c_mem
  have hdA := sit.d_mem
  have hd1 := sit.d_ne_one
  have hdL : d ∈ L := sit.d_mem_L
  have hdp : d ^ p = 1 := sit.pow_eq_one hdA
  have hcp : c ^ p = 1 := sit.pow_eq_one hcA
  have h1le : 1 ≤ CFSG.pRank p ↥L := one_le_pRank_of_mem hp hdL hd1 hdp
  have h2 : 2 ≤ CFSG.pRank p ↥L := by omega
  have hAe : IsElementaryAbelian p A := sit.A_elem
  have hAcard : Nat.card A = p ^ 3 := sit.setup.2.2.2.2.2.2.2.1
  obtain ⟨H, hHidx, S, hS1, hS2, hSA, hSc, hSH⟩ :=
    exists_hyperplane_witness sit.setup hcA sit.c_ne_one
  have hexp : ∀ x : A, x ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p A)
  let : CommGroup A := IsMulCommutative.instCommGroup
  have hgen := sup_eq_top_of_sup_eq sit.a_mem hcA hdA sit.A_eq.symm
  obtain ⟨x, hxP, hxH, hx1⟩ := exists_ne_one_mem_sup_inf hAcard hexp _ _ _ hgen H hHidx
  obtain ⟨u, hu, v, hv, rfl⟩ := Subgroup.mem_sup.mp hxP
  obtain ⟨i₀, rfl⟩ := mem_zpowers_iff.mp hu
  obtain ⟨j₀, rfl⟩ := mem_zpowers_iff.mp hv
  have hf : a ^ i₀ * c ^ j₀ ∈ zpowers a ⊔ zpowers c :=
    Subgroup.mul_mem_sup (zpow_mem (mem_zpowers a) _) (zpow_mem (mem_zpowers c) _)
  have hf1 : a ^ i₀ * c ^ j₀ ≠ 1 := fun h => hx1 (Subtype.ext (by simpa using h))
  have hSf : S ≤ centralizer ({a ^ i₀ * c ^ j₀} : Set G) := by
    have := hSH _ hxH
    simpa using this
  have hRfW : WitnessAt A c (a ^ i₀ * c ^ j₀) S := ⟨hSf, hS1, hS2, hSA, hSc⟩
  obtain ⟨i, j, hij, hi⟩ := sit.exists_coords_of_witness hf hf1 hRfW
  set f : G := a ^ i₀ * c ^ j₀
  have hfA : f ∈ A := by
    rw [hij]
    exact mul_mem (zpow_mem sit.a_mem i) (zpow_mem hcA j)
  have hfp : f ^ p = 1 := sit.pow_eq_one hfA
  have hfd : f * d = d * f := sit.A_comm hfA hdA
  have hfc : f ∈ zpowers c → False := fun h => sit.not_mem_zpowers_c_of_coords hij hi h
  obtain ⟨K, hKmem, hEK, hALK, hRK, hcK⟩ := h114 G p A c L a d sit f hf hf1 S hRfW
  obtain ⟨hAK, sit'⟩ := sit.swap h112 hij hi hKmem hALK hcK
  have hfL : InducesFieldAut p f L := hij ▸ sit.inducesFieldAut_mul j hi
  have hset₁ : FieldAutSetting p L f := sit.fieldAutSetting hfL
  have hset₂ : FieldAutSetting p K c := sit'.fieldAutSetting hcK
  have hKθ : K ∈ thetaComponentsAt p f := hKmem.2
  have hKC : K ≤ centralizer ({f} : Set G) := (mem_thetaComponentsAt_iff.mp hKθ).1
  have hEeq := fixedRes_eq_of_field sit.L_mem.2 hfL hcK hEK hKC
  have hdK : d ∈ K := hALK ⟨hdA, hdL⟩
  have hcd : c * d = d * c := sit.A_comm hcA hdA
  have hlr₁ : localRank p ↥(L ⊔ zpowers f) ≤ 2 := (sit.replace_a hij hi).localRank_le_two
  have hlr₂ : localRank p ↥(K ⊔ zpowers c) ≤ 2 := sit'.localRank_le_two
  obtain ⟨-, S₁, hS₁L, hS₁1, hS₁2, hAS₁, -⟩ := sit.L_mem.1.1.1
  obtain ⟨-, S₂, hS₂K, hS₂1, hS₂2, hAS₂, -⟩ := hKmem.1.1.1
  obtain ⟨K₁, K₂, hK₁, hK₂, hfK₁, hcK₂, hfield₁, hfield₂, hov⟩ :=
    hT G p L K f c hset₁ hset₂ (sit.fieldAutRank hfA)
    (sit'.fieldAutRank hcA) hfp hcp h2 hlr₁ hlr₂ hEeq.symm d hdL hdK hd1 hdp hfd hcd
    ⟨S₁, hS₁L, hS₁1, hS₁2, hAS₁ hfA, hAS₁ hdA⟩ ⟨S₂, hS₂K, hS₂1, hS₂2, hAS₂ hcA, hAS₂ hdA⟩
  have hK₁c : K₁ ≤ centralizer ({c} : Set G) :=
    (hK₁.1.trans inf_le_left).trans sit.L_le_centralizer
  have hK₁d : K₁ ≤ centralizer ({d} : Set G) := hK₁.1.trans inf_le_right
  have hK₂f : K₂ ≤ centralizer ({f} : Set G) := (hK₂.1.trans inf_le_left).trans hKC
  have hK₂d : K₂ ≤ centralizer ({d} : Set G) := hK₂.1.trans inf_le_right
  have hsn₁ := component_subnormal sit.L_mem.2 hK₁
  have hsn₂ := component_subnormal hKθ hK₂
  obtain ⟨I₁, hI₁, hK₁I₁⟩ := exists_thetaComponent_ge_of_subnormal hS sit.setup hcA sit.c_ne_one
    hdA hd1 hK₁.2.1 hK₁c hK₁d hsn₁
  obtain ⟨I₂, hI₂, hK₂I₂⟩ := exists_thetaComponent_ge_of_subnormal hS sit.setup hfA hf1 hdA hd1
    hK₂.2.1 hK₂f hK₂d hsn₂
  have hIeq : I₁ = I₂ := thetaComponent_eq_of_overlap hp hI₁ hI₂ hK₁.2.1 hK₁I₁ hK₂I₂ hov
  have hK₂I : K₂ ≤ I₁ := hIeq ▸ hK₂I₂
  have hI₁d : I₁ ≤ centralizer ({d} : Set G) := (mem_thetaComponentsAt_iff.mp hI₁).1
  have hX₁ : I₁ ⊓ centralizer ({c} : Set G) ≤
      centralizer ({c} : Set G) ⊓ centralizer ({d} : Set G) :=
    fun y hy => Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hy).2, hI₁d (Subgroup.mem_inf.mp hy).1⟩
  have hX₂ : I₁ ⊓ centralizer ({f} : Set G) ≤
      centralizer ({f} : Set G) ⊓ centralizer ({d} : Set G) :=
    fun y hy => Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hy).2, hI₁d (Subgroup.mem_inf.mp hy).1⟩
  have hcomp₁ : IsComponentOf (I₁ ⊓ centralizer ({c} : Set G)) K₁ :=
    ⟨le_inf hK₁I₁ hK₁c, hK₁.2.1, isSubnormal_subgroupOf_of_le hX₁ hsn₁⟩
  have hcomp₂ : IsComponentOf (I₁ ⊓ centralizer ({f} : Set G)) K₂ :=
    ⟨le_inf hK₂I hK₂f, hK₂.2.1, isSubnormal_subgroupOf_of_le hX₂ hsn₂⟩
  exact clash_of_components hP4a hP4b sit.setup hdA hd1 hcA hfA hfc hI₁ hcomp₂ hcomp₁ hcK₂ hfK₁
    hfield₂ hfield₁

end Sec11Indeed

end CFSG.RankThree.PartOne
