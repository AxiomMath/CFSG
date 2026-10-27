module

public import CFSG.RankThree.PartOne.S11b.Sec11Five
public import CFSG.RankThree.PartOne.S11d.SitSwap
public import CFSG.RankThree.PartOne.S11d.FiveClaimAux
public import CFSG.RankThree.PartOne.S11d.Facts5
public import CFSG.RankThree.PartOne.S11d.LayerLink
import CFSG.RankThree.PartOne.S12.Sec125Moved
import CFSG.RankThree.PartOne.S10.EmbeddingTransport
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.RankThree.Coprime.ThompsonElementaryComplement
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

namespace Sec11Indeed

theorem fiveClaimCore_of (hS : SchreierFor InCatalog) (h112 : InSec11Two)
    (hK : CatalogPrimeTwoAutomorphismsInner) (h113 : ThreeClaim) (h114 : FourClaim)
    (hGood : LieGoodComponent) (hF2E : FieldFixedTwoElements)
    (hP4a : FieldOnComponentOuter) (hP4b : OutPCyclicTheta) : FiveClaimCore := by
  intro G _ _ p A c L a d sit h3 f hf hf1 R hR hRf
  classical
  have hp := sit.prime
  have hp3 := sit.three_lt
  have hp5 := sit.five_le
  have : Fact p.Prime := ⟨hp⟩
  have hcA := sit.c_mem
  have hdA := sit.d_mem
  have hd1 := sit.d_ne_one
  have hc1 := sit.c_ne_one
  have hAe : IsElementaryAbelian p A := sit.A_elem
  have he : evenRank G ≤ 3 := (sectionTenSetup_evenRank_eq sit.setup).le
  have hcp : c ^ p = 1 := sit.pow_eq_one hcA
  have hdp : d ^ p = 1 := sit.pow_eq_one hdA
  have hfA : f ∈ A := by
    have : zpowers a ⊔ zpowers c ≤ A := sup_le (zpowers_le.mpr sit.a_mem) (zpowers_le.mpr hcA)
    exact this hf
  have hfp : f ^ p = 1 := sit.pow_eq_one hfA
  have hRfW : WitnessAt A c f R := ⟨hRf, hR.ne_bot, hR.two, hR.norm, hR.comm⟩
  obtain ⟨i, j, hij, hi⟩ := sit.exists_coords_of_witness hf hf1 hRfW
  have hfa : InducesFieldAut p f L := hij ▸ sit.inducesFieldAut_mul j hi
  obtain ⟨K, hKmem, hEK, hALK, hRK, hcK⟩ := h114 G p A c L a d sit f hf hf1 R hRfW
  have hKθ : K ∈ thetaComponentsAt p f := hKmem.2
  have hKC : K ≤ centralizer ({f} : Set G) := (mem_thetaComponentsAt_iff.mp hKθ).1
  obtain ⟨hq₀, hAK, -⟩ := moving_maximal_data_at hS sit.setup hKmem.1.1 hfA hf1 hKθ
  obtain ⟨hEvenK, hndvdK, -⟩ := h112 G p A sit.setup f hfA hf1 K hKmem
  have hdL : d ∈ L := sit.d_mem_L
  have hdK : d ∈ K := hALK (Subgroup.mem_inf.mpr ⟨hdA, hdL⟩)
  have hcf : c ∈ centralizer ({f} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact sit.A_comm hcA hfA
  have hcord : ∃ k : ℕ, orderOf c = p ^ k :=
    ⟨1, by rw [pow_one]; exact orderOf_eq_prime hcp hc1⟩
  have hRN : R ≤ normalizer (K : Set G) :=
    commutator_normalizes_thetaComponentsAt he hp hp3 hcf hcord hRf hR.comm.le hKθ
  have hRA : ⁅R, A⁆ = R := by
    refine le_antisymm (Subgroup.le_normalizer_iff_commutator_le_left.mp hR.norm) ?_
    calc R = ⁅R, zpowers c⁆ := hR.comm
      _ ≤ ⁅R, A⁆ := Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hcA)
  have hKnt : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hq₀
  have hmove : ∃ r ∈ R, ∃ k ∈ K, r * k * r⁻¹ ≠ k := by
    by_contra hno
    push Not at hno
    apply (Subgroup.nontrivial_iff_ne_bot K).mp hKnt
    rw [← hRK, eq_bot_iff, Subgroup.commutator_le]
    intro r hr k hk
    rw [commutatorElement_def, Subgroup.mem_bot, hno r hr k hk, mul_inv_cancel]
  have hcat : Catalog (↥K ⧸ Subgroup.center ↥K) := by
    obtain ⟨t, n, f', -, hL⟩ := hEvenK
    exact lieModel_catalog _ t n 2 f' hL
  obtain ⟨t, htmem, ht2⟩ := exists_involution_of_inner_action hp hp3 hK hq₀ hcat
    (IsElementaryAbelian.isPGroup p A) hAK hRN hR.two hR.norm hRA hdK hR.le_cent hmove
  have hsetK : FieldAutSetting p K c :=
    ⟨hp, hp5, hq₀, hEvenK, (Sec9A.evenRank_subgroup_le (K ⊔ zpowers c)).trans he, hndvdK, hcK⟩
  have hcd : c * d = d * c := sit.A_comm hcA hdA
  have hrankK : FieldAutRank p K c :=
    ⟨he, f, mem_centralizer_iff.mpr fun g hg => mem_centralizer_singleton_iff.mp (hKC hg), hf1,
      hfp, sit.A_comm hcA hfA⟩
  have hpK : CFSG.pRank p ↥K = 1 := h113 G p A f K c d (sit.swap h112 hij hi hKmem hALK hcK).2
  obtain ⟨⟨D, hD⟩, hallK, -⟩ :=
    hGood G p K c hsetK hcp hrankK hpK d hdK hd1 hdp hcd ⟨t, htmem, ht2⟩
  obtain ⟨hcDfield, t₁, ht₁, t₂, ht₂, hk₁, hk₂, hnc⟩ := hallK D hD
  have hcD : c ∈ normalizer (D : Set G) := hcDfield.1
  have hDKd : D ≤ K ⊓ centralizer ({d} : Set G) := hD.1
  have hFeq := fixedRes_eq_of_field sit.L_mem.2 hfa hcK hEK hKC
  have hEfLf : inSubgroup perfectResidual (L ⊓ centralizer ({f} : Set G)) ≤
      L ⊓ centralizer ({f} : Set G) := inSubgroup_perfectResidual_le _
  have h2L : ∀ x ∈ D ⊓ centralizer ({c} : Set G), (∃ k : ℕ, orderOf x = 2 ^ k) →
      x ∈ L ⊓ centralizer ({f} : Set G) ⊓ centralizer ({d} : Set G) := by
    intro x hx hxk
    have hxD := (Subgroup.mem_inf.mp hx).1
    have hxK : x ∈ K ⊓ centralizer ({c} : Set G) :=
      Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp (hDKd hxD)).1, (Subgroup.mem_inf.mp hx).2⟩
    have hres := hF2E G p K c hsetK hcp hrankK hpK d hdK hd1 hdp hcd ⟨t, htmem, ht2⟩ x hxK hxk
    rw [hFeq] at hres
    exact Subgroup.mem_inf.mpr ⟨hEfLf hres, (Subgroup.mem_inf.mp (hDKd hxD)).2⟩
  have ht₁L := h2L t₁ ht₁ hk₁
  have hordpos : orderOf t₁ ≠ 0 := (orderOf_pos t₁).ne'
  have h2t₁ : 2 ∣ orderOf t₁ := by
    obtain ⟨k, hk⟩ := hk₁
    rcases k with _ | k
    · exfalso
      apply hnc
      have : t₁ = 1 := orderOf_eq_one_iff.mp (by simpa using hk)
      rw [this, one_mul, mul_one]
    · rw [hk]
      exact dvd_pow_self 2 (Nat.succ_ne_zero k)
  have hx₀L : t₁ ^ (orderOf t₁ / 2) ∈ L ⊓ centralizer ({d} : Set G) := by
    have h1 := Subgroup.mem_inf.mp ht₁L
    have h2 := Subgroup.mem_inf.mp h1.1
    exact Subgroup.mem_inf.mpr ⟨Subgroup.pow_mem _ h2.1 _, Subgroup.pow_mem _ h1.2 _⟩
  have hsetL : FieldAutSetting p L f := sit.fieldAutSetting hfa
  have hfd : f * d = d * f := sit.A_comm hfA hdA
  obtain ⟨-, hallL, hlayL⟩ := hGood G p L f hsetL hfp (sit.fieldAutRank hfA) h3 d
    hdL hd1 hdp hfd ⟨t₁ ^ (orderOf t₁ / 2), hx₀L, orderOf_pow_orderOf_div hordpos h2t₁⟩
  have hDf : D ≤ centralizer ({f} : Set G) := (hD.1.trans inf_le_left).trans hKC
  have hDd : D ≤ centralizer ({d} : Set G) := hD.1.trans inf_le_right
  have hsnD := component_subnormal hKθ hD
  obtain ⟨ID, hID, hDID⟩ := exists_thetaComponent_ge_of_subnormal hS sit.setup hfA hf1 hdA hd1
    hD.2.1 hDf hDd hsnD
  obtain ⟨E, hE, hEID⟩ := exists_component_le_theta (X := L ⊓ centralizer ({d} : Set G)) hp hID hDID
    inf_le_right
    (fun E hE => exists_thetaComponent_ge_of_subnormal hS sit.setup hcA hc1 hdA hd1 hE.2.1
      ((hE.1.trans inf_le_left).trans sit.L_le_centralizer) (hE.1.trans inf_le_right)
      (component_subnormal sit.L_mem.2 hE))
    (Subgroup.mem_inf.mp ht₁).1 (hlayL t₁ ht₁L hk₁) (hlayL t₂ (h2L t₂ ht₂ hk₂) hk₂) hnc
  have hfEfield : FieldLike p f E := (hallL E hE).1
  have hfE : f ∈ normalizer (E : Set G) := hfEfield.1
  have hEc : E ≤ centralizer ({c} : Set G) := (hE.1.trans inf_le_left).trans sit.L_le_centralizer
  have hsnE := component_subnormal sit.L_mem.2 hE
  have hIEd : ID ≤ centralizer ({d} : Set G) := (mem_thetaComponentsAt_iff.mp hID).1
  have hX1 : ID ⊓ centralizer ({c} : Set G) ≤
      centralizer ({c} : Set G) ⊓ centralizer ({d} : Set G) :=
    fun x hx => Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).2, hIEd (Subgroup.mem_inf.mp hx).1⟩
  have hX2 : ID ⊓ centralizer ({f} : Set G) ≤
      centralizer ({f} : Set G) ⊓ centralizer ({d} : Set G) :=
    fun x hx => Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).2, hIEd (Subgroup.mem_inf.mp hx).1⟩
  have hEcomp : IsComponentOf (ID ⊓ centralizer ({c} : Set G)) E :=
    ⟨le_inf hEID hEc, hE.2.1, isSubnormal_subgroupOf_of_le hX1 hsnE⟩
  have hDcomp : IsComponentOf (ID ⊓ centralizer ({f} : Set G)) D :=
    ⟨le_inf hDID hDf, hD.2.1, isSubnormal_subgroupOf_of_le hX2 hsnD⟩
  have hcnf : c ∉ zpowers f := by
    intro hmem
    apply sit.c_not_mem_sup j hi
    rw [← hij]
    exact Subgroup.mem_sup_left hmem
  exact clash_of_components hP4a hP4b sit.setup hdA hd1 hfA hcA hcnf hID hEcomp hDcomp hfE hcD
    hfEfield hcDfield

end Sec11Indeed

end CFSG.RankThree.PartOne
