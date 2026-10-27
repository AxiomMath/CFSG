module

public import CFSG.RankThree.PartOne.S11d.FinalKey
public import CFSG.RankThree.PartOne.S11d.FinalPigeonhole
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents
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

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.Blueprint CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement Pointwise

namespace Sec11Indeed

variable {G : Type} [Group G] [Finite G]

theorem isTransv_of_data {A : Subgroup G} {d g : G} (hdA : d ∈ A) (hgd : g * d * g⁻¹ = d)
    (hge : ∀ e ∈ A, g * e * g⁻¹ * e⁻¹ ∈ zpowers d) : Transv.IsTransv A d g where
  norm := by
    refine mem_normalizer_of_conj_subset fun e he => ?_
    have := hge e he
    have h2 : g * e * g⁻¹ = (g * e * g⁻¹ * e⁻¹) * e := by group
    rw [h2]
    exact mul_mem ((zpowers_le.mpr hdA) this) he
  cent := by
    calc g * d = (g * d * g⁻¹) * g := by group
      _ = d * g := by rw [hgd]
  comm e he := hge e he

theorem isTransv_of_mem_centralizer {A : Subgroup G} {d g : G} (hdA : d ∈ A)
    (hg : g ∈ centralizer (A : Set G)) : Transv.IsTransv A d g := by
  refine isTransv_of_data hdA ?_ fun e he => ?_
  · have := mem_centralizer_iff.mp hg d hdA
    calc g * d * g⁻¹ = (d * g) * g⁻¹ := by rw [← this]
      _ = d := by group
  · have := mem_centralizer_iff.mp hg e he
    have h1 : g * e * g⁻¹ * e⁻¹ = 1 := by
      calc g * e * g⁻¹ * e⁻¹ = (e * g) * g⁻¹ * e⁻¹ := by rw [← this]
        _ = 1 := by group
    rw [h1]
    exact one_mem _

namespace FinalSetup

variable {p : ℕ} {A : Subgroup G} {c : G} {L : Subgroup G} {a d : G} {K : Subgroup G} {x y : G}

theorem zeta_mem_E (hFix : FieldFixedPElements)
    (h : FinalSetup p A c L a d K x y) :
    y ^ p ∈ inSubgroup perfectResidual (L ⊓ centralizer ({a} : Set G)) :=
  hFix G p L a (h.sit.fieldAutSetting h.sit.a_field) (h.sit.pow_eq_one h.sit.a_mem)
    (h.sit.fieldAutRank h.sit.a_mem) (y ^ p)
    ⟨h.zeta_mem_L, mem_centralizer_singleton_iff.mpr (h.zeta_comm h.sit.a_mem).symm⟩
    ⟨_, h.orderOf_zeta⟩

theorem exists_type_element (h112 : InSec11Two) (hKF : KF128Rank1)
    (h113 : ThreeClaim) (h114 : FourClaim) (h115 : FiveClaim) (hFix : FieldFixedPElements)
    (h : FinalSetup p A c L a d K x y) (j : ℤ) :
    ∃ g : G, Transv.IsTransv A d g ∧ g * y ^ p = y ^ p * g ∧
      orderOf g = p ^ (Nat.card ↥L).factorization p ∧ g ^ p ∈ zpowers (y ^ p) ∧
      Transv.lam g (a * c ^ j) = 1 ∧ Transv.lam g c ≠ 1 := by
  have hp := h.prime
  have hp5 := h.sit.five_le
  have : Fact p.Prime := ⟨hp⟩
  have hcA := h.sit.c_mem
  have hdA := h.sit.d_mem
  set f : G := a * c ^ j with hf
  have hij : f = a ^ (1 : ℤ) * c ^ j := by rw [hf, zpow_one]
  have hi : ¬ (p : ℤ) ∣ 1 := by
    intro hdvd
    have := Int.eq_one_of_dvd_one (by positivity) hdvd
    have : p = 1 := by exact_mod_cast this
    exact hp.one_lt.ne' this
  have hfA : f ∈ A := by
    rw [hf]
    exact mul_mem h.sit.a_mem (zpow_mem hcA j)
  have hf1 : f ≠ 1 := h.sit.ne_one_of_coords hij hi
  have sitj : Sit p A c L f d := h.sit.replace_a hij hi
  obtain ⟨R, hR⟩ := h115 G p A c L f d sitj h.rank
  obtain ⟨K', hK'mem, hE', hALK', -, hcK'⟩ :=
    h114 G p A c L f d sitj f (mem_sup_left (mem_zpowers f)) hf1 R hR
  obtain ⟨hAK', sit''⟩ := h.sit.swap h112 hij hi hK'mem hALK' hcK'
  have hK'F : K' ∈ thetaComponentFamily p A :=
    mem_thetaComponentFamily_iff.mpr ⟨f, hfA, hf1, hK'mem.2⟩
  have hAK'N : A ≤ normalizer (K' : Set G) :=
    selected_prime_elements_normalize_theta_components.2 G h.evenRank_le p hp h.sit.three_lt A
      h.sit.A_elem K' hK'F
  have hK'C : K' ≤ centralizer ({f} : Set G) := (mem_thetaComponentsAt_iff.mp hK'mem.2).1
  have hdK' : d ∈ K' := hALK' ⟨hdA, h.sit.d_mem_L⟩
  have hrank' : CFSG.pRank p ↥K' ≤ 1 := (h113 G p A f K' c d sit'').le
  have hqK' : CFSG.IsQuasisimple ↥K' := sit''.L_isQuasisimple
  have hevK' : evenRank ↥K' ≤ 3 := (Sec9A.evenRank_subgroup_le K').trans h.evenRank_le
  obtain ⟨-, S₂, hS₂K, hS₂1, hS₂2, hAS₂, -⟩ := hK'mem.1.1.1
  obtain ⟨x', hx'K, hx'p, hx'd, hx'c, hx'e⟩ := hKF G p K' A c d hp hp5 hqK' sit''.even hevK' hrank'
    sit''.p_ndvd h.sit.A_elem hAK'N hcA hdA hdK' h.sit.d_ne_one hcK'
    ⟨S₂, hS₂K, hS₂1, hS₂2, hAS₂ hcA, hAS₂ hdA⟩
  have hTv : Transv.IsTransv A d x' := isTransv_of_data hdA hx'd hx'e
  have : IsElementaryAbelian p A := h.sit.A_elem
  obtain ⟨S', hS', -, -, hAS', hgen', hord', hn2'⟩ := exists_sylow_of_transvection hp h.p_ne_two
    hrank' hAK'N (IsElementaryAbelian.isPGroup p A) hx'K hx'p hTv.norm hcA
    (h.sit.pow_eq_one hcA) (fun heq => by
      apply hx'c
      have : c * x' = x' * c := by
        calc c * x' = (c * x' * c⁻¹) * c := by group
          _ = x' * c := by rw [heq]
      calc x' * c * x'⁻¹ = c * x' * x'⁻¹ := by rw [this]
        _ = c := by group)
  set n := (Nat.card ↥L).factorization p with hn
  have hx'pc : x' ^ p ∈ centralizer (A : Set G) :=
    Transv.pow_mem_centralizer (h.sit.pow_eq_one hdA) hTv
  have hsetK' : FieldAutSetting p K' c := sit''.fieldAutSetting hcK'
  have hfL : InducesFieldAut p f L := hij ▸ h.sit.inducesFieldAut_mul j hi
  have hEeq := fixedRes_eq_of_field h.sit.L_mem.2 hfL hcK' hE' hK'C
  have hxp_cK : x' ^ p ∈ centralizer ({c} : Set G) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hx'pc c hcA).symm
  have hx'E : x' ^ p ∈ inSubgroup perfectResidual (K' ⊓ centralizer ({c} : Set G)) :=
    hFix G p K' c hsetK' (sit''.pow_eq_one hcA) (sit''.fieldAutRank hcA) (x' ^ p)
      ⟨K'.pow_mem hx'K p, hxp_cK⟩ (pElement_pow hp hx'p p)
  have hlcj : ∀ l ∈ L, l * c ^ j = c ^ j * l := fun l hl =>
    mem_centralizer_iff.mp (h.sit.zpow_c_mem_centralizer j) l hl
  have hEa : inSubgroup perfectResidual (L ⊓ centralizer ({f} : Set G)) =
      inSubgroup perfectResidual (L ⊓ centralizer ({a} : Set G)) := by
    have hsub : L ⊓ centralizer ({f} : Set G) = L ⊓ centralizer ({a} : Set G) := by
      ext l
      simp only [mem_inf, mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨hl, hlf⟩
        refine ⟨hl, ?_⟩
        have hlf' : l * (a * c ^ j) = a * c ^ j * l := hlf
        calc l * a = (l * (a * c ^ j)) * (c ^ j)⁻¹ := by group
          _ = (a * c ^ j * l) * (c ^ j)⁻¹ := by rw [hlf']
          _ = a * (c ^ j * l) * (c ^ j)⁻¹ := by group
          _ = a * (l * c ^ j) * (c ^ j)⁻¹ := by rw [← hlcj l hl]
          _ = a * l := by group
      · rintro ⟨hl, hla⟩
        refine ⟨hl, ?_⟩
        show l * (a * c ^ j) = a * c ^ j * l
        calc l * (a * c ^ j) = (l * a) * c ^ j := by group
          _ = (a * l) * c ^ j := by rw [hla]
          _ = a * (l * c ^ j) := by group
          _ = a * (c ^ j * l) := by rw [hlcj l hl]
          _ = a * c ^ j * l := by group
    rw [hsub]
  rw [hEeq, hEa] at hx'E
  have hyE := h.zeta_mem_E hFix
  have hvp' : (Nat.card ↥K').factorization p = n := by
    obtain ⟨SL, hSL, -, -, hASL, hyL, -, -⟩ := h.sylow_L
    have hEa' : inSubgroup perfectResidual (L ⊓ centralizer ({a} : Set G)) ≤
        centralizer ({a} : Set G) := (inSubgroup_perfectResidual_le _).trans inf_le_right
    have hEL' : inSubgroup perfectResidual (L ⊓ centralizer ({a} : Set G)) ≤ L :=
      (inSubgroup_perfectResidual_le _).trans inf_le_left
    have hSL' : CFSG.ABGLocalTools.IsSylowOf p (zpowers y) L := by
      rw [hyL]
      exact hSL
    have hSK' : CFSG.ABGLocalTools.IsSylowOf p (zpowers x') K' := by
      rw [hgen']
      exact hS'
    have hmoveL : a * y * a⁻¹ ≠ y := by
      intro heq
      apply h.hy.moves
      have : a * y = y * a := by
        calc a * y = (a * y * a⁻¹) * a := by group
          _ = y * a := by rw [heq]
      calc y * a * y⁻¹ = a * y * y⁻¹ := by rw [this]
        _ = a := by group
    have hmoveK : c * x' * c⁻¹ ≠ x' := by
      intro heq
      apply hx'c
      have : c * x' = x' * c := by
        calc c * x' = (c * x' * c⁻¹) * c := by group
          _ = x' * c := by rw [heq]
      calc x' * c * x'⁻¹ = c * x' * x'⁻¹ := by rw [this]
        _ = c := by group
    exact (factorization_eq_of_common_fixed hSL' hSK' h.sit.a_field.1 hcK'.1
      (by rw [hyL]; exact hASL h.sit.a_mem) (by rw [hgen']; exact hAS' hcA)
      (h.sit.pow_eq_one h.sit.a_mem) (h.sit.pow_eq_one hcA) hmoveL hmoveK hEL' (hEa ▸ hE')
      (fun e he => by rw [← mem_centralizer_singleton_iff.mp (hEa' he)]; group)
      (fun e he => by rw [← h.sit.comm_c_L (hEL' he)]; group) hyE hx'E).symm
  rw [hvp'] at hord' hn2'
  set H : Subgroup G := inSubgroup perfectResidual (L ⊓ centralizer ({a} : Set G)) ⊓
    centralizer ({d} : Set G) with hH
  have hEL : inSubgroup perfectResidual (L ⊓ centralizer ({a} : Set G)) ≤ L :=
    (inSubgroup_perfectResidual_le _).trans inf_le_left
  have hHcyc : ∀ P : Subgroup G, P ≤ H → IsPGroup p P → IsCyclic P := fun P hPH hPp =>
    isCyclic_of_pRank_le_one hp h.p_ne_two (hPH.trans (inf_le_left.trans hEL)) hPp h.rank.le
  have hyH : y ^ p ∈ H := ⟨hyE, mem_centralizer_singleton_iff.mpr (h.zeta_comm hdA).symm⟩
  have hxH : x' ^ p ∈ H :=
    ⟨hx'E, mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hx'pc d hdA).symm⟩
  have hordx : orderOf (x' ^ p) = p ^ (n - 1) := orderOf_pow_prime_of_eq hp (by omega) hord'
  obtain ⟨g, hgH, hgz⟩ := exists_conj_zpowers_eq hp hHcyc hyH hxH ⟨_, h.orderOf_zeta⟩
    (pElement_pow hp hx'p p) (by rw [h.orderOf_zeta, hordx])
  have hgL : g ∈ L := hEL hgH.1
  have hga : g * a = a * g := mem_centralizer_singleton_iff.mp ((inSubgroup_perfectResidual_le _
    hgH.1).2)
  have hgd : g * d = d * g := mem_centralizer_singleton_iff.mp hgH.2
  have hgc : g * c = c * g := h.sit.comm_c_L hgL
  have hgA : ∀ e ∈ A, e * g = g * e := by
    intro e he
    obtain ⟨i, j', k, rfl⟩ := h.sit.exists_zpow_coords he
    have c1 : Commute g a := hga
    have c2 : Commute g c := hgc
    have c3 : Commute g d := hgd
    exact (((c1.zpow_right i).mul_right (c2.zpow_right j')).mul_right (c3.zpow_right k)).symm.eq
  have hgT : Transv.IsTransv A d g := isTransv_of_mem_centralizer hdA (mem_centralizer_iff.mpr hgA)
  set g₀ : G := g * x' * g⁻¹ with hg₀
  have hg₀T : Transv.IsTransv A d g₀ := (hgT.mul hTv).mul hgT.inv
  have hlam : ∀ e ∈ A, Transv.lam g₀ e = Transv.lam x' e := fun e he => Transv.lam_conj hTv hgT he
  have hg₀p : g₀ ^ p = g * x' ^ p * g⁻¹ := conj_pow
  have hzg : zpowers (g₀ ^ p) = zpowers (y ^ p) := by rw [hg₀p]; exact hgz
  have hcommζ : g₀ * y ^ p = y ^ p * g₀ := by
    obtain ⟨s, hs⟩ := mem_zpowers_iff.mp (show y ^ p ∈ zpowers (g₀ ^ p) by
      rw [hzg]; exact mem_zpowers _)
    rw [← hs]
    exact (((Commute.refl g₀).pow_right p).zpow_right s).eq
  have horder : orderOf g₀ = p ^ n := by
    have := CFSG.RankThree.PGroups.orderOf_inv_mul_mul g⁻¹ x'
    simpa [hord'] using this
  have hx'f : x' * f = f * x' := mem_centralizer_singleton_iff.mp (hK'C hx'K)
  refine ⟨g₀, hg₀T, hcommζ, horder, by rw [← hzg]; exact mem_zpowers _, ?_, ?_⟩
  · rw [hlam _ (by rw [hf]; exact mul_mem h.sit.a_mem (zpow_mem hcA j))]
    simp only [Transv.lam]
    rw [hx'f]
    group
  · rw [hlam c hcA]
    intro h1
    apply hx'c
    simp only [Transv.lam] at h1
    calc x' * c * x'⁻¹ = (x' * c * x'⁻¹ * c⁻¹) * c := by group
      _ = c := by rw [h1, one_mul]

end FinalSetup

open FinalSetup in
theorem finalSetup_false (h112 : InSec11Two) (hKF : KF128Rank1) (h113 : ThreeClaim) (h114 : FourClaim) (h115 : FiveClaim)
    (hFix : FieldFixedPElements) (hKO : OutPCyclic) {p : ℕ} {A : Subgroup G} {c : G}
    {L : Subgroup G} {a d : G} {K : Subgroup G} {x y : G}
    (h : FinalSetup p A c L a d K x y) : False := by
  have hp := h.prime
  have hdA := h.sit.d_mem
  have hcA := h.sit.c_mem
  have haA := h.sit.a_mem
  obtain ⟨S, -, -, -, -, -, hyord, hn2⟩ := h.sylow_L
  set n := (Nat.card ↥L).factorization p with hn
  choose gj hgjT hgjζ hgjord hgjp hgj1 hgj2 using fun j : ℤ =>
    exists_type_element h112 hKF h113 h114 h115 hFix h j
  have hn' : n = n - 1 + 1 := by omega
  refine false_of_transvection_types hp h.sit.five_le (A := A)
    (fun e he f hf => h.sit.A_comm he hf) (fun e he => h.sit.pow_eq_one he) hdA h.sit.d_ne_one
    haA hcA (fun e he => h.sit.exists_zpow_coords he) (m := n - 1) (by omega) h.orderOf_zeta
    h.d_mem_zpowers_zeta (fun e he => h.zeta_comm he)
    (fun w hwA hwζ hwp => h.pElement_mem_A_zeta hFix hKO hwA hwζ hwp) y h.isTransv_y
    (((Commute.refl y).pow_right p).eq) (by rw [hyord, ← hn']) (mem_zpowers _) ?_ ?_ gj hgjT
    hgjζ (fun j => by rw [hgjord j, ← hn']) hgjp hgj1 hgj2
  · simp only [Transv.lam]
    rw [h.sit.comm_c_L h.hy.mem]
    group
  · intro h1
    simp only [Transv.lam] at h1
    apply h.hy.moves
    calc y * a * y⁻¹ = (y * a * y⁻¹ * a⁻¹) * a := by group
      _ = a := by rw [h1, one_mul]

theorem finalClaim_of (h112 : InSec11Two) (hKF : KF128Rank1) (h113 : ThreeClaim) (h114 : FourClaim) (h115 : FiveClaim)
    (hFix : FieldFixedPElements) (hKO : OutPCyclic) : FinalClaim := by
  intro G _ _ p A c L a d sit K x y hK hE hALK hAK hcK h3 hx hy
  exfalso
  have hi : ¬ (p : ℤ) ∣ 1 := by
    intro hdvd
    have := Int.eq_one_of_dvd_one (by positivity) hdvd
    have : p = 1 := by exact_mod_cast this
    exact sit.prime.one_lt.ne' this
  obtain ⟨-, sit'⟩ := sit.swap h112 (show a = a ^ (1 : ℤ) * c ^ (0 : ℤ) by simp) hi hK hALK hcK
  exact finalSetup_false h112 hKF h113 h114 h115 hFix hKO
    ⟨sit, sit', hE, hALK, h3, h113 G p A a K c d sit', hx, hy⟩

end Sec11Indeed

end CFSG.RankThree.PartOne
