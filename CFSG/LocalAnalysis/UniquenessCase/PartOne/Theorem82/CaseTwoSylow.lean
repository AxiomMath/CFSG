module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Open.LocalVocabulary
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PGroup.Omega
import CFSG.GroupTheory.PGroup.OmegaComm
import CFSG.GroupTheory.PrimeField.SteinbergBNPowerComparison
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
import CFSG.GroupTheory.PRankCoprimeQuotient
import CFSG.Quasithin.Vol2.Ch11SKFIto
import CFSG.LieType.BorelTits.Basic
import CFSG.RankThree.PartOne.S11d.OutCentral

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem not_dvd_card_center_of_pRank_eq_one {X : Type} [Group X] [Finite X] [Group.IsPerfect X]
    {q : ℕ} [Fact q.Prime] (hq : q ≠ 2)
    (hrank : CFSG.Open.pRank q (⊤ : Subgroup X) = 1) :
    ¬ q ∣ Nat.card (Subgroup.center X) := by
  classical
  have hq' : q.Prime := Fact.out
  intro hdvd
  have hqX : q ∣ Nat.card X := by
    obtain ⟨E, -, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hq'.one_lt (⊤ : Subgroup X)
    rw [hrank, pow_one] at hcard
    exact hcard ▸ Subgroup.card_subgroup_dvd_card E
  obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card' q hdvd
  have hzX : orderOf ((z : Subgroup.center X) : X) = q := by
    rw [← Subgroup.orderOf_mk ((z : Subgroup.center X) : X) z.2]
    exact hzord
  obtain ⟨x, hxq, hxc⟩ :=
    CFSG.Quasithin.Vol2.Ch11.SecS.KF.exists_pow_eq_one_not_mem_center (p := q) hq hqX
  have hx1 : x ≠ 1 := fun h => hxc (h ▸ Subgroup.one_mem _)
  have hxord : orderOf x = q := orderOf_eq_prime hxq hx1
  have hzpow : ((z : Subgroup.center X) : X) ^ q = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hzX]
  have hind : ∀ i j : ℤ,
      ((z : Subgroup.center X) : X) ^ i * x ^ j = 1 → (q : ℤ) ∣ i ∧ (q : ℤ) ∣ j := by
    rintro i j hij
    have hzi : ((z : Subgroup.center X) : X) ^ i ∈ Subgroup.center X :=
      Subgroup.zpow_mem (K := Subgroup.center X) z.2 i
    have hxmem : x ^ j ∈ Subgroup.center X := by
      have h1 : x ^ j = (((z : Subgroup.center X) : X) ^ i)⁻¹ *
          ((((z : Subgroup.center X) : X) ^ i) * x ^ j) := by group
      rw [h1, hij, mul_one]
      exact Subgroup.inv_mem _ hzi
    have hj : (q : ℤ) ∣ j := by
      have hdvd : Nat.gcd q j.natAbs = 1 ∨ Nat.gcd q j.natAbs = q :=
        (Nat.dvd_prime hq').mp (Nat.gcd_dvd_left q j.natAbs)
      rcases hdvd with h1 | hq'
      · exfalso
        have hord : orderOf (x ^ j) = q := by
          rw [orderOf_zpow, hxord, h1, Nat.div_one]
        have hle : Subgroup.zpowers (x ^ j) ≤ Subgroup.zpowers x :=
          Subgroup.zpowers_le.mpr
            (Subgroup.zpow_mem (K := Subgroup.zpowers x) (Subgroup.mem_zpowers x) j)
        have hcen : Subgroup.zpowers (x ^ j) ≤ Subgroup.center X :=
          Subgroup.zpowers_le.mpr hxmem
        have heq : Subgroup.zpowers (x ^ j) = Subgroup.zpowers x := by
          refine Subgroup.eq_of_le_of_card_ge hle ?_
          rw [Nat.card_zpowers, Nat.card_zpowers, hord, hxord]
        have hx2 : x ∈ Subgroup.zpowers (x ^ j) := by
          rw [heq]
          exact Subgroup.mem_zpowers x
        exact hxc (hcen hx2)
      · exact Int.natCast_dvd.mpr (hq' ▸ Nat.gcd_dvd_right q j.natAbs)
    have hxj1 : x ^ j = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one, hxord]
      exact hj
    have hi : (q : ℤ) ∣ i := by
      have hz1 : ((z : Subgroup.center X) : X) ^ i = 1 := by
        rw [hxj1, mul_one] at hij
        exact hij
      rwa [zpow_eq_one_iff_modEq, Int.modEq_zero_iff_dvd, hzX] at hz1
    exact ⟨hi, hj⟩
  have hcomm : Commute ((z : Subgroup.center X) : X) x :=
    (Subgroup.mem_center_iff.mp z.2 x).symm
  have htwo := CFSG.two_le_pRank_of_commute_independent (p := q) hq' hcomm hzpow hxq hind
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top, hrank] at htwo
  omega

structure SylowThreeData (G : Type) [Group G] [Finite G] where
  M : Subgroup G
  Lf : Fin 3 → Subgroup G
  L : Subgroup G
  S : Subgroup G
  hLM : ∀ i, Lf i ≤ M
  hLnorm : ∀ i j, Lf j ≤ Subgroup.normalizer (Lf i : Set G)
  hcomm : ∀ i j, i ≠ j → ⁅Lf i, Lf j⁆ ≤ CFSG.Open.pCoreOf 2 M
  hperf : ∀ i, ⁅Lf i, Lf i⁆ = Lf i
  hrank : ∀ i, CFSG.Open.pRank 3 (Lf i) = 1
  hL : L = Lf 0 ⊔ Lf 1 ⊔ Lf 2
  hS : CFSG.ABGLocalTools.IsSylowOf 3 S L

namespace SylowThreeData

variable (d : SylowThreeData G)

noncomputable def N : Subgroup G := CFSG.Open.pCoreOf 2 d.M

@[expose] def H (i : Fin 3) : Subgroup G := d.S ⊓ d.Lf i

theorem H_def (i : Fin 3) : d.H i = d.S ⊓ d.Lf i := rfl

noncomputable def K (i : Fin 3) : Subgroup G := d.Lf i ⊓ d.N

private theorem N_isPGroup : IsPGroup 2 d.N := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 d.M

private theorem N_normal : d.M ≤ Subgroup.normalizer (d.N : Set G) :=
  CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 d.M

private theorem Lf_le_M (i : Fin 3) : d.Lf i ≤ d.M := d.hLM i

theorem Lf_le_L (i : Fin 3) : d.Lf i ≤ d.L := by
  rw [d.hL]
  fin_cases i
  · exact le_sup_left.trans le_sup_left
  · exact le_sup_right.trans le_sup_left
  · exact le_sup_right

private theorem L_le_normalizer_Lf (i : Fin 3) : d.L ≤ Subgroup.normalizer (d.Lf i : Set G) := by
  rw [d.hL]
  exact sup_le (sup_le (d.hLnorm i 0) (d.hLnorm i 1)) (d.hLnorm i 2)

private theorem L_le_M : d.L ≤ d.M := by
  rw [d.hL]
  exact sup_le (sup_le ((SylowThreeData.Lf_le_M d) 0) ((SylowThreeData.Lf_le_M d) 1))
    ((SylowThreeData.Lf_le_M d) 2)

private theorem S_isPGroup : IsPGroup 3 d.S := d.hS.isPGroup

theorem H_le_Lf (i : Fin 3) : d.H i ≤ d.Lf i := inf_le_right

theorem H_le_S (i : Fin 3) : d.H i ≤ d.S := inf_le_left

private theorem H_isPGroup (i : Fin 3) : IsPGroup 3 (d.H i) :=
  IsPGroup.to_le (SylowThreeData.S_isPGroup d) inf_le_left

theorem isSylowOf_H (i : Fin 3) : CFSG.ABGLocalTools.IsSylowOf 3 (d.H i) (d.Lf i) :=
  CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer d.hS (d.Lf_le_L i)
    ((SylowThreeData.L_le_normalizer_Lf d) i)

theorem isCyclic_H (i : Fin 3) : IsCyclic ↥(d.H i) := by
  have hle : CFSG.pRank 3 ↥(d.Lf i) ≤ 1 := by
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank, d.hrank i]
  exact CFSG.RankThree.PartOne.isCyclic_of_pRank_le_one Nat.prime_three (by norm_num)
    inf_le_right ((SylowThreeData.H_isPGroup d) i) hle

private theorem three_dvd_card_Lf (i : Fin 3) : 3 ∣ Nat.card (d.Lf i) := by
  obtain ⟨E, hE, -, hEcard⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (d.Lf i)
  rw [d.hrank i, pow_one] at hEcard
  have hdvd : Nat.card E ∣ Nat.card (d.Lf i) := by
    have h := Subgroup.card_subgroup_dvd_card (E.subgroupOf (d.Lf i))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv] at h
  exact hEcard ▸ hdvd

theorem H_ne_bot (i : Fin 3) : d.H i ≠ ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hbot
  have hcard := (d.isSylowOf_H i).card_eq
  rw [hbot, Subgroup.card_bot] at hcard
  have hpos : (Nat.card (d.Lf i)).factorization 3 ≠ 0 :=
    (Nat.Prime.factorization_pos_of_dvd Nat.prime_three (Nat.card_pos.ne')
      ((SylowThreeData.three_dvd_card_Lf d) i)).ne'
  have hlt : 1 < 3 ^ (Nat.card (d.Lf i)).factorization 3 := one_lt_pow' (by norm_num) hpos
  omega

private theorem L_le_normalizer_inf_N :
    d.L ≤ Subgroup.normalizer ((d.L ⊓ d.N : Subgroup G) : Set G) :=
  (le_inf Subgroup.le_normalizer
    ((SylowThreeData.L_le_M d).trans (SylowThreeData.N_normal d))).trans
    Subgroup.inf_normalizer_le_normalizer_inf

noncomputable abbrev Kbar : Subgroup ↥(d.L) := (d.L ⊓ d.N).subgroupOf d.L

instance Kbar_normal : d.Kbar.Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_left : d.L ⊓ d.N ≤ d.L)).mpr
    (SylowThreeData.L_le_normalizer_inf_N d)

noncomputable abbrev Q : Type := ↥(d.L) ⧸ d.Kbar

noncomputable abbrev pi : ↥(d.L) →* d.Q := QuotientGroup.mk' d.Kbar

noncomputable abbrev phi (i : Fin 3) : ↥(d.Lf i) →* d.Q :=
  d.pi.comp (Subgroup.inclusion (d.Lf_le_L i))

noncomputable abbrev Lb (i : Fin 3) : Subgroup d.Q := (d.phi i).range

theorem phi_ker (i : Fin 3) : (d.phi i).ker = (d.K i).subgroupOf (d.Lf i) := by
  ext x
  show (d.phi i) x = 1 ↔ (x : G) ∈ d.Lf i ⊓ d.N
  constructor
  · intro hx
    have h := Subgroup.mem_subgroupOf.mp
      ((QuotientGroup.eq_one_iff (Subgroup.inclusion (d.Lf_le_L i) x)).mp hx)
    exact ⟨x.2, h.2⟩
  · intro hx
    exact (QuotientGroup.eq_one_iff (Subgroup.inclusion (d.Lf_le_L i) x)).mpr
      (Subgroup.mem_subgroupOf.mpr (by
        have h : (x : G) ∈ d.L ⊓ d.N := Subgroup.mem_inf.mpr ⟨d.Lf_le_L i x.2, hx.2⟩
        simpa using h))

private theorem Kbar_isPGroup : IsPGroup 2 ↥d.Kbar :=
  (IsPGroup.to_le (SylowThreeData.N_isPGroup d) inf_le_right).of_equiv
    (Subgroup.subgroupOfEquivOfLe inf_le_left).symm

private theorem three_not_dvd_Kbar : ¬ 3 ∣ Nat.card ↥d.Kbar := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := (SylowThreeData.Kbar_isPGroup d).exists_card_eq
  rw [hk]
  intro hdvd
  exact absurd (Nat.prime_three.dvd_of_dvd_pow hdvd) (by norm_num)

theorem ker_phi_isPGroup (i : Fin 3) : IsPGroup 2 ↥((d.phi i).ker) := by
  rw [(SylowThreeData.phi_ker d) i]
  exact (IsPGroup.to_le (SylowThreeData.N_isPGroup d) inf_le_right).of_equiv
    (Subgroup.subgroupOfEquivOfLe inf_le_left).symm

private theorem three_not_dvd_ker_phi (i : Fin 3) : ¬ 3 ∣ Nat.card ↥((d.phi i).ker) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := (SylowThreeData.ker_phi_isPGroup d) i |>.exists_card_eq
  rw [hk]
  intro hdvd
  exact absurd (Nat.prime_three.dvd_of_dvd_pow hdvd) (by norm_num)

theorem isPerfect_Lb (i : Fin 3) : Group.IsPerfect ↥(d.Lb i) := by
  haveI : Group.IsPerfect ↥(d.Lf i) := Subgroup.isPerfect_iff.mpr (d.hperf i)
  exact Group.IsPerfect.ofSurjective (f := (d.phi i).rangeRestrict)
    (d.phi i).rangeRestrict_surjective

theorem pRank_Lb (i : Fin 3) : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(d.Lb i)) = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : CFSG.pRank 3 ↥(d.Lb i) = CFSG.pRank 3 (↥(d.Lf i) ⧸ (d.phi i).ker) :=
    (CFSG.pRank_congr_of_mulEquiv (QuotientGroup.quotientKerEquivRange (d.phi i)) 3).symm
  have h2 : CFSG.pRank 3 (↥(d.Lf i) ⧸ (d.phi i).ker) = CFSG.pRank 3 ↥(d.Lf i) :=
    CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_three _
      ((SylowThreeData.three_not_dvd_ker_phi d) i)
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top, h1, h2,
    CFSG.SectionRank.pRank_coe_eq_openPRank, d.hrank i]

private theorem three_not_dvd_center_Lb (i : Fin 3) :
    ¬ 3 ∣ Nat.card (Subgroup.center ↥(d.Lb i)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := (SylowThreeData.isPerfect_Lb d) i
  exact not_dvd_card_center_of_pRank_eq_one (by norm_num) ((SylowThreeData.pRank_Lb d) i)

private theorem Lb_eq_map (i : Fin 3) : d.Lb i = ((d.Lf i).subgroupOf d.L).map d.pi := by
  rw [SylowThreeData.Lb, SylowThreeData.phi, MonoidHom.range_comp,
    Subgroup.inclusion_range]

private theorem commutator_subgroupOf_le_Kbar (i j : Fin 3) (hij : i ≠ j) :
    ⁅(d.Lf i).subgroupOf d.L, (d.Lf j).subgroupOf d.L⁆ ≤ d.Kbar := by
  show ⁅(d.Lf i).subgroupOf d.L, (d.Lf j).subgroupOf d.L⁆ ≤ (d.L ⊓ d.N).subgroupOf d.L
  rw [Subgroup.commutator_le]
  rintro a ha b hb
  rw [Subgroup.mem_subgroupOf]
  have h1 : ((⁅a, b⁆ : ↥d.L) : G) = ⁅(a : G), (b : G)⁆ :=
    map_commutatorElement d.L.subtype a b
  rw [h1]
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [commutatorElement_def]
    exact d.L.mul_mem (d.L.mul_mem (d.L.mul_mem a.2 b.2) (d.L.inv_mem a.2)) (d.L.inv_mem b.2)
  · exact d.hcomm i j hij (Subgroup.commutator_mem_commutator
      (Subgroup.mem_subgroupOf.mp ha) (Subgroup.mem_subgroupOf.mp hb))

private theorem Lb_comm (i j : Fin 3) (hij : i ≠ j) : ⁅d.Lb i, d.Lb j⁆ = ⊥ := by
  rw [(SylowThreeData.Lb_eq_map d) i, (SylowThreeData.Lb_eq_map d) j, ← Subgroup.map_commutator,
    Subgroup.map_eq_bot_iff,
    QuotientGroup.ker_mk']
  exact (SylowThreeData.commutator_subgroupOf_le_Kbar d) i j hij

theorem Lb_commute (i j : Fin 3) (hij : i ≠ j) {a b : d.Q} (ha : a ∈ d.Lb i)
    (hb : b ∈ d.Lb j) : a * b = b * a := by
  have hcent : d.Lb i ≤ Subgroup.centralizer (d.Lb j : Set d.Q) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp ((SylowThreeData.Lb_comm d) i j hij)
  exact (Subgroup.mem_centralizer_iff.mp (hcent ha) b hb).symm

private theorem Lb_sup : d.Lb 0 ⊔ d.Lb 1 ⊔ d.Lb 2 = ⊤ := by
  have hmap : ((d.Lf 0).subgroupOf d.L ⊔ (d.Lf 1).subgroupOf d.L ⊔
      (d.Lf 2).subgroupOf d.L) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (d.Lf_le_L 0) (d.Lf_le_L 1),
      ← Subgroup.subgroupOf_sup (sup_le (d.Lf_le_L 0) (d.Lf_le_L 1)) (d.Lf_le_L 2), ← d.hL]
    exact Subgroup.subgroupOf_self d.L
  rw [(SylowThreeData.Lb_eq_map d) 0, (SylowThreeData.Lb_eq_map d) 1,
    (SylowThreeData.Lb_eq_map d) 2, ← Subgroup.map_sup, ← Subgroup.map_sup,
    hmap, Subgroup.map_top, MonoidHom.range_eq_top]
  exact QuotientGroup.mk'_surjective _

@[expose] noncomputable def mu : ((↥(d.Lb 0) × ↥(d.Lb 1)) × ↥(d.Lb 2)) →* d.Q :=
  MonoidHom.noncommCoprod
    (MonoidHom.noncommCoprod (Subgroup.subtype (d.Lb 0)) (Subgroup.subtype (d.Lb 1))
      (fun a b => (commute_iff_eq _ _).mpr (d.Lb_commute 0 1 (by decide) a.2 b.2)))
    (Subgroup.subtype (d.Lb 2))
    (fun a b => Commute.mul_left (d.Lb_commute 0 2 (by decide) a.1.2 b.2)
      (d.Lb_commute 1 2 (by decide) a.2.2 b.2))

private theorem mu_range_top : d.mu.range = ⊤ := by
  erw [SylowThreeData.mu, MonoidHom.noncommCoprod_range, MonoidHom.noncommCoprod_range,
    Subgroup.range_subtype, Subgroup.range_subtype, Subgroup.range_subtype, d.Lb_sup]

private theorem three_not_dvd_ker_mu : ¬ 3 ∣ Nat.card ↥d.mu.ker := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h3
  obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hy3 : (y.1 : ((↥(d.Lb 0) × ↥(d.Lb 1)) × ↥(d.Lb 2))) ^ 3 = 1 := by
    have hy3K : (y : d.mu.ker) ^ 3 = 1 := by
      have h := pow_orderOf_eq_one y
      rw [hyord] at h
      exact h
    have h := congrArg (Subgroup.subtype d.mu.ker) hy3K
    simpa using h
  have hxker : (y.1 : ((↥(d.Lb 0) × ↥(d.Lb 1)) × ↥(d.Lb 2))) ∈ d.mu.ker := y.2
  set a : ↥(d.Lb 0) := y.1.1.1 with ha
  set b : ↥(d.Lb 1) := y.1.1.2 with hb
  set c : ↥(d.Lb 2) := y.1.2 with hc
  have ha3 : a ^ 3 = 1 := by
    have h1 := congrArg (fun z : ((↥(d.Lb 0) × ↥(d.Lb 1)) × ↥(d.Lb 2)) => z.1.1) hy3
    simpa [← ha] using h1
  have hb3 : b ^ 3 = 1 := by
    have h1 := congrArg (fun z : ((↥(d.Lb 0) × ↥(d.Lb 1)) × ↥(d.Lb 2)) => z.1.2) hy3
    simpa [← hb] using h1
  have hc3 : c ^ 3 = 1 := by
    have h1 := congrArg (fun z : ((↥(d.Lb 0) × ↥(d.Lb 1)) × ↥(d.Lb 2)) => z.2) hy3
    simpa [← hc] using h1
  have habc : (a : d.Q) * b * c = 1 := by
    rw [MonoidHom.mem_ker] at hxker
    change (y.1.1.1 : d.Q) * (y.1.1.2 : d.Q) * (y.1.2 : d.Q) = 1 at hxker
    rw [← ha, ← hb, ← hc] at hxker
    exact hxker
  have hacent : a ∈ Subgroup.center ↥(d.Lb 0) := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    show (w : d.Q) * (a : d.Q) = (a : d.Q) * (w : d.Q)
    have hb' : Commute (w : d.Q) (b : d.Q) :=
      (d.Lb_commute 0 1 (by decide) w.2 b.2)
    have hc' : Commute (w : d.Q) (c : d.Q) :=
      (d.Lb_commute 0 2 (by decide) w.2 c.2)
    have ha_eq : (a : d.Q) = ((b : d.Q) * (c : d.Q))⁻¹ := by
      rw [← mul_eq_one_iff_eq_inv, ← mul_assoc]
      exact habc
    rw [ha_eq]
    exact ((hb'.mul_right hc').inv_right).eq
  have hbcent : b ∈ Subgroup.center ↥(d.Lb 1) := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    show (w : d.Q) * (b : d.Q) = (b : d.Q) * (w : d.Q)
    have ha' : Commute (w : d.Q) (a : d.Q) :=
      (d.Lb_commute 1 0 (by decide) w.2 a.2)
    have hc' : Commute (w : d.Q) (c : d.Q) :=
      (d.Lb_commute 1 2 (by decide) w.2 c.2)
    have hb_eq : (b : d.Q) = (a : d.Q)⁻¹ * (c : d.Q)⁻¹ := by
      calc (b : d.Q) = (a : d.Q)⁻¹ * ((a : d.Q) * b * c) * (c : d.Q)⁻¹ := by group
        _ = (a : d.Q)⁻¹ * 1 * (c : d.Q)⁻¹ := by rw [habc]
        _ = (a : d.Q)⁻¹ * (c : d.Q)⁻¹ := by group
    rw [hb_eq]
    exact ((ha'.inv_right).mul_right (hc'.inv_right)).eq
  have hccent : c ∈ Subgroup.center ↥(d.Lb 2) := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    show (w : d.Q) * (c : d.Q) = (c : d.Q) * (w : d.Q)
    have ha' : Commute (w : d.Q) (a : d.Q) :=
      (d.Lb_commute 2 0 (by decide) w.2 a.2)
    have hb' : Commute (w : d.Q) (b : d.Q) :=
      (d.Lb_commute 2 1 (by decide) w.2 b.2)
    have hc_eq : (c : d.Q) = ((a : d.Q) * (b : d.Q))⁻¹ :=
      eq_inv_of_mul_eq_one_right habc
    rw [hc_eq]
    exact ((ha'.mul_right hb').inv_right).eq
  have hcop0 : Nat.Coprime (Nat.card (Subgroup.center ↥(d.Lb 0))) 3 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      ((SylowThreeData.three_not_dvd_center_Lb d) 0)).symm
  have hcop1 : Nat.Coprime (Nat.card (Subgroup.center ↥(d.Lb 1))) 3 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      ((SylowThreeData.three_not_dvd_center_Lb d) 1)).symm
  have hcop2 : Nat.Coprime (Nat.card (Subgroup.center ↥(d.Lb 2))) 3 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      ((SylowThreeData.three_not_dvd_center_Lb d) 2)).symm
  have ha1 : a = 1 :=
    CFSG.GroupTheory.PrimeField.eq_one_of_pow_eq_one_of_coprime hacent hcop0 ha3
  have hb1 : b = 1 :=
    CFSG.GroupTheory.PrimeField.eq_one_of_pow_eq_one_of_coprime hbcent hcop1 hb3
  have hc1 : c = 1 :=
    CFSG.GroupTheory.PrimeField.eq_one_of_pow_eq_one_of_coprime hccent hcop2 hc3
  have hy1 : (y : d.mu.ker) = 1 := by
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · refine Prod.ext ?_ ?_
      · rw [← ha]
        simpa using ha1
      · rw [← hb]
        simpa using hb1
    · rw [← hc]
      simpa using hc1
  rw [hy1, orderOf_one] at hyord
  omega

private theorem three_part_L :
    (Nat.card (d.L)).factorization 3 =
      (Nat.card (d.Lf 0)).factorization 3 + (Nat.card (d.Lf 1)).factorization 3 +
        (Nat.card (d.Lf 2)).factorization 3 := by
  have h1 : (Nat.card ↥(d.L)).factorization 3 = (Nat.card d.Q).factorization 3 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup d.Kbar,
      Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'),
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd
        (SylowThreeData.three_not_dvd_Kbar d), add_zero]
  have h2 : (Nat.card ((↥(d.Lb 0) × ↥(d.Lb 1)) × ↥(d.Lb 2))).factorization 3
      = (Nat.card d.Q).factorization 3 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup d.mu.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange d.mu).toEquiv,
      (SylowThreeData.mu_range_top d), Subgroup.card_top,
      Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'),
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd
        (SylowThreeData.three_not_dvd_ker_mu d), add_zero]
  have h3 : (Nat.card ((↥(d.Lb 0) × ↥(d.Lb 1)) × ↥(d.Lb 2))).factorization 3
      = (Nat.card ↥(d.Lb 0)).factorization 3 + (Nat.card ↥(d.Lb 1)).factorization 3 +
        (Nat.card ↥(d.Lb 2)).factorization 3 := by
    rw [Nat.card_prod, Nat.card_prod,
      Nat.factorization_mul (a := Nat.card ↥(d.Lb 0) * Nat.card ↥(d.Lb 1))
        (b := Nat.card ↥(d.Lb 2)) (mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne')
        (Nat.card_pos.ne'),
      Nat.factorization_mul (a := Nat.card ↥(d.Lb 0)) (b := Nat.card ↥(d.Lb 1))
        (Nat.card_pos.ne') (Nat.card_pos.ne'), Finsupp.add_apply, Finsupp.add_apply]
  have h4 : ∀ i : Fin 3,
      (Nat.card ↥(d.Lb i)).factorization 3 = (Nat.card (d.Lf i)).factorization 3 := by
    intro i
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (d.phi i).ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange (d.phi i)).toEquiv,
      Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'),
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd
        ((SylowThreeData.three_not_dvd_ker_phi d) i),
      add_zero]
  rw [h1, ← h2, h3, h4 0, h4 1, h4 2]

private theorem S_inf_N : d.S ⊓ d.N = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (IsPGroup.disjoint_of_ne 3 2 (by norm_num) d.S d.N (SylowThreeData.S_isPGroup d)
    (SylowThreeData.N_isPGroup d)).eq_bot

private theorem H_commute (i j : Fin 3) (hij : i ≠ j) {a b : G} (ha : a ∈ d.H i) (hb : b ∈ d.H j) :
    a * b = b * a := by
  have hmem : ⁅a, b⁆ ∈ d.S ⊓ d.N := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact d.S.mul_mem (d.S.mul_mem (d.S.mul_mem (d.H_le_S i ha) (d.H_le_S j hb))
        (d.S.inv_mem (d.H_le_S i ha))) (d.S.inv_mem (d.H_le_S j hb))
    · exact d.hcomm i j hij (Subgroup.commutator_mem_commutator
        ((SylowThreeData.H_le_Lf d) i ha) ((SylowThreeData.H_le_Lf d) j hb))
  rw [(SylowThreeData.S_inf_N d)] at hmem
  exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hmem)

theorem H_commute_incl (i j : Fin 3) (hij : i ≠ j) (a : ↥(d.H i)) (b : ↥(d.H j)) :
    Commute (Subgroup.inclusion (d.H_le_S i) a) (Subgroup.inclusion (d.H_le_S j) b) := by
  apply Subtype.ext
  show (a : G) * (b : G) = (b : G) * (a : G)
  exact (SylowThreeData.H_commute d) i j hij a.2 b.2

instance Lb_normal (i : Fin 3) : (d.Lb i).Normal := by
  rw [(SylowThreeData.Lb_eq_map d) i]
  exact ((Subgroup.normal_subgroupOf_iff_le_normalizer (d.Lf_le_L i)).mpr
    ((SylowThreeData.L_le_normalizer_Lf d) i)).map d.pi (QuotientGroup.mk'_surjective _)

theorem eq_one_of_mem_Lf_of_mem_sup {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {x : G} (hxS : x ∈ d.S) (hxi : x ∈ d.Lf i) (hxjk : x ∈ d.Lf j ⊔ d.Lf k) : x = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxL : x ∈ d.L := d.Lf_le_L i hxi
  set xbar : d.Q := d.pi ⟨x, hxL⟩ with hxbar
  have hmem_i : xbar ∈ d.Lb i := ⟨⟨x, hxi⟩, rfl⟩
  have hmem_jk : xbar ∈ d.Lb j ⊔ d.Lb k := by
    have h : (⟨x, hxL⟩ : ↥d.L) ∈ (d.Lf j ⊔ d.Lf k).subgroupOf d.L := by
      rw [Subgroup.mem_subgroupOf]
      exact hxjk
    have h' : xbar ∈ ((d.Lf j ⊔ d.Lf k).subgroupOf d.L).map d.pi :=
      Subgroup.mem_map_of_mem d.pi h
    rwa [Subgroup.subgroupOf_sup (d.Lf_le_L j) (d.Lf_le_L k), Subgroup.map_sup,
      ← (SylowThreeData.Lb_eq_map d) j, ← (SylowThreeData.Lb_eq_map d) k] at h'
  have hcent : d.Lb j ⊔ d.Lb k ≤ Subgroup.centralizer (d.Lb i : Set d.Q) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_sup_right,
      (SylowThreeData.Lb_comm d) j i hij.symm, (SylowThreeData.Lb_comm d) k i hik.symm]
    simp
  have hxbar_cent : (⟨xbar, hmem_i⟩ : ↥(d.Lb i)) ∈ Subgroup.center ↥(d.Lb i) := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hcent hmem_jk) (w : d.Q) w.2
  obtain ⟨m, hm⟩ := (SylowThreeData.S_isPGroup d) ⟨x, hxS⟩
  have hm' : x ^ (3 ^ m) = 1 := by
    have h := congrArg Subtype.val hm
    simpa using h
  have hm'' : (⟨x, hxL⟩ : ↥d.L) ^ (3 ^ m) = 1 := by
    apply Subtype.ext
    simpa using hm'
  have hpow : (⟨xbar, hmem_i⟩ : ↥(d.Lb i)) ^ (3 ^ m) = 1 := by
    apply Subtype.ext
    show xbar ^ (3 ^ m) = (1 : d.Q)
    rw [show xbar = d.pi ⟨x, hxL⟩ from rfl, ← map_pow, hm'', map_one]
  have hcop : Nat.Coprime (Nat.card (Subgroup.center ↥(d.Lb i))) (3 ^ m) :=
    Nat.Coprime.pow_right m (((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      ((SylowThreeData.three_not_dvd_center_Lb d) i)).symm)
  have h1 : (⟨xbar, hmem_i⟩ : ↥(d.Lb i)) = 1 :=
    CFSG.GroupTheory.PrimeField.eq_one_of_pow_eq_one_of_coprime hxbar_cent hcop hpow
  have hxN : x ∈ d.N := by
    have h2 : xbar = 1 := congrArg Subtype.val h1
    have h3 : (⟨x, hxL⟩ : ↥d.L) ∈ d.Kbar := (QuotientGroup.eq_one_iff (⟨x, hxL⟩ : ↥d.L)).mp h2
    exact (Subgroup.mem_subgroupOf.mp h3).2
  have hmem : x ∈ d.S ⊓ d.N := Subgroup.mem_inf.mpr ⟨hxS, hxN⟩
  rw [(SylowThreeData.S_inf_N d)] at hmem
  exact Subgroup.mem_bot.mp hmem

@[expose] noncomputable def nu : ((↥(d.H 0) × ↥(d.H 1)) × ↥(d.H 2)) →* ↥d.S :=
  MonoidHom.noncommCoprod
    (MonoidHom.noncommCoprod (Subgroup.inclusion (d.H_le_S 0)) (Subgroup.inclusion (d.H_le_S 1))
      (fun a b => d.H_commute_incl 0 1 (by decide) a b))
    (Subgroup.inclusion (d.H_le_S 2))
    (fun a b => (d.H_commute_incl 0 2 (by decide) a.1 b).mul_left
      (d.H_commute_incl 1 2 (by decide) a.2 b))

private theorem nu_apply (a : ↥(d.H 0)) (b : ↥(d.H 1)) (c : ↥(d.H 2)) :
    ((d.nu ((a, b), c) : ↥d.S) : G) = (a : G) * (b : G) * (c : G) := rfl

private theorem nu_injective : Function.Injective d.nu := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  rintro ⟨⟨a, b⟩, c⟩ habc
  have hprod : (a : G) * (b : G) * (c : G) = 1 := by
    rw [← (SylowThreeData.nu_apply d) a b c]
    exact congrArg Subtype.val habc
  have ha_eq : (a : G) = ((b : G) * (c : G))⁻¹ := by
    rw [← mul_eq_one_iff_eq_inv, ← mul_assoc]
    exact hprod
  have ha_1 : (a : G) = 1 := by
    refine d.eq_one_of_mem_Lf_of_mem_sup (i := 0) (j := 1) (k := 2) (by decide) (by decide)
      (by decide) ?_ ((SylowThreeData.H_le_Lf d) 0 a.2) ?_
    · exact d.H_le_S 0 a.2
    · rw [ha_eq]
      exact Subgroup.inv_mem _ (Subgroup.mul_mem_sup ((SylowThreeData.H_le_Lf d) 1 b.2)
        ((SylowThreeData.H_le_Lf d) 2 c.2))
  have hbc : (b : G) * (c : G) = 1 := by
    have h := hprod
    rw [ha_1, one_mul] at h
    exact h
  have hb_eq : (b : G) = (c : G)⁻¹ := by
    rw [← mul_eq_one_iff_eq_inv]
    exact hbc
  have hb_1 : (b : G) = 1 := by
    refine d.eq_one_of_mem_Lf_of_mem_sup (i := 1) (j := 2) (k := 0) (by decide) (by decide)
      (by decide) ?_ ((SylowThreeData.H_le_Lf d) 1 b.2) ?_
    · exact d.H_le_S 1 b.2
    · rw [hb_eq]
      exact Subgroup.inv_mem _ (Subgroup.mem_sup_left ((SylowThreeData.H_le_Lf d) 2 c.2))
  have hc_1 : (c : G) = 1 := by
    rw [hb_1, one_mul] at hbc
    exact hbc
  exact Subgroup.mem_bot.mpr (Prod.ext (Prod.ext (Subtype.ext ha_1) (Subtype.ext hb_1))
    (Subtype.ext hc_1))

private theorem card_H_mul_card_H_mul_card_H :
    Nat.card ↥(d.H 0) * Nat.card ↥(d.H 1) * Nat.card ↥(d.H 2) = Nat.card ↥d.S := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [d.hS.card_eq, (SylowThreeData.three_part_L d), (d.isSylowOf_H 0).card_eq,
    (d.isSylowOf_H 1).card_eq,
    (d.isSylowOf_H 2).card_eq, pow_add, pow_add]

private theorem nu_range_top : d.nu.range = ⊤ := by
  have hinj := (SylowThreeData.nu_injective d)
  have hcard : Nat.card ((↥(d.H 0) × ↥(d.H 1)) × ↥(d.H 2)) = Nat.card ↥d.S := by
    rw [Nat.card_prod, Nat.card_prod, (SylowThreeData.card_H_mul_card_H_mul_card_H d)]
  have hrange : Nat.card ↥d.nu.range = Nat.card ↥d.S := by
    rw [← hcard]
    exact Nat.card_congr (Equiv.ofInjective d.nu hinj).symm
  exact Subgroup.eq_top_of_card_eq _ hrange

theorem S_eq_sup : d.S = d.H 0 ⊔ d.H 1 ⊔ d.H 2 := by
  refine le_antisymm ?_ (sup_le (sup_le (d.H_le_S 0) (d.H_le_S 1)) (d.H_le_S 2))
  intro s hs
  have hs' : (⟨s, hs⟩ : ↥d.S) ∈ d.nu.range := by
    rw [(SylowThreeData.nu_range_top d)]
    exact Subgroup.mem_top _
  obtain ⟨⟨⟨a, b⟩, c⟩, hx⟩ := hs'
  have hval : (a : G) * (b : G) * (c : G) = s := by
    rw [← (SylowThreeData.nu_apply d) a b c]
    exact congrArg Subtype.val hx
  rw [← hval]
  exact Subgroup.mul_mem_sup (Subgroup.mul_mem_sup a.2 b.2) c.2

private theorem nu_surjective : Function.Surjective d.nu :=
  MonoidHom.range_eq_top.mp (SylowThreeData.nu_range_top d)

theorem S_commute : ∀ a b : G, a ∈ d.S → b ∈ d.S → a * b = b * a := by
  let e : ((↥(d.H 0) × ↥(d.H 1)) × ↥(d.H 2)) ≃* ↥d.S :=
    MulEquiv.ofBijective d.nu ⟨(SylowThreeData.nu_injective d), (SylowThreeData.nu_surjective d)⟩
  haveI : IsMulCommutative ↥(d.H 0) := (d.isCyclic_H 0).isMulCommutative
  haveI : IsMulCommutative ↥(d.H 1) := (d.isCyclic_H 1).isMulCommutative
  haveI : IsMulCommutative ↥(d.H 2) := (d.isCyclic_H 2).isMulCommutative
  have key : ∀ x y : ((↥(d.H 0) × ↥(d.H 1)) × ↥(d.H 2)), x * y = y * x :=
    fun x y => (inferInstance : IsMulCommutative _).is_comm.comm x y
  intro a b ha hb
  have h1 : (⟨a, ha⟩ : ↥d.S) = e (e.symm ⟨a, ha⟩) := (MulEquiv.apply_symm_apply e _).symm
  have h2 : (⟨b, hb⟩ : ↥d.S) = e (e.symm ⟨b, hb⟩) := (MulEquiv.apply_symm_apply e _).symm
  have h3 : (⟨a, ha⟩ : ↥d.S) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := by
    rw [h1, h2, ← map_mul, key, map_mul, h2, h1]
  exact congrArg Subtype.val h3

@[expose] noncomputable def A (i : Fin 3) : Subgroup G :=
  (CFSG.omega₁ ↥(d.H i) (p := 3)).map (d.H i).subtype

theorem A_def (i : Fin 3) :
    d.A i = (CFSG.omega₁ ↥(d.H i) (p := 3)).map (d.H i).subtype := rfl

@[expose] noncomputable def AA : Subgroup G := d.A 0 ⊔ d.A 1 ⊔ d.A 2

theorem AA_def : d.AA = d.A 0 ⊔ d.A 1 ⊔ d.A 2 := rfl

theorem A_le_H (i : Fin 3) : d.A i ≤ d.H i := Subgroup.map_subtype_le _

theorem A_le_S (i : Fin 3) : d.A i ≤ d.S := (d.A_le_H i).trans (d.H_le_S i)

theorem A_le_L (i : Fin 3) : d.A i ≤ d.L :=
  (d.A_le_H i).trans ((SylowThreeData.H_le_Lf d) i |>.trans (d.Lf_le_L i))

theorem AA_le_S : d.AA ≤ d.S :=
  sup_le (sup_le ((SylowThreeData.A_le_S d) 0) ((SylowThreeData.A_le_S d) 1))
    ((SylowThreeData.A_le_S d) 2)

theorem AA_le_L : d.AA ≤ d.L :=
  sup_le (sup_le ((SylowThreeData.A_le_L d) 0) ((SylowThreeData.A_le_L d) 1))
    ((SylowThreeData.A_le_L d) 2)

private theorem H_comm (i : Fin 3) : ∀ a b : ↥(d.H i), a * b = b * a := fun a b => by
  haveI : IsMulCommutative ↥(d.H i) := (d.isCyclic_H i).isMulCommutative
  exact IsMulCommutative.is_comm.comm a b

theorem mem_A_iff (i : Fin 3) {x : G} : x ∈ d.A i ↔ x ∈ d.H i ∧ x ^ 3 = 1 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    have h := (CFSG.mem_omega₁_iff_of_comm (p := 3) ((SylowThreeData.H_comm d) i)).mp hy
    simpa using congrArg (Subgroup.subtype (d.H i)) h
  · rintro ⟨hxH, hx3⟩
    exact Subgroup.mem_map_of_mem _ (Subgroup.subset_closure (show
      (⟨x, hxH⟩ : ↥(d.H i)) ∈ {y : ↥(d.H i) | y ^ (3 ^ 1) = 1} from by
        simpa [pow_one] using hx3))

private theorem three_dvd_card_H (i : Fin 3) : 3 ∣ Nat.card ↥(d.H i) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [(d.isSylowOf_H i).card_eq]
  exact dvd_pow_self 3 (Nat.Prime.factorization_pos_of_dvd Nat.prime_three
    (Nat.card_pos.ne') ((SylowThreeData.three_dvd_card_Lf d) i)).ne'

theorem card_A (i : Fin 3) : Nat.card (d.A i) = 3 := by
  haveI := d.isCyclic_H i
  rw [d.A_def i, Subgroup.card_map_of_injective (Subgroup.subtype_injective (d.H i)),
    CFSG.card_omega₁_of_isCyclic (p := 3)]
  exact Nat.gcd_eq_right ((SylowThreeData.three_dvd_card_H d) i)

@[expose] noncomputable def prodIncl : ((↥(d.A 0) × ↥(d.A 1)) × ↥(d.A 2)) →*
    ((↥(d.H 0) × ↥(d.H 1)) × ↥(d.H 2)) :=
  MonoidHom.prodMap
    (MonoidHom.prodMap (Subgroup.inclusion (d.A_le_H 0)) (Subgroup.inclusion (d.A_le_H 1)))
    (Subgroup.inclusion (d.A_le_H 2))

private theorem prodIncl_injective : Function.Injective d.prodIncl := by
  erw [SylowThreeData.prodIncl]
  exact Function.Injective.prodMap
    (Function.Injective.prodMap (Subgroup.inclusion_injective (d.A_le_H 0))
      (Subgroup.inclusion_injective (d.A_le_H 1)))
    (Subgroup.inclusion_injective (d.A_le_H 2))

@[expose] noncomputable def nuA : ((↥(d.A 0) × ↥(d.A 1)) × ↥(d.A 2)) →* ↥d.S :=
  d.nu.comp d.prodIncl

private theorem nuA_apply (a : ↥(d.A 0)) (b : ↥(d.A 1)) (c : ↥(d.A 2)) :
    ((d.nuA ((a, b), c) : ↥d.S) : G) = (a : G) * (b : G) * (c : G) := by
  have h : d.prodIncl ((a, b), c) = ((⟨(a : G), d.A_le_H 0 a.2⟩, ⟨(b : G), d.A_le_H 1 b.2⟩),
      ⟨(c : G), d.A_le_H 2 c.2⟩) := rfl
  show ((d.nu (d.prodIncl ((a, b), c)) : ↥d.S) : G) = (a : G) * (b : G) * (c : G)
  rw [h, (SylowThreeData.nu_apply d)]

private theorem nuA_apply' (x : ((↥(d.A 0) × ↥(d.A 1)) × ↥(d.A 2))) :
    ((d.nuA x : ↥d.S) : G) = (x.1.1 : G) * (x.1.2 : G) * (x.2 : G) := by
  obtain ⟨⟨a, b⟩, c⟩ := x
  exact (SylowThreeData.nuA_apply d) a b c

private theorem nuA_injective : Function.Injective d.nuA :=
  (SylowThreeData.nu_injective d).comp (SylowThreeData.prodIncl_injective d)

private theorem nuA_range : d.nuA.range.map (Subgroup.subtype d.S) = d.AA := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, rfl⟩ := hy
    rw [show d.S.subtype (d.nuA x) = (x.1.1 : G) * (x.1.2 : G) * (x.2 : G) from
      (SylowThreeData.nuA_apply' d) x]
    refine d.AA.mul_mem (d.AA.mul_mem ?_ ?_) ?_
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left x.1.1.2)
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right x.1.2.2)
    · exact Subgroup.mem_sup_right x.2.2
  · refine sup_le (sup_le ?_ ?_) ?_
    · rintro a ha
      have hx : (⟨a, (SylowThreeData.A_le_S d) 0 ha⟩ : ↥d.S) ∈ d.nuA.range := by
        refine ⟨((⟨a, ha⟩, 1), 1), ?_⟩
        apply Subtype.ext
        rw [(SylowThreeData.nuA_apply d)]
        simp
      exact Subgroup.mem_map_of_mem (Subgroup.subtype d.S) hx
    · rintro b hb
      have hx : (⟨b, (SylowThreeData.A_le_S d) 1 hb⟩ : ↥d.S) ∈ d.nuA.range := by
        refine ⟨((1, ⟨b, hb⟩), 1), ?_⟩
        apply Subtype.ext
        rw [(SylowThreeData.nuA_apply d)]
        simp
      exact Subgroup.mem_map_of_mem (Subgroup.subtype d.S) hx
    · rintro c hc
      have hx : (⟨c, (SylowThreeData.A_le_S d) 2 hc⟩ : ↥d.S) ∈ d.nuA.range := by
        refine ⟨((1, 1), ⟨c, hc⟩), ?_⟩
        apply Subtype.ext
        rw [(SylowThreeData.nuA_apply d)]
        simp
      exact Subgroup.mem_map_of_mem (Subgroup.subtype d.S) hx

theorem card_AA : Nat.card d.AA = 27 := by
  have h1 : Nat.card d.AA = Nat.card ↥d.nuA.range := by
    rw [← (SylowThreeData.nuA_range d),
      Subgroup.card_map_of_injective (Subgroup.subtype_injective d.S)]
  rw [h1]
  have h2 : Nat.card ↥d.nuA.range = Nat.card ((↥(d.A 0) × ↥(d.A 1)) × ↥(d.A 2)) :=
    Nat.card_congr (Equiv.ofInjective d.nuA (SylowThreeData.nuA_injective d)).symm
  rw [h2, Nat.card_prod, Nat.card_prod, (SylowThreeData.card_A d) 0,
    (SylowThreeData.card_A d) 1, (SylowThreeData.card_A d) 2]

private theorem mem_AA_iff {x : G} : x ∈ d.AA ↔ x ∈ d.S ∧ x ^ 3 = 1 := by
  constructor
  · intro hx
    refine ⟨(SylowThreeData.AA_le_S d) hx, ?_⟩
    rw [← (SylowThreeData.nuA_range d), Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨z, rfl⟩ := hy
    rw [show d.S.subtype (d.nuA z) = (z.1.1 : G) * (z.1.2 : G) * (z.2 : G) from
      (SylowThreeData.nuA_apply' d) z]
    have h0 : (z.1.1 : G) ^ 3 = 1 := (((SylowThreeData.mem_A_iff d) 0).mp z.1.1.2).2
    have h1 : (z.1.2 : G) ^ 3 = 1 := (((SylowThreeData.mem_A_iff d) 1).mp z.1.2.2).2
    have h2 : (z.2 : G) ^ 3 = 1 := (((SylowThreeData.mem_A_iff d) 2).mp z.2.2).2
    have c01 : Commute (z.1.1 : G) (z.1.2 : G) :=
      d.S_commute _ _ ((SylowThreeData.A_le_S d) 0 z.1.1.2) ((SylowThreeData.A_le_S d) 1 z.1.2.2)
    have c2 : Commute ((z.1.1 : G) * z.1.2) (z.2 : G) :=
      Commute.mul_left (d.S_commute _ _ ((SylowThreeData.A_le_S d) 0 z.1.1.2)
        ((SylowThreeData.A_le_S d) 2 z.2.2))
        (d.S_commute _ _ ((SylowThreeData.A_le_S d) 1 z.1.2.2) ((SylowThreeData.A_le_S d) 2 z.2.2))
    rw [c2.mul_pow, c01.mul_pow, h0, h1, h2, one_mul, mul_one]
  · rintro ⟨hxS, hx3⟩
    obtain ⟨z, hz⟩ := (SylowThreeData.nu_surjective d) ⟨x, hxS⟩
    have hx_eq : (x : G) = (z.1.1 : G) * (z.1.2 : G) * (z.2 : G) := by
      have h := congrArg Subtype.val hz
      rw [(SylowThreeData.nu_apply d)] at h
      exact h.symm
    have c01 : Commute (z.1.1 : G) (z.1.2 : G) :=
      d.S_commute _ _ (d.H_le_S 0 z.1.1.2) (d.H_le_S 1 z.1.2.2)
    have c2 : Commute ((z.1.1 : G) * z.1.2) (z.2 : G) :=
      Commute.mul_left (d.S_commute _ _ (d.H_le_S 0 z.1.1.2) (d.H_le_S 2 z.2.2))
        (d.S_commute _ _ (d.H_le_S 1 z.1.2.2) (d.H_le_S 2 z.2.2))
    have hcube : d.nu ((z.1.1 ^ 3, z.1.2 ^ 3), z.2 ^ 3) = 1 := by
      apply Subtype.ext
      rw [(SylowThreeData.nu_apply d)]
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [← Commute.mul_pow c01, ← Commute.mul_pow c2, ← hx_eq]
      exact hx3
    have hone : ((z.1.1 ^ 3, z.1.2 ^ 3), z.2 ^ 3) =
        (1 : ((↥(d.H 0) × ↥(d.H 1)) × ↥(d.H 2))) :=
      (SylowThreeData.nu_injective d) (by rw [hcube, map_one])
    have h0 : (z.1.1 : G) ^ 3 = 1 := congrArg (fun w => (w.1.1 : G)) hone
    have h1 : (z.1.2 : G) ^ 3 = 1 := congrArg (fun w => (w.1.2 : G)) hone
    have h2 : (z.2 : G) ^ 3 = 1 := congrArg (fun w => (w.2 : G)) hone
    have hm0 : (z.1.1 : G) ∈ d.A 0 := ((SylowThreeData.mem_A_iff d) 0).mpr ⟨z.1.1.2, h0⟩
    have hm1 : (z.1.2 : G) ∈ d.A 1 := ((SylowThreeData.mem_A_iff d) 1).mpr ⟨z.1.2.2, h1⟩
    have hm2 : (z.2 : G) ∈ d.A 2 := ((SylowThreeData.mem_A_iff d) 2).mpr ⟨z.2.2, h2⟩
    rw [hx_eq]
    exact Subgroup.mul_mem_sup (Subgroup.mul_mem_sup hm0 hm1) hm2

theorem isElemAbelian_AA : CFSG.Open.IsElemAbelian 3 d.AA := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ((SylowThreeData.mem_AA_iff d).mp hx).2⟩
  exact Subtype.ext (d.S_commute a b ((SylowThreeData.AA_le_S d) a.2)
    ((SylowThreeData.AA_le_S d) b.2))

theorem mem_AA_of_pow_eq_one {x : G} (hxS : x ∈ d.S) (hx3 : x ^ 3 = 1) : x ∈ d.AA :=
  (SylowThreeData.mem_AA_iff d).mpr ⟨hxS, hx3⟩

theorem isCyclic_A (i : Fin 3) : IsCyclic ↥(d.A i) := by
  haveI : IsCyclic ↥(d.H i) := d.isCyclic_H i
  exact Subgroup.isCyclic_of_le (H := d.A i) (H' := d.H i) (d.A_le_H i)

theorem centralizes_A_of_isPGroup {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (i : Fin 3) {x : G}
    (hx : IsPGroup q (Subgroup.zpowers x))
    (hxS : x ∈ Subgroup.normalizer (d.S : Set G))
    (hxL : x ∈ Subgroup.normalizer (d.Lf i : Set G)) :
    ∀ a ∈ d.A i, x * a = a * x := by
  have hxH : x ∈ Subgroup.normalizer (d.H i : Set G) := by
    rw [d.H_def i]
    refine Subgroup.mem_normalizer_iff.mpr fun y => ?_
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨(Subgroup.mem_normalizer_iff.mp hxS y).mp h.1,
      (Subgroup.mem_normalizer_iff.mp hxL y).mp h.2⟩,
      fun h => ⟨(Subgroup.mem_normalizer_iff.mp hxS y).mpr h.1,
      (Subgroup.mem_normalizer_iff.mp hxL y).mpr h.2⟩⟩
  haveI : (CFSG.omega₁ ↥(d.H i) (p := 3)).Characteristic := CFSG.omega₁_characteristic ↥(d.H i)
  have hxA : x ∈ Subgroup.normalizer (d.A i : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := d.H i) (K := CFSG.omega₁ ↥(d.H i) (p := 3)) hxH
  obtain ⟨k, hk⟩ := hx ⟨x, Subgroup.mem_zpowers x⟩
  have hxqk : x ^ (q ^ k) = 1 := by
    have h := congrArg Subtype.val hk
    simpa using h
  have hcard_mulAut : Nat.card (MulAut ↥(d.A i)) = 2 := by
    haveI := (SylowThreeData.isCyclic_A d) i
    rw [IsCyclic.card_mulAut, (SylowThreeData.card_A d) i,
      Nat.totient_prime (by norm_num : Nat.Prime 3)]
  have hone : (Subgroup.normalizerMonoidHom (d.A i)) ⟨x, hxA⟩ = 1 := by
    have hdiv1 : orderOf ((Subgroup.normalizerMonoidHom (d.A i)) ⟨x, hxA⟩) ∣ q ^ k := by
      refine (orderOf_map_dvd _ _).trans (orderOf_dvd_of_pow_eq_one ?_)
      exact Subtype.ext hxqk
    have hdiv2 : orderOf ((Subgroup.normalizerMonoidHom (d.A i)) ⟨x, hxA⟩) ∣ 2 := by
      have h := orderOf_dvd_natCard ((Subgroup.normalizerMonoidHom (d.A i)) ⟨x, hxA⟩)
      rwa [hcard_mulAut] at h
    have hq2' : ¬ q ∣ 2 := fun h =>
      hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h)
    have hcop : Nat.Coprime (q ^ k) 2 :=
      Nat.Coprime.pow_left k ((hq.coprime_iff_not_dvd).mpr hq2')
    refine orderOf_eq_one_iff.mp (Nat.dvd_one.mp ?_)
    have h := Nat.dvd_gcd hdiv1 hdiv2
    rwa [hcop.gcd_eq_one] at h
  have hxker : (⟨x, hxA⟩ : ↥(Subgroup.normalizer (d.A i : Set G))) ∈
      (Subgroup.normalizerMonoidHom (d.A i)).ker := by
    rw [MonoidHom.mem_ker, hone]
  rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hxker
  intro a ha
  exact (Subgroup.mem_centralizer_iff.mp hxker a ha).symm

theorem centralizes_AA_of_isPGroup {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {x : G}
    (hx : IsPGroup q (Subgroup.zpowers x))
    (hxS : x ∈ Subgroup.normalizer (d.S : Set G))
    (hxL : ∀ i, x ∈ Subgroup.normalizer (d.Lf i : Set G)) :
    ∀ a ∈ d.AA, x * a = a * x := by
  have hsub : d.AA ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [d.AA_def]
    refine sup_le (sup_le ?_ ?_) ?_
    · intro b hb
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((d.centralizes_A_of_isPGroup hq hq2 0 hx hxS (hxL 0) b hb).symm)
    · intro b hb
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((d.centralizes_A_of_isPGroup hq hq2 1 hx hxS (hxL 1) b hb).symm)
    · intro b hb
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((d.centralizes_A_of_isPGroup hq hq2 2 hx hxS (hxL 2) b hb).symm)
  intro a ha
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hsub ha)).symm

theorem threeElement_centralizes_A (i : Fin 3) {x : G}
    (hx : IsPGroup 3 (Subgroup.zpowers x))
    (hxS : x ∈ Subgroup.normalizer (d.S : Set G))
    (hxL : x ∈ Subgroup.normalizer (d.Lf i : Set G)) :
    ∀ a ∈ d.A i, x * a = a * x :=
  d.centralizes_A_of_isPGroup Nat.prime_three (by norm_num) i hx hxS hxL

theorem threeElement_centralizes_AA {x : G} (hx : IsPGroup 3 (Subgroup.zpowers x))
    (hxS : x ∈ Subgroup.normalizer (d.S : Set G))
    (hxL : ∀ i, x ∈ Subgroup.normalizer (d.Lf i : Set G)) :
    ∀ a ∈ d.AA, x * a = a * x :=
  d.centralizes_AA_of_isPGroup Nat.prime_three (by norm_num) hx hxS hxL

end SylowThreeData

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
