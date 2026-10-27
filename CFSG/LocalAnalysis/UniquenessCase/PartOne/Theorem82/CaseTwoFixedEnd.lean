module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CenterNine
public import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.GroupTheory.PrimeField.SteinbergBNPowerComparison
import CFSG.Quasithin.EmptyFaithful.S151cOrbit
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorSupLeOfCommutatorLeAndNormalize
import CFSG.GroupTheory.PRankCoprimeQuotient
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Diag.Fixed
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSylow
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CComponents
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace SylowThreeData

variable (d : SylowThreeData G)

theorem isElemAbelian_A_sup_A (i j : Fin 3) : CFSG.Open.IsElemAbelian 3 (d.A i ⊔ d.A j) := by
  have hAi : CFSG.Open.IsElemAbelian 3 (d.A i) :=
    ⟨⟨⟨fun x y => Subtype.ext (d.S_commute x y (d.A_le_S i x.2) (d.A_le_S i y.2))⟩⟩,
      fun x hx => ((d.mem_A_iff i).mp hx).2⟩
  have hAj : CFSG.Open.IsElemAbelian 3 (d.A j) :=
    ⟨⟨⟨fun x y => Subtype.ext (d.S_commute x y (d.A_le_S j x.2) (d.A_le_S j y.2))⟩⟩,
      fun x hx => ((d.mem_A_iff j).mp hx).2⟩
  exact CFSG.Open.IsElemAbelian.sup_of_commute hAi hAj
    (fun x hx y hy => d.S_commute x y (d.A_le_S i hx) (d.A_le_S j hy))

theorem card_A_sup_A {i j : Fin 3} (hij : i ≠ j) :
    Nat.card ↥(d.A i ⊔ d.A j) = 3 ^ 2 := by
  obtain ⟨k, hik, hjk⟩ : ∃ k : Fin 3, i ≠ k ∧ j ≠ k := by
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact ⟨2, by decide, by decide⟩
    · exact ⟨1, by decide, by decide⟩
    · exact ⟨2, by decide, by decide⟩
    · exact (hij rfl).elim
    · exact ⟨0, by decide, by decide⟩
    · exact ⟨1, by decide, by decide⟩
    · exact ⟨0, by decide, by decide⟩
    · exact (hij rfl).elim
  have hcomm : ∀ x ∈ d.A i, ∀ y ∈ d.A j, x * y = y * x :=
    fun x hx y hy => d.S_commute x y (d.A_le_S i hx) (d.A_le_S j hy)
  obtain ⟨hcard, -⟩ :=
    CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (d.A i) (d.A j) hcomm
  have hinf : d.A i ⊓ d.A j = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    exact d.eq_one_of_mem_Lf_of_mem_sup hij hik hjk (d.A_le_S i hx.1)
      (((d.A_le_H i).trans (d.H_le_Lf i)) hx.1)
      (Subgroup.mem_sup_left (((d.A_le_H j).trans (d.H_le_Lf j)) hx.2))
  rw [hinf, d.card_A i, d.card_A j, Subgroup.card_bot, mul_one] at hcard
  simpa [pow_two] using hcard

theorem AA_le_inf_centralizer {P : Subgroup G} (hP3 : IsPGroup 3 P) (hSP : d.S ≤ P)
    (hPS : P ≤ Subgroup.normalizer (d.S : Set G))
    (hPn : ∀ i, P ≤ Subgroup.normalizer (d.Lf i : Set G)) :
    d.AA ≤ P ⊓ Subgroup.centralizer (P : Set G) := by
  refine le_inf ((SylowThreeData.AA_le_S d).trans hSP) ?_
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hx3 : IsPGroup 3 (Subgroup.zpowers x) := hP3.to_le (Subgroup.zpowers_le.mpr hx)
  exact d.threeElement_centralizes_AA hx3 (hPS hx) (fun i => hPn i hx) a ha

end SylowThreeData

theorem eq_one_of_isPGroup_of_mem_inf_Lf (d : SylowThreeData G) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {i j : Fin 3} (hij : i ≠ j) {x : G} (hxi : x ∈ d.Lf i) (hxj : x ∈ d.Lf j)
    (hxp : IsPGroup p (Subgroup.zpowers x)) (hrank : CFSG.Open.pRank p (d.Lf i) = 1) :
    x = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpp : p.Prime := Fact.out
  let xbar : d.Q := d.phi i ⟨x, hxi⟩
  have hxbar_Lbi : xbar ∈ d.Lb i := ⟨⟨x, hxi⟩, rfl⟩
  have hxbar_eq : xbar = d.phi j ⟨x, hxj⟩ := by
    apply congrArg d.pi
    exact Subtype.ext rfl
  have hxbar_Lbj : xbar ∈ d.Lb j := by
    rw [hxbar_eq]
    exact ⟨⟨x, hxj⟩, rfl⟩
  have hxbar_center : (⟨xbar, hxbar_Lbi⟩ : ↥(d.Lb i)) ∈ Subgroup.center ↥(d.Lb i) := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    exact d.Lb_commute i j hij w.2 hxbar_Lbj
  haveI : Group.IsPerfect ↥(d.Lb i) := d.isPerfect_Lb i
  have hcenter_notdvd : ¬ p ∣ Nat.card (Subgroup.center ↥(d.Lb i)) := by
    have hrankLb : CFSG.Open.pRank p (⊤ : Subgroup ↥(d.Lb i)) = 1 := by
      rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
      have h1' : CFSG.pRank p ↥(d.Lb i) =
          CFSG.pRank p (↥(d.Lf i) ⧸ (d.phi i).ker) :=
        (CFSG.pRank_congr_of_mulEquiv (QuotientGroup.quotientKerEquivRange (d.phi i)) p).symm
      have hker_notdvd : ¬ p ∣ Nat.card ↥((d.phi i).ker) := by
        obtain ⟨k, hk⟩ := (d.ker_phi_isPGroup i).exists_card_eq
        rw [hk]
        intro hdvd
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp
          (hpp.dvd_of_dvd_pow hdvd))
      have h2 : CFSG.pRank p (↥(d.Lf i) ⧸ (d.phi i).ker) = CFSG.pRank p ↥(d.Lf i) :=
        CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hpp _
          hker_notdvd
      rw [h1', h2, CFSG.SectionRank.pRank_coe_eq_openPRank, hrank]
    exact not_dvd_card_center_of_pRank_eq_one hp2 hrankLb
  obtain ⟨k, hk⟩ := hxp.exists_orderOf_eq_pow ⟨x, Subgroup.mem_zpowers x⟩
  have hxord : orderOf x = p ^ k := by
    rwa [Subgroup.orderOf_mk] at hk
  have hxk : x ^ (p ^ k) = 1 := by
    rw [← hxord]
    exact pow_orderOf_eq_one x
  have hxk' : (⟨x, hxi⟩ : ↥(d.Lf i)) ^ (p ^ k) = 1 := by
    apply Subtype.ext
    simpa using hxk
  have hxbar_pow : xbar ^ (p ^ k) = 1 := by
    change d.phi i ⟨x, hxi⟩ ^ (p ^ k) = 1
    rw [← map_pow, hxk', map_one]
  have hxbar_pow' : (⟨xbar, hxbar_Lbi⟩ : ↥(d.Lb i)) ^ (p ^ k) = 1 := by
    apply Subtype.ext
    simpa using hxbar_pow
  have hxbar1 : xbar = 1 := by
    have hcop : Nat.Coprime (Nat.card (Subgroup.center ↥(d.Lb i))) (p ^ k) :=
      Nat.Coprime.pow_right k (((Nat.Prime.coprime_iff_not_dvd hpp).mpr
        hcenter_notdvd).symm)
    have h1 : (⟨xbar, hxbar_Lbi⟩ : ↥(d.Lb i)) = 1 :=
      CFSG.GroupTheory.PrimeField.eq_one_of_pow_eq_one_of_coprime hxbar_center hcop
        hxbar_pow'
    exact congrArg Subtype.val h1
  let Kerg : Subgroup G := ((d.phi i).ker).map (d.Lf i).subtype
  have hKerg2 : IsPGroup 2 Kerg := (d.ker_phi_isPGroup i).map (d.Lf i).subtype
  have hxKerg : x ∈ Kerg := by
    refine Subgroup.mem_map.mpr ⟨⟨x, hxi⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    exact hxbar1
  have hdisj : Subgroup.zpowers x ⊓ Kerg = ⊥ := by
    have h := (IsPGroup.disjoint_of_ne 2 p hp2.symm Kerg (Subgroup.zpowers x) hKerg2 hxp).eq_bot
    rwa [inf_comm] at h
  have hxbot : x ∈ (⊥ : Subgroup G) := by
    rw [← hdisj]
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_zpowers x, hxKerg⟩
  exact Subgroup.mem_bot.mp hxbot

private theorem exists_commute_of_isPGroup_normalizes {p : ℕ} [Fact p.Prime]
    {g : G} (hg : IsPGroup p (Subgroup.zpowers g)) {X : Subgroup G}
    (hX : g ∈ Subgroup.normalizer (X : Set G)) (hpdvd : p ∣ Nat.card X) :
    ∃ u ∈ X, orderOf u = p ∧ u * g = g * u := by
  obtain ⟨u, huX, huord, hucent⟩ :=
    CFSG.Quasithin.exists_orderOf_eq_of_isPGroup_normalizer hg
      (Subgroup.zpowers_le.mpr hX) hpdvd
  exact ⟨u, huX, huord,
    (Subgroup.mem_centralizer_iff.mp hucent g (Subgroup.mem_zpowers g)).symm⟩

namespace Ctx812E

private theorem false_of_two_pElements (c : Ctx812E G) {p : ℕ}
    (hp : p ∈ c.sig)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M p)
    (d : SylowThreeData G) (hdM : d.M = c.S.M) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P c.S.M)
    (hAA_le : d.AA ≤ P ⊓ Subgroup.centralizer (P : Set G))
    {a b : G} (haM : a ∈ c.S.M) (hbM : b ∈ c.S.M)
    (haord : orderOf a = p) (hbord : orderOf b = p)
    (hab : a * b = b * a) (haind : a ∉ Subgroup.zpowers b)
    (haAA : a ∈ Subgroup.centralizer (d.AA : Set G))
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hbLf : b ∈ d.Lf k) : False := by
  classical
  have hpp : p.Prime := (c.sig_prime p hp).1
  have hp1 : 1 < p := hpp.one_lt
  haveI : Fact p.Prime := ⟨hpp⟩
  have ha_pow : a ^ p = 1 := by rw [← haord]; exact pow_orderOf_eq_one a
  have hb_pow : b ^ p = 1 := by rw [← hbord]; exact pow_orderOf_eq_one b
  let R : Subgroup G := Subgroup.zpowers a ⊔ Subgroup.zpowers b
  have hcomm_ab : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers b, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((show Commute a b from hab).zpow_zpow m n).eq
  have hinf : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ :=
    CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Diag.zpowers_inf_eq_bot hpp ha_pow haind
  have hR_elem : CFSG.Open.IsElemAbelian p R :=
    CFSG.Open.IsElemAbelian.sup_of_commute
      (CFSG.Open.isElemAbelian_zpowers ha_pow)
      (CFSG.Open.isElemAbelian_zpowers hb_pow) hcomm_ab
  have hcardR : Nat.card ↥R = p ^ 2 := by
    obtain ⟨hcard, -⟩ :=
      CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
        (Subgroup.zpowers a) (Subgroup.zpowers b) hcomm_ab
    rw [hinf, Nat.card_zpowers, Nat.card_zpowers, haord, hbord] at hcard
    simpa [pow_two] using hcard
  have hrankR : 2 ≤ CFSG.Open.pRank p R :=
    CFSG.SectionRank.le_pRank hp1 (le_refl R) hR_elem hcardR
  have hRM : R ≤ c.S.M :=
    sup_le (Subgroup.zpowers_le.mpr haM) (Subgroup.zpowers_le.mpr hbM)
  let E : Subgroup G := d.A i ⊔ d.A j
  have hAiAA : ∀ l : Fin 3, d.A l ≤ d.AA := by
    intro l
    fin_cases l
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_right
  have hE_le_AA : E ≤ d.AA := sup_le (hAiAA i) (hAiAA j)
  have hE : E ≤ P ⊓ Subgroup.centralizer (P : Set G) := hE_le_AA.trans hAA_le
  have hEab : CFSG.Open.IsElemAbelian 3 E := d.isElemAbelian_A_sup_A i j
  have hEcard : Nat.card E = 3 ^ 2 := d.card_A_sup_A hij
  have ha_centE : a ∈ Subgroup.centralizer (E : Set G) :=
    (Subgroup.centralizer_le (fun x hx => hE_le_AA hx)) haAA
  have hcomm_aE : ⁅Subgroup.zpowers a, E⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact Subgroup.zpowers_le.mpr ha_centE
  have hb_le_sup : Subgroup.zpowers b ≤ d.Lf k := Subgroup.zpowers_le.mpr hbLf
  have hE_le_supij : E ≤ d.Lf i ⊔ d.Lf j := by
    refine sup_le ?_ ?_
    · exact (((d.A_le_H i).trans (d.H_le_Lf i))).trans le_sup_left
    · exact (((d.A_le_H j).trans (d.H_le_Lf j))).trans le_sup_right
  have hcomm_bi : ⁅d.Lf i, Subgroup.zpowers b⁆ ≤ d.N :=
    (Subgroup.commutator_mono le_rfl hb_le_sup).trans (d.hcomm i k hik)
  have hcomm_bj : ⁅d.Lf j, Subgroup.zpowers b⁆ ≤ d.N :=
    (Subgroup.commutator_mono le_rfl hb_le_sup).trans (d.hcomm j k hjk)
  have hLf_normN : ∀ l : Fin 3, d.Lf l ≤ Subgroup.normalizer (d.N : Set G) := fun l =>
    (d.hLM l).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 d.M)
  have hcomm_sup_b : ⁅d.Lf i ⊔ d.Lf j, Subgroup.zpowers b⁆ ≤ d.N :=
    CFSG.GorensteinWalter.commutator_sup_le_of_commutator_le_and_normalize
      (d.Lf i) (d.Lf j) (Subgroup.zpowers b) d.N hcomm_bi hcomm_bj
      (hLf_normN i) (hLf_normN j)
  have hcomm_bE : ⁅Subgroup.zpowers b, E⁆ ≤ d.N := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono hE_le_supij le_rfl).trans hcomm_sup_b
  have hM_normO : c.S.M ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 c.S.M : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 c.S.M
  have hnorm_a : Subgroup.zpowers a ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 c.S.M : Set G) :=
    (Subgroup.zpowers_le.mpr haM).trans hM_normO
  have hnorm_b : Subgroup.zpowers b ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 c.S.M : Set G) :=
    (Subgroup.zpowers_le.mpr hbM).trans hM_normO
  have hN_eq : d.N = CFSG.Open.pCoreOf 2 c.S.M := by
    rw [SylowThreeData.N, hdM]
  have hcommRE : ⁅R, E⁆ ≤ CFSG.Open.pCoreOf 2 c.S.M :=
    CFSG.GorensteinWalter.commutator_sup_le_of_commutator_le_and_normalize
      (Subgroup.zpowers a) (Subgroup.zpowers b) E (CFSG.Open.pCoreOf 2 c.S.M)
      (by rw [hcomm_aE]; exact bot_le) (hN_eq ▸ hcomm_bE) hnorm_a hnorm_b
  exact c.false_of_commutator_le_pCoreOf hp h76 hP hE hEab hEcard hRM hR_elem.isPGroup
    hrankR hcommRE

end Ctx812E

namespace Ctx812

theorem pRank_inf_centralizer_AA_le_one (c : Ctx812 G) {p : ℕ}
    (hp : p ∈ c.sig)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M p)
    (d : SylowThreeData G) (hdM : d.M = c.S.M) (hdL : d.L = c.L) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P c.S.M) (hdS : d.S = P ⊓ c.L)
    (hPn : ∀ i, P ≤ Subgroup.normalizer (d.Lf i : Set G)) :
    CFSG.Open.pRank p (c.S.M ⊓ Subgroup.centralizer (d.AA : Set G)) ≤ 1 := by
  classical
  have hP3 : IsPGroup 3 P := hP.isPGroup
  have hSP : d.S ≤ P := by rw [hdS]; exact inf_le_left
  have hPnormL : P ≤ Subgroup.normalizer (c.L : Set G) := hP.le.trans (c.le_normalizer_L)
  have hPS : P ≤ Subgroup.normalizer (d.S : Set G) := by
    rw [hdS]
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hx, hPnormL hx⟩
  have hAA_le : d.AA ≤ P ⊓ Subgroup.centralizer (P : Set G) :=
    d.AA_le_inf_centralizer hP3 hSP hPS hPn
  let E : Subgroup G := d.A 0 ⊔ d.A 1
  have hE_le_AA : E ≤ d.AA := le_sup_left
  have hE : E ≤ P ⊓ Subgroup.centralizer (P : Set G) := hE_le_AA.trans hAA_le
  have hEab : CFSG.Open.IsElemAbelian 3 E := d.isElemAbelian_A_sup_A 0 1
  have hEcard : Nat.card E = 3 ^ 2 := d.card_A_sup_A (by decide)
  have hbound := c.pRank_inf_centralizer_le_one hp h76 hP hE hEab hEcard
  refine (CFSG.SectionRank.pRank_mono (c.sig_prime p hp).1.one_lt ?_).trans hbound
  exact inf_le_inf_left c.S.M (Subgroup.centralizer_le (fun x hx => hE_le_AA hx))

private theorem exists_complement (k : Fin 3) : ∃ i j : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
  revert k
  decide

end Ctx812

namespace Ctx812E

theorem false_of_pElement_centralizer_AA_of_ne (c : Ctx812E G) {p : ℕ}
    (hp : p ∈ c.sig)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M p)
    (d : SylowThreeData G) (hdM : d.M = c.S.M) (hdL : d.L = c.L) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P c.S.M) (hdS : d.S = P ⊓ c.L)
    (hPn : ∀ i, P ≤ Subgroup.normalizer (d.Lf i : Set G))
    {k k' : Fin 3} (hkk' : k ≠ k')
    (hk : CFSG.Open.pRank p (d.Lf k) = 1) (hk' : 1 ≤ CFSG.Open.pRank p (d.Lf k'))
    {e : G} (he : e ≠ 1) (hep : IsPGroup p (Subgroup.zpowers e)) (heM : e ∈ c.S.M)
    (heA : e ∈ Subgroup.centralizer (d.AA : Set G))
    (heN : ∀ i, e ∈ Subgroup.normalizer (d.Lf i : Set G)) : False := by
  classical
  have hpp : p.Prime := (c.sig_prime p hp).1
  have hp5 : 5 ≤ p := c.five_le_of_mem_sigma hp
  have hp2 : p ≠ 2 := by omega
  have hp1 : 1 < p := hpp.one_lt
  haveI : Fact p.Prime := ⟨hpp⟩
  have hP3 : IsPGroup 3 P := hP.isPGroup
  have hSP : d.S ≤ P := by rw [hdS]; exact inf_le_left
  have hPnormL : P ≤ Subgroup.normalizer (c.L : Set G) := hP.le.trans (c.le_normalizer_L)
  have hPS : P ≤ Subgroup.normalizer (d.S : Set G) := by
    rw [hdS]
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hx, hPnormL hx⟩
  have hAA_le : d.AA ≤ P ⊓ Subgroup.centralizer (P : Set G) :=
    d.AA_le_inf_centralizer hP3 hSP hPS hPn
  have hp_dvd_Lf : ∀ i : Fin 3, 1 ≤ CFSG.Open.pRank p (d.Lf i) → p ∣ Nat.card (d.Lf i) := by
    intro i hi
    obtain ⟨E, hE, hEab, hEcard⟩ := CFSG.SectionRank.exists_pRank hp1 (d.Lf i)
    have hdvd : p ∣ Nat.card E := by
      rw [hEcard]
      exact dvd_pow_self p (by omega)
    exact hdvd.trans (Subgroup.card_dvd_of_le hE)
  obtain ⟨u, huLf0, huord, hue⟩ :=
    exists_commute_of_isPGroup_normalizes hep (heN k) (hp_dvd_Lf k hk.ge)
  have huM : u ∈ c.S.M := hdM ▸ d.hLM k huLf0
  have hu_pow : u ^ p = 1 := by rw [← huord]; exact pow_orderOf_eq_one u
  by_cases hu : u ∈ Subgroup.zpowers e
  ·
    have hup : IsPGroup p (Subgroup.zpowers u) :=
      (CFSG.Open.isElemAbelian_zpowers hu_pow).isPGroup
    obtain ⟨v, hvLf2, hvord, hvu⟩ :=
      exists_commute_of_isPGroup_normalizes hup (Subgroup.zpowers_le.mpr (heN k') hu)
        (hp_dvd_Lf k' hk')
    have hvM : v ∈ c.S.M := hdM ▸ d.hLM k' hvLf2
    have hv_pow : v ^ p = 1 := by rw [← hvord]; exact pow_orderOf_eq_one v
    have hvu_not : v ∉ Subgroup.zpowers u := by
      intro hv
      have hvLf0 : v ∈ d.Lf k := Subgroup.zpowers_le.mpr huLf0 hv
      have hv1 : v = 1 :=
        eq_one_of_isPGroup_of_mem_inf_Lf d hp2 (i := k) (j := k') hkk'
          hvLf0 hvLf2 ((CFSG.Open.isElemAbelian_zpowers hv_pow).isPGroup) hk
      rw [hv1, orderOf_one] at hvord
      omega
    have haind : u ∉ Subgroup.zpowers v := by
      intro huv
      have hEq : Subgroup.zpowers u = Subgroup.zpowers v := by
        refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr huv) ?_
        rw [Nat.card_zpowers, Nat.card_zpowers, huord, hvord]
      exact hvu_not (hEq.symm ▸ Subgroup.mem_zpowers v)
    have huAA : u ∈ Subgroup.centralizer (d.AA : Set G) :=
      Subgroup.zpowers_le.mpr heA hu
    obtain ⟨i, j, hij, hik, hjk⟩ := Ctx812.exists_complement k'
    exact false_of_two_pElements c hp h76 d hdM hP hAA_le huM hvM huord hvord
      hvu.symm haind huAA hij hik hjk hvLf2
  ·
    obtain ⟨e', he'Z, he'ord⟩ : ∃ e' ∈ Subgroup.zpowers e, orderOf e' = p := by
      have hne : Subgroup.zpowers e ≠ ⊥ := Subgroup.zpowers_eq_bot.not.mpr he
      exact CFSG.Quasithin.exists_orderOf_eq_of_isPGroup_ne_bot hep hne
    have he'M : e' ∈ c.S.M := Subgroup.zpowers_le.mpr heM he'Z
    have he'AA : e' ∈ Subgroup.centralizer (d.AA : Set G) :=
      Subgroup.zpowers_le.mpr heA he'Z
    have hcomm_eu : Commute e u := hue.symm
    have he'u : Commute e' u := by
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp he'Z
      rw [← hm]
      exact hcomm_eu.zpow_left m
    have haind : e' ∉ Subgroup.zpowers u := by
      intro h
      have hEq : Subgroup.zpowers e' = Subgroup.zpowers u := by
        refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr h) ?_
        rw [Nat.card_zpowers, Nat.card_zpowers, he'ord, huord]
      exact hu (Subgroup.zpowers_le.mpr he'Z (hEq ▸ Subgroup.mem_zpowers u))
    obtain ⟨i, j, hij, hik, hjk⟩ := Ctx812.exists_complement k
    exact false_of_two_pElements c hp h76 d hdM hP hAA_le he'M huM he'ord huord
      he'u.eq haind he'AA hij hik hjk huLf0

theorem false_of_pElement_centralizer_AA (c : Ctx812E G) {p : ℕ}
    (hp : p ∈ c.sig)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M p)
    (d : SylowThreeData G) (hdM : d.M = c.S.M) (hdL : d.L = c.L) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P c.S.M) (hdS : d.S = P ⊓ c.L)
    (hPn : ∀ i, P ≤ Subgroup.normalizer (d.Lf i : Set G))
    (h1 : ∀ i, CFSG.Open.pRank p (d.Lf i) = 1)
    {e : G} (he : e ≠ 1) (hep : IsPGroup p (Subgroup.zpowers e)) (heM : e ∈ c.S.M)
    (heA : e ∈ Subgroup.centralizer (d.AA : Set G))
    (heN : ∀ i, e ∈ Subgroup.normalizer (d.Lf i : Set G)) : False :=
  c.false_of_pElement_centralizer_AA_of_ne hp h76 d hdM hdL hP hdS hPn
    (k := 0) (k' := 2) (by decide) (h1 0) (h1 2).ge he hep heM heA heN

end Ctx812E

namespace Ctx812

theorem false_of_pElement_centralizer_AA_of_ne (c : Ctx812 G) {p : ℕ}
    (hp : p ∈ c.sig)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M p)
    (d : SylowThreeData G) (hdM : d.M = c.S.M) (hdL : d.L = c.L) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P c.S.M) (hdS : d.S = P ⊓ c.L)
    (hPn : ∀ i, P ≤ Subgroup.normalizer (d.Lf i : Set G))
    {k k' : Fin 3} (hkk' : k ≠ k')
    (hk : CFSG.Open.pRank p (d.Lf k) = 1) (hk' : 1 ≤ CFSG.Open.pRank p (d.Lf k'))
    {e : G} (he : e ≠ 1) (hep : IsPGroup p (Subgroup.zpowers e)) (heM : e ∈ c.S.M)
    (heA : e ∈ Subgroup.centralizer (d.AA : Set G))
    (heN : ∀ i, e ∈ Subgroup.normalizer (d.Lf i : Set G)) : False := by
  exact c.toCtx812E.false_of_pElement_centralizer_AA_of_ne hp h76 d hdM hdL hP hdS hPn
    hkk' hk hk' he hep heM heA heN

end Ctx812

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
