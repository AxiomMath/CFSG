module

public import CFSG.RankThree.GF2n.Smith81.InspOrders
public import CFSG.RankThree.GF2n.Smith81.S81BLane
import CFSG.RankThree.GF2n.Smith81.InspLocal
import CFSG.RankThree.GF2n.Smith81.Smith219Step1
import CFSG.RankThree.GF2n.Smith81.TiBridge
import CFSG.RankThree.GF2n.Stroth80.Sec1110Core
import CFSG.LocalAnalysis.ComponentInitial.UnitaryModelOuterTwoPart
public import CFSG.LocalAnalysis.EvenBN.U5.LinSec43OutGen
public import CFSG.RankThree.GF2n.Smith81.Sec2FStar
public import CFSG.RankThree.GF2n.Smith81.TiSylow
import CFSG.RankThree.GF2n.Smith81.InspLinOrder

public section

namespace CFSG.RankThree.GF2n.Smith81.Insp

open CFSG CFSG.Blueprint CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
  CFSG.RankThree.GF2n.Stroth80 CFSG.Timmesfeld CFSG.Timmesfeld.Orders
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped commutatorElement

section Local

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem rootGroup_eq_Z_E_of_nonfused (hN : Smith212ENonfusedStatement)
    (IH : Smith1981Below (Nat.card G)) (hc : SmithECfg M Q Z B) {z : G} (hz : z ∈ Z)
    (hz1 : z ≠ 1) : CFSG.Timmesfeld.rootGroup (CFSG.Timmesfeld.CorB.cls z) z = Z :=
  Smith219Step1.rootGroup_eq_Z_of_212 hc.ctx.hyp hz hz1 fun x hxM hxQ hxc c hc' hxc' =>
    Classical.byContradiction fun hc1 =>
      hN G M Q Z B IH hc z hz hz1 x hxM hxQ hxc c hc' hc1 (hxc.symm.trans hxc')

theorem Q_le_H0_of_strothHyp (H : StrothHyp M Q Z) : Q ≤ H0 M Z := by
  intro x hx
  refine ⟨H.Q_normal.1 hx, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
  have hzC : z ∈ Subgroup.centralizer (Q : Set G) := by
    rw [H.centralizer_Q]
    exact hz
  exact ((Subgroup.mem_centralizer_iff.mp hzC) x hx).symm

theorem card_H0_dvd_mulAut_of_centTrivial (hc : Ctx M Q Z B)
    (hCT : CentTrivial M Q Z (Lgen M (LB M Q B)))
    [(Q.subgroupOf (Lgen M (LB M Q B))).Normal] :
    Nat.card (H0 M Z) ∣ Nat.card Q *
      Nat.card (MulAut (↥(Lgen M (LB M Q B)) ⧸ Q.subgroupOf (Lgen M (LB M Q B)))) := by
  have hNM : H0 M Z ≤ M := inf_le_left
  have hRL : H0 M Z ≤ Subgroup.normalizer (Lgen M (LB M Q B) : Set G) :=
    hNM.trans (Lgen_normalizes M _)
  have hRN : ∀ r ∈ H0 M Z, ∀ x ∈ Q, r * x * r⁻¹ ∈ Q := fun r hr x hx =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hNM hr)) x).mp hx
  let act := LocalAnalysis.EvenBN.U5.Lin43Out.outAct (N := Q) hRL hRN
  have hker : act.ker ≤ Q.subgroupOf (H0 M Z) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_subgroupOf]
    refine hCT x x.2 fun y hy => ?_
    have h3 := congrArg (fun α : MulAut (↥(Lgen M (LB M Q B)) ⧸
      Q.subgroupOf (Lgen M (LB M Q B))) =>
        α ((⟨y⁻¹, Subgroup.inv_mem _ hy⟩ : ↥(Lgen M (LB M Q B))) :
          ↥(Lgen M (LB M Q B)) ⧸ Q.subgroupOf (Lgen M (LB M Q B)))) hx
    simp only [act, LocalAnalysis.EvenBN.U5.Lin43Out.outAct_mk, MulAut.one_apply] at h3
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h3
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, LocalAnalysis.EvenBN.U5.Lin43Out.conjL_coe]
      at h3
    have e1 : ⁅(x : G), y⁆ = ((x : G) * y⁻¹ * (x : G)⁻¹)⁻¹ * y⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e1]
    exact h3
  have hcard := Subgroup.card_ker_mul_card_range act
  haveI : Finite (MulAut (↥(Lgen M (LB M Q B)) ⧸ Q.subgroupOf (Lgen M (LB M Q B)))) :=
    Finite.of_injective (fun α : MulAut (↥(Lgen M (LB M Q B)) ⧸
      Q.subgroupOf (Lgen M (LB M Q B))) => (α : _ → _)) DFunLike.coe_injective
  have hk : Nat.card act.ker ∣ Nat.card Q := by
    have h := Subgroup.card_dvd_of_le hker
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Q_le_H0_of_strothHyp hc.hyp)).toEquiv]
      at h
  rw [← hcard]
  exact mul_dvd_mul hk (Subgroup.card_subgroup_dvd_card act.range)

theorem card_mulAut_dvd_outer_mul (X : Type) [Group X] :
    Nat.card (MulAut X) ∣ Nat.card (Outer X) * Nat.card X := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (inner X)]
  exact mul_dvd_mul_left _ (Subgroup.card_range_dvd _)

theorem card_H0_dvd_of_centTrivial (hc : Ctx M Q Z B)
    (hCT : CentTrivial M Q Z (Lgen M (LB M Q B)))
    [(Q.subgroupOf (Lgen M (LB M Q B))).Normal] :
    Nat.card (H0 M Z) ∣ Nat.card Q *
      (Nat.card (Outer (↥(Lgen M (LB M Q B)) ⧸ Q.subgroupOf (Lgen M (LB M Q B)))) *
        Nat.card (↥(Lgen M (LB M Q B)) ⧸ Q.subgroupOf (Lgen M (LB M Q B)))) :=
  (card_H0_dvd_mulAut_of_centTrivial hc hCT).trans
    (mul_dvd_mul_left _ (card_mulAut_dvd_outer_mul _))

theorem e3_quot {f : ℕ} (hf1 : 1 ≤ f) (hf : Nat.card Z = 2 ^ f)
    (hE3 : QuotSat (Lgen M (LB M Q B)) Q (IsPSLModel 6 (Nat.card Z)) ∨
      QuotSat (Lgen M (LB M Q B)) Q (IsPSUModel 6 (Nat.card Z))) :
    ∃ _ : (Q.subgroupOf (Lgen M (LB M Q B))).Normal,
      (Nat.card (↥(Lgen M (LB M Q B)) ⧸ Q.subgroupOf (Lgen M (LB M Q B)))).factorization 2 =
        f * 15 ∧
      ∃ d : ℕ, ¬ 2 ∣ d ∧ d ≠ 0 ∧
        Nat.card (Outer (↥(Lgen M (LB M Q B)) ⧸ Q.subgroupOf (Lgen M (LB M Q B)))) ∣
          2 * f * d := by
  rw [hf] at hE3
  have hq2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  rcases hE3 with ⟨hN, K, _, _, hK, ⟨e⟩⟩ | ⟨hN, K, _, _, hK, ⟨e⟩⟩
  · have h : StatedClassicalModel (↥(Lgen M (LB M Q B)) ⧸ Q.subgroupOf (Lgen M (LB M Q B)))
        .PSL 6 2 f :=
      ⟨⟨Nat.prime_two, hf1, by norm_num, by simp, by simp⟩, K, inferInstance, inferInstance,
        hK, ⟨e⟩⟩
    refine ⟨hN, ?_, Nat.gcd 6 (2 ^ f - 1), fun h2 => ?_, Nat.gcd_ne_zero_left (by norm_num),
      (LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound _ 6 2 f h).2.2.2.2
        (by norm_num)⟩
    · rw [(card_statedClassicalModel_two h).1 rfl,
        factorization_two_of_profile (profile_ordA (n := 5) (by norm_num) hf1)]
    · have : 2 ∣ 2 ^ f - 1 := h2.trans (Nat.gcd_dvd_right _ _)
      omega
  · have h : StatedClassicalModel (↥(Lgen M (LB M Q B)) ⧸ Q.subgroupOf (Lgen M (LB M Q B)))
        .PSU 6 2 f :=
      ⟨⟨Nat.prime_two, hf1, by norm_num, by simp⟩, K, inferInstance, inferInstance, hK, ⟨e⟩⟩
    refine ⟨hN, ?_, Nat.gcd 6 (2 ^ f + 1), fun h2 => ?_, Nat.gcd_ne_zero_left (by norm_num),
      (LocalAnalysis.ComponentInitial.unitary_model_outer_two_part_bound _ 6 2 f h).2.2.1 ▸ dvd_rfl⟩
    · rw [(card_statedClassicalModel_two h).2.1 rfl,
        factorization_two_of_profile (profile_ordTwistedA (n := 5) (by norm_num) hf1)]
    · have : 2 ∣ 2 ^ f + 1 := h2.trans (Nat.gcd_dvd_right _ _)
      omega

theorem factorization_card_le_e3 (hc : Ctx M Q Z B)
    (hCT : CentTrivial M Q Z (Lgen M (LB M Q B))) (hQ21 : Nat.card Q = Nat.card Z ^ 21)
    (hE3 : QuotSat (Lgen M (LB M Q B)) Q (IsPSLModel 6 (Nat.card Z)) ∨
      QuotSat (Lgen M (LB M Q B)) Q (IsPSUModel 6 (Nat.card Z)))
    {f : ℕ} (hf : Nat.card Z = 2 ^ f) :
    (Nat.card G).factorization 2 ≤ f * 36 + 2 * f.factorization 2 + 1 := by
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · have := hc.hyp.q4
      rw [hf] at this
      norm_num at this
    · exact h
  obtain ⟨hN, hT15, d, hd2, hd0, hOut⟩ := e3_quot hf1 hf hE3
  have hdvd := card_H0_dvd_of_centTrivial hc hCT
  have v_le : ∀ {a b : ℕ}, b ≠ 0 → a ∣ b → a.factorization 2 ≤ b.factorization 2 :=
    fun hb h => (Nat.factorization_le_iff_dvd (fun ha => hb (Nat.eq_zero_of_zero_dvd (ha ▸ h)))
      hb).mpr h 2
  have v_mul : ∀ {a b : ℕ}, a ≠ 0 → b ≠ 0 →
      (a * b).factorization 2 = a.factorization 2 + b.factorization 2 :=
    fun ha hb => by rw [Nat.factorization_mul ha hb, Finsupp.add_apply]
  have hQ0 : Nat.card Q ≠ 0 := Nat.card_pos.ne'
  have hT0 : Nat.card (↥(Lgen M (LB M Q B)) ⧸ Q.subgroupOf (Lgen M (LB M Q B))) ≠ 0 :=
    Nat.card_pos.ne'
  have hO0 : 2 * f * d ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) (by omega)) hd0
  have hH0 : (Nat.card (H0 M Z)).factorization 2 ≤ f * 21 + (1 + f.factorization 2) + f * 15 := by
    have h := v_le (mul_ne_zero hQ0 (mul_ne_zero hO0 hT0))
      (hdvd.trans (mul_dvd_mul_left _ (mul_dvd_mul_right hOut _)))
    rw [v_mul hQ0 (mul_ne_zero hO0 hT0), v_mul hO0 hT0, v_mul (mul_ne_zero (by norm_num)
      (by omega)) hd0, v_mul (by norm_num) (by omega), Nat.Prime.factorization_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd hd2, hT15, hQ21, hf, ← pow_mul,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same] at h
    linarith
  have h1 := factorization_relIndex_H0_le hc.hyp hf
  rw [← factorization_card_M_eq hc.hyp]
  have hHM : H0 M Z ≤ M := inf_le_left
  have hrel := Subgroup.relIndex_mul_card (H := H0 M Z) (K := M)
  rw [inf_eq_left.mpr hHM] at hrel
  have hr0 : (H0 M Z).relIndex M ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at hrel
    exact Nat.card_pos.ne' hrel.symm
  rw [← hrel, Nat.factorization_mul hr0 Nat.card_pos.ne', Finsupp.add_apply]
  omega

end Local

theorem e3_identify (hN : Smith212ENonfusedStatement) (hK1 : K1NSLStatement)
    (hK2L : K2PSLStatement2) (hK2S : K2PSpStatement2) {G : Type} [Group G] [Finite G]
    {M Q Z B : Subgroup G} (IH : Smith1981Below (Nat.card G)) (hc : SmithECfg M Q Z B)
    (hCT : CentTrivial M Q Z (Lgen M (LB M Q B))) (hQ21 : Nat.card Q = Nat.card Z ^ 21)
    (hE3 : QuotSat (Lgen M (LB M Q B)) Q (IsPSLModel 6 (Nat.card Z)) ∨
      QuotSat (Lgen M (LB M Q B)) Q (IsPSUModel 6 (Nat.card Z)))
    (hroot : ∀ z ∈ Z, z ≠ 1 → Timmesfeld.IsRootInvolutionSet (conjClassSet z)) {z : G}
    (hz : z ∈ Z) (hz1 : z ≠ 1) :
    ∃ f : ℕ, Nat.card Z = 2 ^ f ∧ 2 ≤ f ∧
      (LieModel ↥(Subgroup.normalClosure ({z} : Set G)) .E6 0 2 f ∨
        LieModel ↥(Subgroup.normalClosure ({z} : Set G)) .twistedE6 0 2 f) := by
  classical
  have H := hc.ctx.hyp
  obtain ⟨f, k₀, hf, hcp⟩ := H.cp
  have hf2 : 2 ≤ f := by
    have h4 := H.q4
    rw [hf] at h4
    by_contra hlt
    push Not at hlt
    interval_cases f <;> norm_num at h4
  have hodd : pPrimeCore 2 G = ⊥ := H.toTim81Hyp.pPrimeCore_eq_bot H.q4
  have hnd : ∃ d e : G, IsConj z d ∧ IsConj z e ∧ orderOf (d * e) = 4 := by
    obtain ⟨d, hd, e, he, h4⟩ := exists_orderOf_mul_eq_four H hz hz1
    exact ⟨d, e, hd, he, h4⟩
  have hHyp := hyp_classIn (hroot z hz hz1) (isConj_normalClosure H hz hz1) hodd H.o2 hnd
  have hrootZ : rootGroup {g : G | IsConj z g} z = Z :=
    rootGroup_eq_Z_E_of_nonfused hN IH hc hz hz1
  have hcardroot : Nat.card (rootGroup (classIn z) (selfIn z)) = 2 ^ f := by
    rw [card_rootGroup_classIn]
    show Nat.card (rootGroup {g : G | IsConj z g} z) = 2 ^ f
    rw [hrootZ, hf]
  have hl : ∃ d ∈ classIn z, ∃ e ∈ rootSet (classIn z) d, e ≠ d := by
    refine ⟨selfIn z, IsConj.refl z, ?_⟩
    by_contra hcon
    push Not at hcon
    have hle : rootGroup (classIn z) (selfIn z) ≤ Subgroup.zpowers (selfIn z) := by
      rw [rootGroup, Subgroup.closure_le]
      intro e he
      rw [hcon e he]
      exact Subgroup.mem_zpowers _
    have h1 := Subgroup.card_le_of_le hle
    have hz2 : (selfIn z) ^ 2 = 1 := Subtype.ext (by simpa using sq_eq_one_of_cp hcp z hz)
    have h2 := orderOf_le_of_pow_eq_one (by norm_num) hz2
    rw [hcardroot, Nat.card_zpowers] at h1
    have h3 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    omega
  have hQdvd : Nat.card Q ∣ Nat.card ↥(Subgroup.normalClosure ({z} : Set G)) :=
    Subgroup.card_dvd_of_le (Q_le_normalClosure H hz hz1)
  obtain ⟨hN, hT15, -⟩ := e3_quot (by omega) hf hE3
  have hLcard : Nat.card (Lgen M (LB M Q B)) = Nat.card Q *
      Nat.card (↥(Lgen M (LB M Q B)) ⧸ Q.subgroupOf (Lgen M (LB M Q B))) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Q.subgroupOf (Lgen M (LB M Q B))),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Q_le_Lgen M Q B)).toEquiv, mul_comm]
  have hLX : Nat.card (Lgen M (LB M Q B)) ∣ Nat.card ↥(Subgroup.normalClosure ({z} : Set G)) :=
    (card_Lgen_dvd_centralizer hc.ctx hz hz1).trans (Subgroup.card_subgroup_dvd_card _)
  have hX0 : Nat.card ↥(Subgroup.normalClosure ({z} : Set G)) ≠ 0 := Nat.card_pos.ne'
  have hlo : f * 36 ≤ (Nat.card ↥(Subgroup.normalClosure ({z} : Set G))).factorization 2 := by
    have h := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' hX0).mpr hLX 2
    rw [hLcard, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, hT15,
      hQ21, hf, ← pow_mul, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same] at h
    linarith
  have hup : (Nat.card ↥(Subgroup.normalClosure ({z} : Set G))).factorization 2 ≤
      f * 36 + 2 * f.factorization 2 + 1 :=
    le_trans ((Nat.factorization_le_iff_dvd hX0 Nat.card_pos.ne').mpr
      (Subgroup.card_subgroup_dvd_card _) 2) (factorization_card_le_e3 hc.ctx hCT hQ21 hE3 hf)
  rcases rootOutcome_of_K1NSL hK1 hHyp hl with ⟨t, k, f', -, htag, hL, hroot'⟩ | hU
  · have hff : f' = f := by
      have h1 := hroot' (selfIn z) (IsConj.refl z)
      rw [hcardroot] at h1
      exact (Nat.pow_right_injective (le_refl 2) h1).symm
    rw [hff] at htag hL hroot'
    have hv := factorization_two_card_of_lieModel (by omega) htag hL
    have hv2 := factorization_two_lt f (by omega)
    have hlo' : 36 ≤ Smith219Arith.sylowExp t k := by
      rw [hv] at hlo
      exact Nat.le_of_mul_le_mul_left hlo (by omega)
    have hhi' : Smith219Arith.sylowExp t k ≤ 36 + 2 := by
      rw [hv] at hup
      exact Smith219Arith.le_add_two_of_mul_le (f := f) (a := 2 * f.factorization 2 + 1)
        (by linarith) (by omega)
    have hQ : (2 ^ f) ^ 21 ≤ Nat.card (pCoreOf 2 (Subgroup.centralizer
        ({selfIn z} : Set ↥(Subgroup.normalClosure ({z} : Set G))))) := by
      have h1 := card_Q_le_pCoreOf H hz hz1
      rwa [hQ21, hf] at h1
    have hq1 : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
    have hPSL : t = .PSL → 10 + 2 ≤ k := by
      rintro rfl
      have hk : 3 ≤ k := by simpa [TimmesfeldTag] using htag
      have hO := hK2L _ _ k f hHyp hk (by omega) hL hroot' (selfIn z) (IsConj.refl z)
      have hw : 21 ≤ 2 * k - 3 := (Nat.pow_le_pow_iff_right hq1).mp (hQ.trans hO)
      omega
    have hPSp : t = .PSp → 10 + 3 ≤ 2 * k := by
      rintro rfl
      have hk : 3 ≤ k := by simpa [TimmesfeldTag] using htag
      rcases hK2S _ _ k f hHyp hk (by omega) hL hroot' (selfIn z) (IsConj.refl z) with hO | ⟨hO, -⟩
      · have hw : 21 ≤ 2 * k - 1 := (Nat.pow_le_pow_iff_right hq1).mp (hQ.trans hO)
        omega
      · have hw : 21 ≤ 4 * k - 5 := (Nat.pow_le_pow_iff_right hq1).mp (hQ.trans hO)
        omega
    rcases Smith219Arith.laneB_window (Or.inl ⟨rfl, rfl⟩) hlo' hhi' hPSL hPSp with
      ⟨-, ht | ht⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · subst ht
      have hk0 : k = 0 := by simpa [TimmesfeldTag] using htag
      subst hk0
      exact ⟨f, hf, hf2, Or.inl hL⟩
    · subst ht
      have hk0 : k = 0 := by simpa [TimmesfeldTag] using htag
      subst hk0
      exact ⟨f, hf, hf2, Or.inr hL⟩
    · omega
    · omega
  · exfalso
    have h5 := factorization_psu_three_three hU
    have hpow : 2 ^ (f * 21) ∣ Nat.card ↥(Subgroup.normalClosure ({z} : Set G)) := by
      rw [pow_mul, ← hf, ← hQ21]
      exact hQdvd
    have hle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hX0).mp hpow
    rw [h5] at hle
    omega

theorem smith219EInspectionE3L_of (hN : Smith212ENonfusedStatement) (hK1 : K1NSLStatement)
    (hK2L : K2PSLStatement2) (hK2S : K2PSpStatement2) : Smith219EInspectionE3LStatement := by
  intro G _ _ M Q Z B IH hc hcase hroot _
  obtain ⟨t₀, hD4, hQ21, -, hL6⟩ := hcase
  have H := hc.ctx.hyp
  obtain ⟨z, hz, hz1, -⟩ := exists_mem_Z_ne H 1
  obtain ⟨f, hf, hf2, hE6 | h2E6⟩ :=
    e3_identify hN hK1 hK2L hK2S IH hc hD4.2.2.2 hQ21 (Or.inl hL6) hroot hz hz1
  · obtain ⟨hF, -⟩ := generalizedFitting_eq_normalClosure H hz hz1
    exact ⟨f, hf, LieModel.of_mulEquiv (MulEquiv.subgroupCongr hF.symm) hE6⟩
  · exfalso
    obtain ⟨hN, K, _, _, hK, ⟨e⟩⟩ := hL6
    rw [hf] at hK
    have hT : Nat.card (↥(Lgen M (LB M Q B)) ⧸ Q.subgroupOf (Lgen M (LB M Q B))) =
        ordA 5 (2 ^ f) :=
      (card_statedClassicalModel_two (t := .PSL) (n := 6)
        ⟨⟨Nat.prime_two, by omega, by norm_num, by simp, by simp⟩, K, inferInstance,
          inferInstance, hK, ⟨e⟩⟩).1 rfl
    have hTX : Nat.card (↥(Lgen M (LB M Q B)) ⧸ Q.subgroupOf (Lgen M (LB M Q B))) ∣
        Nat.card ↥(Subgroup.normalClosure ({z} : Set G)) := by
      refine (Subgroup.card_quotient_dvd_card _).trans ?_
      exact (card_Lgen_dvd_centralizer hc.ctx hz hz1).trans (Subgroup.card_subgroup_dvd_card _)
    have hX := card_chevalleyExceptionalModel_two (h2E6.chevalleyExceptionalModel (by decide))
    obtain ⟨ℓ, hℓ, hℓA, hℓE⟩ := Smith219Arith.laneB_ppd_L6 (q := 2 ^ f)
      (by calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2)
      (Nat.even_pow.mpr ⟨even_two, by omega⟩)
    rw [← hT] at hℓA
    have := hℓA.trans hTX
    rw [hX] at this
    exact hℓE this

theorem smith219EInspectionE3U_of (hN : Smith212ENonfusedStatement) (hK1 : K1NSLStatement)
    (hK2L : K2PSLStatement2) (hK2S : K2PSpStatement2) : Smith219EInspectionE3UStatement := by
  intro G _ _ M Q Z B IH hc hcase hroot _
  obtain ⟨t₀, hD4, hQ21, -, hU6⟩ := hcase
  have H := hc.ctx.hyp
  obtain ⟨z, hz, hz1, -⟩ := exists_mem_Z_ne H 1
  obtain ⟨f, hf, hf2, hE6 | h2E6⟩ :=
    e3_identify hN hK1 hK2L hK2S IH hc hD4.2.2.2 hQ21 (Or.inr hU6) hroot hz hz1
  · exfalso
    obtain ⟨hN, K, _, _, hK, ⟨e⟩⟩ := hU6
    rw [hf] at hK e
    have hT : Nat.card (↥(Lgen M (LB M Q B)) ⧸ Q.subgroupOf (Lgen M (LB M Q B))) =
        ordTwistedA 5 (2 ^ f) :=
      (card_statedClassicalModel_two (t := .PSU) (n := 6)
        ⟨⟨Nat.prime_two, by omega, by norm_num, by simp⟩, K, inferInstance, inferInstance, hK,
          ⟨e⟩⟩).2.1 rfl
    have hTX : Nat.card (↥(Lgen M (LB M Q B)) ⧸ Q.subgroupOf (Lgen M (LB M Q B))) ∣
        Nat.card ↥(Subgroup.normalClosure ({z} : Set G)) := by
      refine (Subgroup.card_quotient_dvd_card _).trans ?_
      exact (card_Lgen_dvd_centralizer hc.ctx hz hz1).trans (Subgroup.card_subgroup_dvd_card _)
    have hX := card_chevalleyExceptionalModel_two (hE6.chevalleyExceptionalModel (by decide))
    obtain ⟨ℓ, hℓ, hℓA, hℓE⟩ := Smith219Arith.laneB_ppd_U6 (q := 2 ^ f)
      (by calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2)
    rw [← hT] at hℓA
    have := hℓA.trans hTX
    rw [hX] at this
    exact hℓE this
  · obtain ⟨hF, -⟩ := generalizedFitting_eq_normalClosure H hz hz1
    exact ⟨f, hf, LieModel.of_mulEquiv (MulEquiv.subgroupCongr hF.symm) h2E6⟩

end CFSG.RankThree.GF2n.Smith81.Insp
