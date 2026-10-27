module

public import CFSG.RankThree.GF2n.Smith81.InspOrthSmallModels
public import CFSG.RankThree.GF2n.Smith81.InspE45
public import CFSG.RankThree.GF2n.Smith81.OrthStmt
import CFSG.RankThree.GF2n.Smith81.InspE3
import CFSG.RankThree.GF2n.Smith81.Smith219Step1
import CFSG.RankThree.GF2n.Stroth80.Sec1110Core
import CFSG.RankThree.PartTwo.Sec14.Wales1411WHJCoreA5J2
import CFSG.RankThree.GF2n.Smith81.InspLinOrder

public section

namespace CFSG.RankThree.GF2n.Smith81.Insp

open CFSG CFSG.Blueprint CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
  CFSG.RankThree.GF2n.Stroth80 CFSG.Timmesfeld CFSG.Timmesfeld.Orders CFSG.CGT.Timmesfeld75
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def KCOmegaFourStatement : Prop :=
  ∀ (Y : Type) [Group Y] (D : Set Y) (f : ℕ), Hyp Y D → 2 ≤ f →
    (∀ d ∈ D, Nat.card (rootGroup D d) = 2 ^ f) →
      (LieModel Y .POmegaPlus 4 2 f → ∀ d ∈ D, Nat.card (Subgroup.centralizer ({d} : Set Y)) ∣
        (2 ^ f) ^ 9 * ordBC 1 (2 ^ f) * ordD 2 (2 ^ f)) ∧
      (LieModel Y .POmegaMinus 4 2 f → ∀ d ∈ D, Nat.card (Subgroup.centralizer ({d} : Set Y)) ∣
        (2 ^ f) ^ 9 * ordBC 1 (2 ^ f) * ordTwistedD 2 (2 ^ f))

@[expose] def Smith219OrthSmallStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), SmithOrthCfg M Q Z B →
    (∀ z ∈ Z, z ≠ 1 → Timmesfeld.IsRootInvolutionSet (conjClassSet z)) →
      Timmesfeld.Outcome (FStar G) →
      (∀ t : G, CtxD4 M Q Z B t → CaseE1Plus M Q Z B t → ∃ f : ℕ, Nat.card Z = 2 ^ f ∧
        LieModel (FStar G) .POmegaPlus 4 2 f) ∧
      (∀ t : G, CtxD4 M Q Z B t → CaseE1Minus M Q Z B t → ∃ f : ℕ, Nat.card Z = 2 ^ f ∧
        LieModel (FStar G) .POmegaMinus 4 2 f) ∧
      (∀ (t : G) (m : ℕ), m ≤ 2 → CtxD4 M Q Z B t → CaseE2Plus M Q Z B t m → ∃ f : ℕ,
        Nat.card Z = 2 ^ f ∧ LieModel (FStar G) .POmegaPlus (m + 2) 2 f) ∧
      (∀ (t : G) (m : ℕ), m ≤ 3 → CtxD4 M Q Z B t → CaseE2Minus M Q Z B t m → ∃ f : ℕ,
        Nat.card Z = 2 ^ f ∧ LieModel (FStar G) .POmegaMinus (m + 2) 2 f)

theorem ordBC_one_two_pow {f : ℕ} (hf : 1 ≤ f) : ordBC 1 (2 ^ f) = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
  have hq2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hg : Nat.gcd 2 (2 ^ f - 1) = 1 := by
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two _ (Nat.gcd_dvd_left 2 (2 ^ f - 1)) with
      h | h
    · exact h
    · have h3 := Nat.gcd_dvd_right 2 (2 ^ f - 1)
      rw [h] at h3
      omega
  unfold ordBC
  rw [hg, Nat.div_one, Finset.Icc_self, Finset.prod_singleton]
  ring_nf

theorem not_ordD_dvd_ordTwistedD {f m : ℕ} (hf : 2 ≤ f) (hm : 1 ≤ m) :
    ¬ ordD m (2 ^ f) ∣ ordTwistedD m (2 ^ f) ∧ ¬ ordTwistedD m (2 ^ f) ∣ ordD m (2 ^ f) := by
  set q := 2 ^ f with hq
  have hq2 : 2 ∣ q := dvd_pow_self 2 (by omega)
  have hq4 : 2 ≤ q := Nat.le_of_dvd (by positivity) hq2
  have hqm2 : 2 ∣ q ^ m := dvd_pow hq2 (by omega)
  have hqm : 2 ≤ q ^ m := le_trans hq4 (Nat.le_self_pow (by omega) q)
  have hodd1 : Odd (q ^ m - 1) := by
    rw [Nat.odd_iff]
    omega
  have hodd2 : Odd (q ^ m + 1) := by
    rw [Nat.odd_iff]
    omega
  have hg1 : Nat.gcd 4 (q ^ m - 1) = 1 :=
    Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd1)
  have hg2 : Nat.gcd 4 (q ^ m + 1) = 1 :=
    Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd2)
  set P := ∏ i ∈ Finset.Icc 1 (m - 1), (q ^ (2 * i) - 1) with hP
  have hP0 : 0 < P := by
    rw [hP]
    refine Finset.prod_pos fun i hi => ?_
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have : 2 ≤ q ^ (2 * i) := le_trans hq4 (Nat.le_self_pow (by omega) q)
    omega
  have hD : ordD m q = q ^ (m * (m - 1)) * P * (q ^ m - 1) := by
    unfold ordD
    rw [hg1, Nat.div_one]
    ring
  have hTD : ordTwistedD m q = q ^ (m * (m - 1)) * P * (q ^ m + 1) := by
    unfold ordTwistedD
    rw [hg2, Nat.div_one]
    ring
  have hC : 0 < q ^ (m * (m - 1)) * P := Nat.mul_pos (by positivity) hP0
  rw [hD, hTD]
  constructor
  · intro h
    have h1 := Nat.dvd_of_mul_dvd_mul_left hC h
    have h2 : q ^ m - 1 ∣ 2 := by
      have := (Nat.dvd_sub h1 (dvd_refl _))
      rwa [show q ^ m + 1 - (q ^ m - 1) = 2 by omega] at this
    have := Nat.le_of_dvd (by norm_num) h2
    have h4 : 4 ≤ q ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (f * m) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
        _ = q ^ m := by rw [hq, ← pow_mul]
    omega
  · intro h
    have h1 := Nat.dvd_of_mul_dvd_mul_left hC h
    have := Nat.le_of_dvd (by omega) h1
    omega

theorem orthE2_identify_core (h212 : Smith212OrthCoreStatement) (hK1 : K1NSLStatement)
    (hK2L : K2PSLStatement2) (hKCO : KCOmegaStatement2) {G : Type} [Group G] [Finite G]
    {M Q Z B : Subgroup G} (hc : SmithOrthCfg M Q Z B)
    (hroot : ∀ z ∈ Z, z ≠ 1 → Timmesfeld.IsRootInvolutionSet (conjClassSet z)) {t₀ : G}
    (hD4 : CtxD4 M Q Z B t₀) {m : ℕ} (hm : 2 ≤ m) (hKC4 : m = 2 → KCOmegaFourStatement)
    (hQ : Nat.card Q = Nat.card Z ^ (4 * m + 1))
    {f : ℕ} (hf : Nat.card Z = 2 ^ f) [(Q.subgroupOf (Lgen M (LB M Q B))).Normal] {ordB : ℕ}
    (hordB : ordB = ordD m (2 ^ f) ∨ ordB = ordTwistedD m (2 ^ f))
    (hLc : Nat.card (Lgen M (LB M Q B)) = Nat.card Q * (2 ^ f * ((2 ^ f) ^ 2 - 1) * ordB))
    {c : ℕ} (hAut : (Nat.card (MulAut (↥(Lgen M (LB M Q B)) ⧸
      Q.subgroupOf (Lgen M (LB M Q B))))).factorization 2 ≤ f * (m * (m - 1) + 1) + c)
    (hcf : f.factorization 2 + c < 3 * f)
    (h3D4 : m = 2 → ¬ Nat.card Q * (2 ^ f * ((2 ^ f) ^ 2 - 1) * ordB) ∣ ordTrialityD4 (2 ^ f))
    {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1) :
    ∃ t : StatedLieTag, LieModel ↥(Subgroup.normalClosure ({z} : Set G)) t (m + 2) 2 f ∧
      ((t = .POmegaPlus ∧ ordB ∣ ordD m (2 ^ f)) ∨
        (t = .POmegaMinus ∧ ordB ∣ ordTwistedD m (2 ^ f))) := by
  classical
  have H := hc.ctx.hyp
  have hf2 : 2 ≤ f := by
    have h4 := H.q4
    rw [hf] at h4
    by_contra hlt
    push Not at hlt
    interval_cases f <;> norm_num at h4
  have hf1 : 1 ≤ f := by omega
  have hpr : Profile ordB (f * (m * (m - 1)))
      (if ordB = ordD m (2 ^ f) then zD m f else z2D m f) := by
    rcases hordB with h | h
    · rw [if_pos h, h]
      exact profile_ordD (by omega) hf1
    · by_cases h' : ordB = ordD m (2 ^ f)
      · rw [if_pos h', h']
        exact profile_ordD (by omega) hf1
      · rw [if_neg h', h]
        exact profile_ordTwistedD (by omega) hf1
  have hvB : ordB.factorization 2 = f * (m * (m - 1)) := factorization_two_of_profile hpr
  have v_le : ∀ {a b : ℕ}, b ≠ 0 → a ∣ b → a.factorization 2 ≤ b.factorization 2 :=
    fun hb h => (Nat.factorization_le_iff_dvd (fun ha => hb (Nat.eq_zero_of_zero_dvd (ha ▸ h)))
      hb).mpr h 2
  have v_mul : ∀ {a b : ℕ}, a ≠ 0 → b ≠ 0 →
      (a * b).factorization 2 = a.factorization 2 + b.factorization 2 :=
    fun ha hb => by rw [Nat.factorization_mul ha hb, Finsupp.add_apply]
  have hQ0 : Nat.card Q ≠ 0 := Nat.card_pos.ne'
  have hL0 : Nat.card (Lgen M (LB M Q B)) ≠ 0 := Nat.card_pos.ne'
  have hA0 : 2 ^ f * ((2 ^ f) ^ 2 - 1) ≠ 0 := by
    have : 4 ≤ (2 ^ f) ^ 2 := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (f * 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = (2 ^ f) ^ 2 := by rw [pow_mul]
    exact mul_ne_zero (by positivity) (by omega)
  have hB0 : ordB ≠ 0 := fun h0 => hL0 (by rw [hLc, h0, mul_zero, mul_zero])
  have hvA : (2 ^ f * ((2 ^ f) ^ 2 - 1)).factorization 2 = f := by
    have hodd : Odd ((2 ^ f) ^ 2 - 1) := by
      have h1 : 2 ∣ (2 ^ f) ^ 2 := dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)
      have h2 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
      rw [Nat.odd_iff]
      omega
    exact factorization_two_eq_of_odd rfl hodd
  haveI : Finite (MulAut (↥(Lgen M (LB M Q B)) ⧸ Q.subgroupOf (Lgen M (LB M Q B)))) :=
    Finite.of_injective (fun α : MulAut (↥(Lgen M (LB M Q B)) ⧸
      Q.subgroupOf (Lgen M (LB M Q B))) => (α : _ → _)) DFunLike.coe_injective
  have hMA0 : Nat.card (MulAut (↥(Lgen M (LB M Q B)) ⧸ Q.subgroupOf (Lgen M (LB M Q B)))) ≠ 0 :=
    Nat.card_pos.ne'
  have hH0 : (Nat.card (H0 M Z)).factorization 2 ≤
      f * (4 * m + 1) + (f * (m * (m - 1) + 1) + c) := by
    have h := v_le (mul_ne_zero hQ0 hMA0) (card_H0_dvd_mulAut_of_centTrivial hc.ctx hD4.2.2.2)
    rw [v_mul hQ0 hMA0, hQ, hf, ← pow_mul, Nat.Prime.factorization_pow Nat.prime_two,
      Finsupp.single_eq_same] at h
    omega
  have hmm : (m + 1) * (m + 2) = 4 * m + 1 + (m * (m - 1) + 1) := by
    obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  have hG : (Nat.card G).factorization 2 ≤
      f * ((m + 1) * (m + 2)) + (f.factorization 2 + c) := by
    have h1 := factorization_relIndex_H0_le H hf
    rw [← factorization_card_M_eq H]
    have hHM : H0 M Z ≤ M := inf_le_left
    have hrel := Subgroup.relIndex_mul_card (H := H0 M Z) (K := M)
    rw [inf_eq_left.mpr hHM] at hrel
    have hr0 : (H0 M Z).relIndex M ≠ 0 := fun h0 => by
      rw [h0, zero_mul] at hrel
      exact Nat.card_pos.ne' hrel.symm
    rw [← hrel, Nat.factorization_mul hr0 Nat.card_pos.ne', Finsupp.add_apply, hmm, mul_add]
    omega
  have hLC := card_Lgen_dvd_centralizer hc.ctx hz hz1
  have hX0 : Nat.card ↥(Subgroup.normalClosure ({z} : Set G)) ≠ 0 := Nat.card_pos.ne'
  have hlo : f * ((m + 1) * (m + 2)) ≤
      (Nat.card ↥(Subgroup.normalClosure ({z} : Set G))).factorization 2 := by
    have h := v_le hX0 (hLC.trans (Subgroup.card_subgroup_dvd_card _))
    rw [hLc, v_mul hQ0 (mul_ne_zero hA0 hB0), v_mul hA0 hB0, hvA, hvB, hQ, hf,
      ← pow_mul, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same] at h
    rw [hmm, mul_add, mul_add, mul_one]
    nlinarith
  have hup : (Nat.card ↥(Subgroup.normalClosure ({z} : Set G))).factorization 2 ≤
      f * ((m + 1) * (m + 2)) + (f.factorization 2 + c) :=
    le_trans (v_le Nat.card_pos.ne' (Subgroup.card_subgroup_dvd_card _)) hG
  have h6 : 2 ^ 6 ∣ Nat.card Q := by
    rw [hQ, hf, ← pow_mul]
    exact pow_dvd_pow 2 (by nlinarith)
  have hrootZ : rootGroup {g : G | IsConj z g} z = Z :=
    Smith219Step1.rootGroup_eq_Z_orth h212 hc hz hz1
  obtain ⟨-, hHyp, t, k, htag, hL, hroot'⟩ :=
    rootOutcome_classIn hK1 H hz hz1 (hroot z hz hz1) hrootZ hf h6
  have hv := factorization_two_card_of_lieModel hf1 htag hL
  have hlo' : (m + 1) * (m + 2) ≤ Smith219Arith.sylowExp t k := by
    rw [hv] at hlo
    exact Nat.le_of_mul_le_mul_left hlo (by omega)
  have hhi' : Smith219Arith.sylowExp t k ≤ (m + 1) * (m + 2) + 2 := by
    rw [hv] at hup
    exact Smith219Arith.le_add_two_of_mul_le (f := f) hup hcf
  have hQ' : (2 ^ f) ^ (4 * m + 1) ≤ Nat.card (pCoreOf 2 (Subgroup.centralizer
      ({selfIn z} : Set ↥(Subgroup.normalClosure ({z} : Set G))))) := by
    have h1 := card_Q_le_pCoreOf H hz hz1
    rwa [hQ, hf] at h1
  have hq1 : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
  have hPSL : t = .PSL → 2 * m + 2 ≤ k := by
    rintro rfl
    have hk : 3 ≤ k := by simpa [TimmesfeldTag] using htag
    have hO := hK2L _ _ k f hHyp hk hf2 hL hroot' (selfIn z) (IsConj.refl z)
    have hw : 4 * m + 1 ≤ 2 * k - 3 := (Nat.pow_le_pow_iff_right hq1).mp (hQ'.trans hO)
    omega
  rcases Smith219Arith.laneA_window (by omega) hlo' hhi' hPSL with ⟨ht, rfl⟩ | ⟨rfl, hm2⟩
  ·
    have hKC : (LieModel ↥(Subgroup.normalClosure ({z} : Set G)) .POmegaPlus (m + 2) 2 f →
          ∀ d ∈ classIn z, Nat.card (Subgroup.centralizer
            ({d} : Set ↥(Subgroup.normalClosure ({z} : Set G)))) ∣
            (2 ^ f) ^ (4 * (m + 2) - 7) * ordBC 1 (2 ^ f) * ordD (m + 2 - 2) (2 ^ f)) ∧
        (LieModel ↥(Subgroup.normalClosure ({z} : Set G)) .POmegaMinus (m + 2) 2 f →
          ∀ d ∈ classIn z, Nat.card (Subgroup.centralizer
            ({d} : Set ↥(Subgroup.normalClosure ({z} : Set G)))) ∣
            (2 ^ f) ^ (4 * (m + 2) - 7) * ordBC 1 (2 ^ f) * ordTwistedD (m + 2 - 2) (2 ^ f)) := by
      rcases Nat.lt_or_ge m 3 with h3 | h3
      · obtain rfl : m = 2 := by omega
        exact hKC4 rfl _ _ f hHyp hf2 hroot'
      · exact hKCO _ _ (m + 2) f hHyp (by omega) hf2 hroot'
    have hT : Nat.card Q * (2 ^ f * ((2 ^ f) ^ 2 - 1) * ordB) ∣ Nat.card (Subgroup.centralizer
        ({selfIn z} : Set ↥(Subgroup.normalClosure ({z} : Set G)))) := hLc ▸ hLC
    rw [hQ, hf] at hT
    have h47 : 4 * (m + 2) - 7 = 4 * m + 1 := by omega
    have hm2 : m + 2 - 2 = m := by omega
    have hpos : 0 < (2 ^ f) ^ (4 * m + 1) * (2 ^ f * ((2 ^ f) ^ 2 - 1)) :=
      Nat.pos_of_ne_zero (mul_ne_zero (by positivity) hA0)
    rcases ht with rfl | rfl
    · have h1 := hKC.1 hL (selfIn z) (IsConj.refl z)
      rw [h47, hm2, ordBC_one_two_pow hf1] at h1
      refine ⟨.POmegaPlus, hL, Or.inl ⟨rfl, ?_⟩⟩
      exact Nat.dvd_of_mul_dvd_mul_left hpos (by
        rw [mul_assoc]
        exact hT.trans h1)
    · have h1 := hKC.2 hL (selfIn z) (IsConj.refl z)
      rw [h47, hm2, ordBC_one_two_pow hf1] at h1
      refine ⟨.POmegaMinus, hL, Or.inr ⟨rfl, ?_⟩⟩
      exact Nat.dvd_of_mul_dvd_mul_left hpos (by
        rw [mul_assoc]
        exact hT.trans h1)
  ·
    have hX := card_of_lieModel_trialityD4 hL
    exact absurd (hLc ▸ hX ▸ hLC.trans (Subgroup.card_subgroup_dvd_card _)) (h3D4 hm2)

theorem orthE2_identify (h212 : Smith212OrthCoreStatement) (hK1 : K1NSLStatement)
    (hK2L : K2PSLStatement2) (hKCO : KCOmegaStatement2) {G : Type} [Group G] [Finite G]
    {M Q Z B : Subgroup G} (hc : SmithOrthCfg M Q Z B)
    (hroot : ∀ z ∈ Z, z ≠ 1 → Timmesfeld.IsRootInvolutionSet (conjClassSet z)) {t₀ : G}
    (hD4 : CtxD4 M Q Z B t₀) {m : ℕ} (hm : 2 ≤ m) (hKC4 : m = 2 → KCOmegaFourStatement)
    (hQ : Nat.card Q = Nat.card Z ^ (4 * m + 1))
    {f : ℕ} (hf : Nat.card Z = 2 ^ f) {A Bo : Type} [Group A] [Group Bo]
    [(Q.subgroupOf (Lgen M (LB M Q B))).Normal]
    (e : (↥(Lgen M (LB M Q B)) ⧸ Q.subgroupOf (Lgen M (LB M Q B))) ≃* A × Bo)
    (hA : IsSLModel 2 (2 ^ f) A) {ordB : ℕ} (hBs : IsSimpleGroup Bo) (hBc : Nat.card Bo = ordB)
    (hBo : ordProj[2] (Nat.card (Outer Bo)) ≤ 4 * ordProj[2] f)
    (hordB : ordB = ordD m (2 ^ f) ∨ ordB = ordTwistedD m (2 ^ f)) {z : G} (hz : z ∈ Z)
    (hz1 : z ≠ 1) :
    ∃ t : StatedLieTag, LieModel ↥(Subgroup.normalClosure ({z} : Set G)) t (m + 2) 2 f ∧
      ((t = .POmegaPlus ∧ ordB ∣ ordD m (2 ^ f)) ∨
        (t = .POmegaMinus ∧ ordB ∣ ordTwistedD m (2 ^ f))) := by
  classical
  have H := hc.ctx.hyp
  have hf2 : 2 ≤ f := by
    have h4 := H.q4
    rw [hf] at h4
    by_contra hlt
    push Not at hlt
    interval_cases f <;> norm_num at h4
  have hf1 : 1 ≤ f := by omega
  haveI : Finite A := Finite.of_injective (fun a : A => (e.symm (a, 1) : _)) (fun a b h => by
    have := congrArg e h
    simpa using this)
  haveI : Finite Bo := Finite.of_injective (fun b : Bo => (e.symm (1, b) : _)) (fun a b h => by
    have := congrArg e h
    simpa using this)
  obtain ⟨hAs, hAc, hAo⟩ := sl2_model_facts hf2 hA
  haveI := hAs
  haveI := hBs
  have h4A : 4 ∣ Nat.card A := by
    rw [hAc]
    exact Dvd.dvd.mul_right (show 2 ^ 2 ∣ 2 ^ f from pow_dvd_pow 2 hf2) _
  have hAinj := CFSG.RankThree.PartTwo.Sec14.Wales1411W.HJProd.conj_injective_of_simple
    (exists_not_commute_of_simple hAs h4A)
  have hev : Even (2 ^ f) := (Nat.even_pow' (by omega)).mpr even_two
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have hAB : Nat.card A < Nat.card Bo := by
    rw [hAc, hBc]
    rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | hm3
    · have h1 : 2 ^ f * ((2 ^ f) ^ 2 - 1) < (2 ^ f) ^ 2 * ((2 ^ f) ^ 2 - 1) :=
        Nat.mul_lt_mul_of_pos_right (by nlinarith) (by
          have : 16 ≤ (2 ^ f) ^ 2 := by nlinarith
          omega)
      rcases hordB with rfl | rfl
      · rw [ordD_two_eq_of_even hev (by positivity)]
        calc 2 ^ f * ((2 ^ f) ^ 2 - 1) < (2 ^ f) ^ 2 * ((2 ^ f) ^ 2 - 1) := h1
          _ ≤ (2 ^ f) ^ 2 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 2 - 1)) :=
            Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (by
              have : 16 ≤ (2 ^ f) ^ 2 := by nlinarith
              omega))
      · rw [ordTwistedD_two_eq_of_even hev]
        calc 2 ^ f * ((2 ^ f) ^ 2 - 1) < (2 ^ f) ^ 2 * ((2 ^ f) ^ 2 - 1) := h1
          _ ≤ (2 ^ f) ^ 2 * (((2 ^ f) ^ 2 + 1) * ((2 ^ f) ^ 2 - 1)) :=
            Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
    · have hpr : Profile ordB (f * (m * (m - 1)))
          (if ordB = ordD m (2 ^ f) then zD m f else z2D m f) := by
        rcases hordB with h | h
        · rw [if_pos h, h]
          exact profile_ordD (by omega) hf1
        · by_cases h' : ordB = ordD m (2 ^ f)
          · rw [if_pos h', h']
            exact profile_ordD (by omega) hf1
          · rw [if_neg h', h]
            exact profile_ordTwistedD (by omega) hf1
      have hvB : ordB.factorization 2 = f * (m * (m - 1)) := factorization_two_of_profile hpr
      have hB0 : 0 < ordB := by
        rw [← hBc]
        exact Nat.card_pos
      have hBq : 2 ^ (f * (m * (m - 1))) ∣ ordB := by
        have h := Nat.ordProj_dvd ordB 2
        rwa [hvB] at h
      have h1 : 2 ^ (f * (m * (m - 1))) ≤ ordB := Nat.le_of_dvd hB0 hBq
      have h2 : 2 ^ f * ((2 ^ f) ^ 2 - 1) < (2 ^ f) ^ 3 := by
        have : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
        calc 2 ^ f * ((2 ^ f) ^ 2 - 1) < 2 ^ f * (2 ^ f) ^ 2 :=
              Nat.mul_lt_mul_of_pos_left (by omega) (by positivity)
          _ = (2 ^ f) ^ 3 := by ring
      have h3 : (2 ^ f) ^ 3 ≤ 2 ^ (f * (m * (m - 1))) := by
        rw [← pow_mul]
        have h12 : 3 * 2 ≤ m * (m - 1) := Nat.mul_le_mul (by omega) (by omega)
        exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left f (by omega))
      omega
  have v_le : ∀ {a b : ℕ}, b ≠ 0 → a ∣ b → a.factorization 2 ≤ b.factorization 2 :=
    fun hb h => (Nat.factorization_le_iff_dvd (fun ha => hb (Nat.eq_zero_of_zero_dvd (ha ▸ h)))
      hb).mpr h 2
  have v_mul : ∀ {a b : ℕ}, a ≠ 0 → b ≠ 0 →
      (a * b).factorization 2 = a.factorization 2 + b.factorization 2 :=
    fun ha hb => by rw [Nat.factorization_mul ha hb, Finsupp.add_apply]
  have hOA0 : Nat.card (Outer A) ≠ 0 := Nat.card_pos.ne'
  have hOB0 : Nat.card (Outer Bo) ≠ 0 := Nat.card_pos.ne'
  have hA0 : Nat.card A ≠ 0 := Nat.card_pos.ne'
  have hBo0 : Nat.card Bo ≠ 0 := Nat.card_pos.ne'
  have hOA : (Nat.card (Outer A)).factorization 2 ≤ f.factorization 2 := v_le (by omega) hAo
  have hOB : (Nat.card (Outer Bo)).factorization 2 ≤ 2 + f.factorization 2 := by
    have h' : 2 ^ (Nat.card (Outer Bo)).factorization 2 ≤ 2 ^ (2 + f.factorization 2) := by
      rw [pow_add]
      exact hBo
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h'
  have hvA : (Nat.card A).factorization 2 = f := by
    rw [hAc]
    have hodd : Odd ((2 ^ f) ^ 2 - 1) := by
      have h1 : 2 ∣ (2 ^ f) ^ 2 := dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)
      have h2 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
      rw [Nat.odd_iff]
      omega
    exact factorization_two_eq_of_odd rfl hodd
  have hpr : Profile ordB (f * (m * (m - 1)))
      (if ordB = ordD m (2 ^ f) then zD m f else z2D m f) := by
    rcases hordB with h | h
    · rw [if_pos h, h]
      exact profile_ordD (by omega) hf1
    · by_cases h' : ordB = ordD m (2 ^ f)
      · rw [if_pos h', h']
        exact profile_ordD (by omega) hf1
      · rw [if_neg h', h]
        exact profile_ordTwistedD (by omega) hf1
  have hvB : ordB.factorization 2 = f * (m * (m - 1)) := factorization_two_of_profile hpr
  have hTmul : Nat.card (MulAut (↥(Lgen M (LB M Q B)) ⧸ Q.subgroupOf (Lgen M (LB M Q B)))) ∣
      Nat.card (Outer A) * Nat.card A * (Nat.card (Outer Bo) * Nat.card Bo) := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv]
    exact (card_mulAut_prod_dvd hAB hAinj).trans
      (mul_dvd_mul (card_mulAut_dvd_outer_mul A) (card_mulAut_dvd_outer_mul Bo))
  have hAut : (Nat.card (MulAut (↥(Lgen M (LB M Q B)) ⧸
      Q.subgroupOf (Lgen M (LB M Q B))))).factorization 2 ≤
        f * (m * (m - 1) + 1) + (2 * f.factorization 2 + 2) := by
    have hprod0 : Nat.card (Outer A) * Nat.card A * (Nat.card (Outer Bo) * Nat.card Bo) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hOA0 hA0) (mul_ne_zero hOB0 hBo0)
    have h := v_le hprod0 hTmul
    rw [v_mul (mul_ne_zero hOA0 hA0) (mul_ne_zero hOB0 hBo0), v_mul hOA0 hA0,
      v_mul hOB0 hBo0, hvA, hBc, hvB] at h
    rw [mul_add, mul_one]
    omega
  have hLc : Nat.card (Lgen M (LB M Q B)) = Nat.card Q * (2 ^ f * ((2 ^ f) ^ 2 - 1) * ordB) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Q.subgroupOf (Lgen M (LB M Q B))),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Q_le_Lgen M Q B)).toEquiv, Nat.card_congr
      e.toEquiv, Nat.card_prod, hAc, hBc, mul_comm]
  have hcf : f.factorization 2 + (2 * f.factorization 2 + 2) < 3 * f := by
    have h1 := Smith219Arith.four_mul_padicValNat_two_add_one_lt (by omega : 0 < f)
    rw [← Nat.factorization_def f Nat.prime_two] at h1
    omega
  have h3D4 : m = 2 → ¬ Nat.card Q * (2 ^ f * ((2 ^ f) ^ 2 - 1) * ordB) ∣
      ordTrialityD4 (2 ^ f) := by
    rintro rfl
    rw [hQ, hf, show 4 * 2 + 1 = 9 by rfl]
    rcases hordB with rfl | rfl
    · exact not_dvd_ordTrialityD4_plus hf2
    · exact not_dvd_ordTrialityD4_minus hf1
  exact orthE2_identify_core h212 hK1 hK2L hKCO hc hroot hD4 hm hKC4 hQ hf hordB hLc hAut hcf h3D4
    hz hz1

theorem smith219OrthInspection_of (hSmall : Smith219OrthSmallStatement)
    (h212 : Smith212OrthCoreStatement) (hK1 : K1NSLStatement) (hK2L : K2PSLStatement2)
    (hKCO : KCOmegaStatement2) : Smith219OrthInspectionStatement := by
  intro G _ _ M Q Z B hc hroot hout
  obtain ⟨h1P, h1M, h2P, h2M⟩ := hSmall G M Q Z B hc hroot hout
  have H := hc.ctx.hyp
  obtain ⟨z, hz, hz1, -⟩ := exists_mem_Z_ne H 1
  obtain ⟨hF, -⟩ := generalizedFitting_eq_normalClosure H hz hz1
  obtain ⟨f, k₀, hf, -⟩ := H.cp
  have hf2 : 2 ≤ f := by
    have h4 := H.q4
    rw [hf] at h4
    by_contra hlt
    push Not at hlt
    interval_cases f <;> norm_num at h4
  have hf1 : 1 ≤ f := by omega
  refine ⟨h1P, h1M, fun t m hD4 hcase => ?_, fun t m hD4 hcase => ?_⟩
  · rcases le_or_gt m 2 with hm | hm
    · exact h2P t m hm hD4 hcase
    · obtain ⟨-, hQ, -, -, hT⟩ := hcase
      rw [hf] at hT
      obtain ⟨hN, A, Bo, _, _, hA, hB, ⟨e⟩⟩ := hT
      obtain ⟨hBs, hBc, hBo⟩ : IsSimpleGroup Bo ∧ Nat.card Bo = ordD m (2 ^ f) ∧
          ordProj[2] (Nat.card (Outer Bo)) ≤ 4 * ordProj[2] f := by
        rcases Nat.lt_or_ge m 4 with h4 | h4
        · obtain rfl : m = 3 := by omega
          exact omegaPlus_three_model_facts hf2 hB
        · exact omegaPlus_model_facts h4 hf1 hB
      obtain ⟨t', hL, hsign | hsign⟩ := orthE2_identify h212 hK1 hK2L hKCO hc hroot hD4
        (by omega) (fun h => absurd h (by omega)) hQ hf e hA hBs hBc hBo (Or.inl rfl) hz hz1
      · obtain ⟨rfl, -⟩ := hsign
        exact ⟨f, hf, LieModel.of_mulEquiv (MulEquiv.subgroupCongr hF.symm) hL⟩
      · exact absurd hsign.2 (not_ordD_dvd_ordTwistedD hf2 (by omega)).1
  · rcases le_or_gt m 3 with hm | hm
    · exact h2M t m hm hD4 hcase
    · obtain ⟨-, hQ, -, -, hT⟩ := hcase
      rw [hf] at hT
      obtain ⟨hN, A, Bo, _, _, hA, hB, ⟨e⟩⟩ := hT
      obtain ⟨hBs, hBc, hBo⟩ := omegaMinus_model_facts (by omega) hf1 hB
      obtain ⟨t', hL, hsign | hsign⟩ := orthE2_identify h212 hK1 hK2L hKCO hc hroot hD4
        (by omega) (fun h => absurd h (by omega)) hQ hf e hA hBs hBc hBo (Or.inr rfl) hz hz1
      · exact absurd hsign.2 (not_ordD_dvd_ordTwistedD hf2 (by omega)).2
      · obtain ⟨rfl, -⟩ := hsign
        exact ⟨f, hf, LieModel.of_mulEquiv (MulEquiv.subgroupCongr hF.symm) hL⟩

end CFSG.RankThree.GF2n.Smith81.Insp
