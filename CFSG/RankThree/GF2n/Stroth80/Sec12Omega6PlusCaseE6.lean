module

public import CFSG.RankThree.GF2n.Stroth80.Sec12Omega6PlusCfg
import CFSG.RankThree.GF2n.Stroth80.GriessOrthSmall
import CFSG.RankThree.GF2n.Stroth80.Sec7TailRecogGroup
import CFSG.RankThree.GF2n.Stroth80.Sec78Z1
import CFSG.RankThree.GF2n.Smith81.Sec217Perfect
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidPlusFacts
import CFSG.LieType.Universal.SpinOmega.Center
import CFSG.Adapters.StatedClassicalOrders
import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
public import CFSG.ClassicalGroups.Orthogonal.RootGroupSwap
public import CFSG.RankThree.GF2n.Stroth80.Sec12SubWidth
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsE
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsSylow
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssembly1015
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssembly69
public import CFSG.RankThree.GF2n.Stroth80.Sec86Assembly
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviFields
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOEightChoice
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofRigidDefs
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidSetup
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidTheta
import CFSG.RankThree.GF2n.Stroth80.Sec78NormZ0
import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssemblyFixed
import CFSG.RankThree.GF2n.Stroth80.Sec7TailBarFrattini
import CFSG.RankThree.GF2n.Stroth80.Sec7TailCorBList
import CFSG.RankThree.GF2n.Stroth80.Sec7TailFStarSimple
import CFSG.RankThree.GF2n.Stroth80.Sec7TailFlagArith
import CFSG.RankThree.GF2n.Stroth80.Sec7TailFlagType
import CFSG.RankThree.GF2n.Stroth80.Sec7TailStmts
import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoClassical.ORigid
  (isSimpleGroup_statedOmega_quadPlus_of_three_le)
open scoped commutatorElement

theorem isOmegaPlus_three_facts {q : ℕ} {Y : Type} [Group Y] (hq : ∃ a : ℕ, 2 ≤ a ∧ q = 2 ^ a)
    (h : IsOmegaPlus 3 q Y) :
    IsSimpleGroup Y ∧ (∃ x y : Y, x * y ≠ y * x) ∧
      Nat.card Y = q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 - 1) * (q ^ 4 - 1))) := by
  obtain ⟨a, ha, rfl⟩ := hq
  obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := h
  haveI hchar : CharP K 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hK
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  haveI hs : IsSimpleGroup ↥(StatedOmega (StatedQuadPlus 3 K)) :=
    isSimpleGroup_statedOmega_quadPlus_of_three_le (K := K) (k := 3) le_rfl
  haveI hp : Group.IsPerfect ↥(StatedOmega (StatedQuadPlus 3 K)) :=
    CFSG.LieType.Universal.Spin.isPerfect_statedOmega_quadPlus (K := K) (n := 3) le_rfl
  obtain ⟨eSL⟩ := nonempty_statedOmega_quadPlus_three_mulEquiv (K := K) h4
  have hcard : Nat.card Y = Nat.card (StatedSL 4 K) :=
    Nat.card_congr (e.toEquiv.trans eSL.toEquiv)
  rw [CFSG.Open.StatedAPI.card_statedSL_eq_prod (by norm_num), hK] at hcard
  refine ⟨e.isSimpleGroup, ?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    haveI : IsMulCommutative ↥(StatedOmega (StatedQuadPlus 3 K)) :=
      ⟨⟨fun x y => e.symm.injective (by rw [map_mul, map_mul]; exact hcon _ _)⟩⟩
    exact Group.IsPerfect.not_isMulCommutative ↥(StatedOmega (StatedQuadPlus 3 K)) inferInstance
  · rw [hcard, show Finset.Icc 2 4 = ({2, 3, 4} : Finset ℕ) from by decide,
      Finset.prod_insert (show (2 : ℕ) ∉ ({3, 4} : Finset ℕ) by decide),
      Finset.prod_insert (show (3 : ℕ) ∉ ({4} : Finset ℕ) by decide), Finset.prod_singleton]

theorem op6_ge_pow_nine (q : ℕ) (hq : 4 ≤ q) :
    q ^ 9 ≤ q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 - 1) * (q ^ 4 - 1))) := by
  have h2 : q ≤ q ^ 2 - 1 := by
    have : q * 4 ≤ q ^ 2 := by rw [sq]; exact Nat.mul_le_mul_left q hq
    omega
  have h3 : q ^ 2 ≤ q ^ 3 - 1 := by
    have : q ^ 2 * 4 ≤ q ^ 3 := by rw [pow_succ]; exact Nat.mul_le_mul_left _ hq
    have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have h4 : 1 ≤ q ^ 4 - 1 := by
    have : 4 ≤ q ^ 4 := le_trans hq (Nat.le_self_pow (by norm_num) q)
    omega
  calc q ^ 9 = q ^ 6 * (q * (q ^ 2 * 1)) := by ring
    _ ≤ q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 - 1) * (q ^ 4 - 1))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul h2 (Nat.mul_le_mul h3 h4))

@[expose] def Stroth12Omega6PlusCaseE6Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ),
    Stroth12Hyp hc n → ∀ t ∈ LB M Q B, t ∉ Q → OmegaPlusNat hc t 3 →
    SubConfigSatz M Q Z (hc.CN t) →
    ∃ hN : (Q.subgroupOf (H0 M Z)).Normal, haveI := hN
      ∀ B₂ : Subgroup (↥(H0 M Z) ⧸ Q.subgroupOf (H0 M Z)),
        Ctx (Subgroup.normalizer ((cen (bar (H0 M Z) Q (hc.CN t)) : Subgroup _) : Set _))
          (bar (H0 M Z) Q (hc.CN t)) (cen (bar (H0 M Z) Q (hc.CN t))) B₂ →
        SecondCfgCaseE6Four (bar (H0 M Z) Q (hc.CN t)) B₂

theorem stroth12Omega6PlusCaseE6_of_second (hZcard : Sec7ZCardStatement)
    (h78 : Stroth78Statement) (hgen : StrothGenByBStatement) (h4i : Stroth4iStatement) :
    Stroth12Omega6PlusCaseE6Statement := by
  intro G _ _ M Q Z B hc n h12 t ht htQ hp hsub
  haveI := hc.normal_Q_in_M
  obtain ⟨⟨hN', H₂⟩, hN'', hall⟩ := hsub
  haveI := hN'
  refine ⟨hN', fun B₂ hcB₂ => ?_⟩
  have h5 : Sec5Hyp hc n t := h12.toSec5 ht htQ
  have hlarge := h12.large t ht htQ
  have hnot : ¬ OmegaPlusNat hc t 2 := not_omegaPlusNat_two_of (m := 3) le_rfl (Or.inl hp)
  have hs : Sec7Hyp hc n t := ⟨h5, hnot, ⟨3, by norm_num, Or.inl hp⟩, hlarge⟩
  have hC := h78 G M Q Z B hc n t h5 hlarge hnot 3 (by norm_num) (Or.inl hp)
  have hnN : n = 10 ∧ Nat.card (hc.CN t) = Nat.card Q * Nat.card Z ^ 9 := by
    unfold Conc78 at hC
    rcases hC with ⟨-, h1, h2⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · exact ⟨h1, h2⟩
    all_goals omega
  obtain ⟨Z0, hZ0⟩ := hc.exists_centre ht
  have hZN := sec7ctr_Z0_le_CN hc hs hZ0
  have hZc := hZcard G M Q Z B hc n t hs Z0 hZ0
  have hQH : Q ≤ H0 M Z := hc.Q_le_H0'
  have hQN : Q ≤ hc.CN t := sec8_Q_le_CN hc ht
  have hCNR : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
  have hRH0 : Rt M (LB M Q B) t ≤ H0 M Z := hc.Rt_le_H0 t
  have hCNH0 : hc.CN t ≤ H0 M Z := hCNR.trans hRH0
  have hZ0H0 : Z0 ≤ H0 M Z := hZ0.le.trans hRH0
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have hbar := bar_card_mul_card_of_le (M := H0 M Z) hQN hCNH0
  have hbarZ := bar_card_mul_card_of_le (M := H0 M Z) hQZ0 hZ0H0
  have hbarN : Nat.card (bar (H0 M Z) Q (hc.CN t)) = Nat.card Z ^ 9 := by
    rw [hnN.2] at hbar
    exact Nat.eq_of_mul_eq_mul_right hQpos (by rw [hbar]; ring)
  have hbarZq : Nat.card (bar (H0 M Z) Q Z0) = Nat.card Z := by
    rw [hZc] at hbarZ
    exact Nat.eq_of_mul_eq_mul_right hQpos (by rw [hbarZ]; ring)
  have hNR : bar (H0 M Z) Q (hc.CN t) ≤ bar (H0 M Z) Q (Rt M (LB M Q B) t) :=
    Subgroup.map_mono (fun a ha => hCNR ha)
  have hRM : bar (H0 M Z) Q (Rt M (LB M Q B) t) ≤
      Subgroup.normalizer ((cen (bar (H0 M Z) Q (hc.CN t)) : Subgroup _) : Set _) := by
    rintro _ ⟨r, hr, rfl⟩
    have hrR : (r : G) ∈ Rt M (LB M Q B) t := Subgroup.mem_subgroupOf.mp hr
    have hrN : (r : G) ∈ Subgroup.normalizer ((hc.CN t : Subgroup G) : Set G) :=
      Subgroup.mem_normalizer_fintype fun x hx => hc.CN_conj_mem ht hrR hx
    exact mem_normalizer_cen_of_mem_normalizer _
      (mk_mem_normalizer_bar_of_normalizer (M := H0 M Z) hQN r hrN)
  obtain ⟨hnR, hRq⟩ : QuotSat (bar (H0 M Z) Q (Rt M (LB M Q B) t)) (bar (H0 M Z) Q (hc.CN t))
      (IsOmegaPlus 3 (Nat.card Z)) :=
    quotSat_bar_of (fun X Y _ _ e h => IsOmegaPlus.congr e h) hQN hCNR hRH0 hp.quotSat
  haveI := hnR
  obtain ⟨r0, -, hr0, -⟩ := hc.hyp.cp
  have hqa : ∃ a : ℕ, 2 ≤ a ∧ Nat.card Z = 2 ^ a := by
    refine ⟨r0, ?_, hr0⟩
    by_contra hlt
    have h4 := hc.hyp.q4
    rw [hr0] at h4
    interval_cases r0 <;> simp at h4
  obtain ⟨hRs, hRn, hRcard⟩ := isOmegaPlus_three_facts hqa hRq
  haveI := hRs
  have hnc : ¬ IsMulCommutative (↥(bar (H0 M Z) Q (Rt M (LB M Q B) t)) ⧸
      (bar (H0 M Z) Q (hc.CN t)).subgroupOf (bar (H0 M Z) Q (Rt M (LB M Q B) t))) := fun h => by
    obtain ⟨x, y, hxy⟩ := hRn
    exact hxy (h.is_comm.comm x y)
  have hperfRN := (TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative hnc).commutator_eq_top
  obtain ⟨E, hER, hEperf, hEN, -⟩ := exists_perfect_sup_eq hNR hperfRN
  have hEc := Smith81.perfect_centralizes_of_semilinAct (Smith81.semilinAct_Z H₂)
    (P := E) (hER.trans hRM) (Group.isPerfect_def.mpr hEperf)
  have hRC : bar (H0 M Z) Q (Rt M (LB M Q B) t) ≤
      Subgroup.centralizer ((cen (bar (H0 M Z) Q (hc.CN t)) : Subgroup _) : Set _) := by
    rw [← hEN]
    refine sup_le (fun p hp => Subgroup.mem_centralizer_iff.mpr fun y hy => (hEc p hp y hy).symm)
      (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
    have hy' : y ∈ cen (bar (H0 M Z) Q (hc.CN t)) := hy
    rw [cen_eq] at hy'
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy').2 x hx).symm
  have hcen : cen (bar (H0 M Z) Q (hc.CN t)) = bar (H0 M Z) Q Z0 := by
    refine le_antisymm (fun y hy => ?_) (bar_centre_le_cen hc hZ0 hZN)
    have hyN : y ∈ bar (H0 M Z) Q (hc.CN t) := by
      have hy' : y ∈ cen (bar (H0 M Z) Q (hc.CN t)) := hy
      rw [cen_eq] at hy'
      exact (Subgroup.mem_inf.mp hy').1
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hyN
    have hxC : (x : G) ∈ hc.CN t := Subgroup.mem_subgroupOf.mp hx
    refine Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ((hZ0 x).mpr
      ⟨hCNR hxC, fun r hr => ?_⟩))
    have hrH : r ∈ H0 M Z := hRH0 hr
    have hrb : QuotientGroup.mk' (Q.subgroupOf (H0 M Z)) ⟨r, hrH⟩ ∈
        bar (H0 M Z) Q (Rt M (LB M Q B) t) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hr)
    have h1 := Subgroup.mem_centralizer_iff.mp (hRC hrb) _ hy
    exact (mk_comm_iff (M := H0 M Z) x ⟨r, hrH⟩).mp h1
  have hcard : Nat.card (cen (bar (H0 M Z) Q (hc.CN t))) = Nat.card Z := by
    rw [hcen]
    exact hbarZq
  have hW : Width (bar (H0 M Z) Q (hc.CN t)) (cen (bar (H0 M Z) Q (hc.CN t))) 4 := by
    show Nat.card (bar (H0 M Z) Q (hc.CN t)) =
      Nat.card (cen (bar (H0 M Z) Q (hc.CN t))) ^ (2 * 4 + 1)
    rw [hbarN, hcard]
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have h9 := op6_ge_pow_nine _ hq4
  have hc1 : Nat.card (cen (bar (H0 M Z) Q (hc.CN t))) *
      (Nat.card (cen (bar (H0 M Z) Q (hc.CN t))) ^ 2 - 1) <
      Nat.card Z ^ 6 * ((Nat.card Z ^ 2 - 1) * ((Nat.card Z ^ 3 - 1) * (Nat.card Z ^ 4 - 1))) := by
    rw [hcard]
    refine lt_of_lt_of_le ?_ h9
    calc Nat.card Z * (Nat.card Z ^ 2 - 1) < Nat.card Z * Nat.card Z ^ 2 :=
          Nat.mul_lt_mul_of_pos_left
            (by have := Nat.one_le_pow 2 _ (by omega : 0 < Nat.card Z); omega)
            (by omega)
      _ = Nat.card Z ^ 3 := by ring
      _ ≤ Nat.card Z ^ 9 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hc2 : Nat.card (cen (bar (H0 M Z) Q (hc.CN t))) ^ 3 *
      (Nat.card (cen (bar (H0 M Z) Q (hc.CN t))) ^ 6 - 1) <
      Nat.card Z ^ 6 * ((Nat.card Z ^ 2 - 1) * ((Nat.card Z ^ 3 - 1) * (Nat.card Z ^ 4 - 1))) := by
    rw [hcard]
    refine lt_of_lt_of_le ?_ h9
    calc Nat.card Z ^ 3 * (Nat.card Z ^ 6 - 1) < Nat.card Z ^ 3 * Nat.card Z ^ 6 :=
          Nat.mul_lt_mul_of_pos_left
            (by have := Nat.one_le_pow 6 _ (by omega : 0 < Nat.card Z); omega)
            (pow_pos (by omega : 0 < Nat.card Z) 3)
      _ = Nat.card Z ^ 9 := by ring
  have hc3 : Nat.card (cen (bar (H0 M Z) Q (hc.CN t))) ^ 2 *
      (Nat.card (cen (bar (H0 M Z) Q (hc.CN t))) ^ 4 - 1) <
      Nat.card Z ^ 6 * ((Nat.card Z ^ 2 - 1) * ((Nat.card Z ^ 3 - 1) * (Nat.card Z ^ 4 - 1))) := by
    rw [hcard]
    refine lt_of_lt_of_le ?_ h9
    calc Nat.card Z ^ 2 * (Nat.card Z ^ 4 - 1) < Nat.card Z ^ 2 * Nat.card Z ^ 4 :=
          Nat.mul_lt_mul_of_pos_left
            (by have := Nat.one_le_pow 4 _ (by omega : 0 < Nat.card Z); omega)
            (pow_pos (by omega : 0 < Nat.card Z) 2)
      _ = Nat.card Z ^ 6 := by ring
      _ ≤ Nat.card Z ^ 9 := Nat.pow_le_pow_right (by omega) (by norm_num)
  exact secondCfgCaseE6Four_of_large ⟨H₂, hall⟩ hW hgen h4i hNR hRC hnR hRn hRcard hc1 hc2 hc3
    hcB₂

end CFSG.RankThree.GF2n.Stroth80
