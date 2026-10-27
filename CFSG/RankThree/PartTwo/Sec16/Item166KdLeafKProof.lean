module

public import CFSG.RankThree.PartTwo.Sec16.Item166KdNarrowK
public import CFSG.RankThree.PartTwo.J2Residue.Config
import CFSG.RankThree.PartTwo.Sec16.Item166KdE1
import CFSG.RankThree.PartTwo.Sec16.Item166KdA6Quot
import CFSG.RankThree.PartTwo.Sec16.Item166CtrJ2Config
import CFSG.RankThree.PartTwo.Sec16.Kcd166.A6Step
import CFSG.RankThree.PartTwo.Sec16.Kcd166.BlackburnScalar
import CFSG.GroupTheory.PerfectChiefStability
import CFSG.GroupTheory.ChiefFactorScalar

public section

namespace CFSG.RankThree.PartTwo.Sec16.Kd166

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec17 CFSG.RankThree.PartTwo.Sec16 CFSG.GH74.GLS
open scoped Pointwise commutatorElement

theorem step166ThetaDCommK_of_beta
    (hbeta : ∀ {G : Type} [Group G] [Finite G],
      (∀ q : ℕ, q.Prime → 3 < q → CFSG.Assembly.RankThreeEven.localRank q G < 3) →
      ∀ {L LB Θ : Subgroup G} {d : G}, J2Residue.J2Config L d LB →
        CFSG.Open.pCoreOf 2 LB ≠ ⊥ → Group.IsSolvable Θ → ¬ 3 ∣ Nat.card Θ →
        CFSG.Open.pCoreOf 2 Θ = ⊥ → CFSG.Open.pCoreOf 2 LB ≤ Θ →
        Θ ≤ Subgroup.centralizer ({d} : Set G) →
        L ⊓ Subgroup.normalizer (Subgroup.zpowers d : Set G) ≤
          Subgroup.normalizer (Θ : Set G) → False) :
    Step166ThetaDCommK := by
  intro G _ _ A c L Y₀ h hJ d hdA hd1 hdc K hK hKeq hKA6 hAK hNK hO2
  classical
  set LB := lB A (Subgroup.closure {c, d}) with hLBdef
  set Θ := inSubgroup (aschbacherSolvableCore 3) K with hΘdef
  have hD13 : Sec13Data G A c L := h.toSec13Data
  have hcA : c ∈ A := (Sec13.zpowers_mem_omegaA_iff.mp h.zpowers_mem_omegaA).1
  have hJK : LB ≤ K := by
    rw [hKeq]
    exact le_sup_left
  have hLBperf : Group.IsPerfect ↥LB := by
    rw [hLBdef, Ctr166.lB_closure_eq_residual h hJ hdA hd1 hdc]
    exact Item148HJ.residual_isPerfect L d
  have hΘs : Group.IsSolvable ↥Θ := (Sec6.theta_solvable_and_not_dvd K).1
  have hΘ3 : ¬ 3 ∣ Nat.card ↥Θ := (Sec6.theta_solvable_and_not_dvd K).2
  have hΘK : Θ ≤ K := Sec6.theta_le K
  have hKΘ : K ≤ Subgroup.normalizer (Θ : Set G) := Sec6.le_normalizer_theta K
  have hΘd : Θ ≤ Subgroup.centralizer ({d} : Set G) :=
    inSubgroup_theta_le_centralizer_of_mem_thetaComponentsAt hK
  have hΘ2 : CFSG.Open.pCoreOf 2 Θ = ⊥ := by
    have hle : CFSG.Open.pCoreOf 2 Θ ≤ CFSG.Open.pCoreOf 2 K :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 Θ).trans hΘK)
        (hKΘ.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
          (CFSG.pCore 2 ↥Θ)))
        ((CFSG.pCore_isPGroup (p := 2) (G := ↥Θ)).map Θ.subtype)
    rw [hO2] at hle
    exact le_bot_iff.mp hle
  have hΘ3' : CFSG.Open.pCoreOf 3 Θ = ⊥ := by
    have h3 : IsPGroup 3 ↥(CFSG.Open.pCoreOf 3 Θ) :=
      (CFSG.pCore_isPGroup (p := 3) (G := ↥Θ)).map Θ.subtype
    have hle : CFSG.Open.pCoreOf 3 Θ ≤ Θ := CFSG.LieType.BorelTits.pCoreOf_le 3 Θ
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rcases Subgroup.bot_or_exists_ne_one (CFSG.Open.pCoreOf 3 Θ) with hb | ⟨x, hx, hx1⟩
    · exact hb
    · exfalso
      obtain ⟨k, hk⟩ := h3 ⟨x, hx⟩
      have hord : orderOf x ∣ 3 ^ k := by
        apply orderOf_dvd_of_pow_eq_one
        have := congrArg Subtype.val hk
        simpa using this
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hord
      have hj0 : j ≠ 0 := by
        intro h0
        rw [h0, pow_zero] at hj
        exact hx1 (orderOf_eq_one_iff.mp hj)
      have h3x : 3 ∣ orderOf x := by
        rw [hj]
        exact dvd_pow_self 3 hj0
      have hxΘ : orderOf x ∣ Nat.card ↥Θ := by
        have := Subgroup.orderOf_dvd_natCard Θ (hle hx)
        simpa using this
      exact hΘ3 (h3x.trans hxΘ)
  have hU : CFSG.Open.pCoreOf 2 LB = ⊥ := by
    by_contra hU
    have hJ2 := Ctr166.j2Config_lB_closure h hJ hdA hd1 hdc
    have hrk : ∀ q : ℕ, q.Prime → 3 < q → CFSG.Assembly.RankThreeEven.localRank q G < 3 :=
      fun q hq hq3 => h.localRank_lt q hq hq3
    have hUΘ : CFSG.Open.pCoreOf 2 LB ≤ Θ := by
      obtain ⟨-, -, -, -, -, -, hθO⟩ :=
        solvable_prime_complement_core_characterization (H := ↥LB) Nat.prime_three
      have h1 : CFSG.Open.pCoreOf 2 LB ≤ inSubgroup (aschbacherSolvableCore 3) LB :=
        Subgroup.map_mono (hθO 2 Nat.prime_two (by norm_num))
      rw [← inf_theta_eq_of_eq_sup hJK hKeq] at h1
      exact h1.trans inf_le_right
    have hYΘ : L ⊓ Subgroup.normalizer (Subgroup.zpowers d : Set G) ≤
        Subgroup.normalizer (Θ : Set G) :=
      (inf_comm L _ ▸ hNK).trans (Sec6.normalizer_le_normalizer_theta K)
    exact hbeta hrk hJ2 hU hΘs hΘ3 hΘ2 hUΘ hΘd hYΘ
  have hJΘ : LB ≤ Subgroup.normalizer (Θ : Set G) := hJK.trans hKΘ
  have hAΘ : A ≤ Subgroup.normalizer (Θ : Set G) :=
    hAK.trans (Sec6.normalizer_le_normalizer_theta K)
  have hLBc : LB ≤ Subgroup.centralizer ({c} : Set G) :=
    (Sec14.lB_le_centralizer A (Subgroup.closure ({c, d} : Set G))).trans
      (Subgroup.centralizer_le (by
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact Subgroup.subset_closure (by simp)))
  have hAc : A ≤ Subgroup.centralizer ({c} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hD13.isElemAbelian.1.is_comm.comm ⟨a, ha⟩ ⟨c, hcA⟩)
  have hc3 : c ^ 3 = 1 := h.toSec14Std.isE27.1.2 c hcA
  obtain ⟨π, hπs, hπker⟩ := exists_alternatingGroup_quotient_lB h hJ hdA hd1 hdc
  refine CFSG.GroupTheory.commutator_eq_bot_of_forall_chief_pCoreOf hΘs hLBperf hJΘ hAΘ hΘ2 hΘ3'
    ?_
  intro r hr hr5 N M hNM hMP hHN hHM hmin
  haveI : Fact r.Prime := ⟨hr⟩
  set P := CFSG.Open.pCoreOf r Θ with hPdef
  have hP : IsPGroup r ↥P := (CFSG.pCore_isPGroup (p := r) (G := ↥Θ)).map Θ.subtype
  have hPΘ : P ≤ Θ := CFSG.LieType.BorelTits.pCoreOf_le r Θ
  have hHP : P ⊔ LB ⊔ A ≤ Subgroup.normalizer (P : Set G) :=
    sup_le (sup_le Subgroup.le_normalizer
      (hJΘ.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (CFSG.pCore r ↥Θ))))
      (hAΘ.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (CFSG.pCore r ↥Θ)))
  have hPM : ⁅M, P⁆ ≤ N :=
    CFSG.GroupTheory.commutator_le_of_chief_of_isPGroup hP (le_sup_left.trans le_sup_left) hHP
      hNM hMP hHN hHM hmin
  have hYN : LB ⊔ A ≤ Subgroup.normalizer (N : Set G) := by
    refine sup_le ?_ ?_
    · exact (le_sup_right.trans le_sup_left).trans hHN
    · exact le_sup_right.trans hHN
  have hYM : LB ⊔ A ≤ Subgroup.normalizer (M : Set G) := by
    refine sup_le ?_ ?_
    · exact (le_sup_right.trans le_sup_left).trans hHM
    · exact le_sup_right.trans hHM
  have hchief : CFSG.ABGLocalTools.IsChiefFactorUnder r (LB ⊔ A) M N := by
    refine CFSG.GroupTheory.isChiefFactorUnder_of_commutator_le hP hNM hMP hPM hYN hYM ?_
    intro K' h1 h2 h3
    exact hmin K' h1 h2 (by rw [sup_assoc]; exact h3)
  have hYc : LB ⊔ A ≤ Subgroup.centralizer ({c} : Set G) := sup_le hLBc hAc
  have hcM : c ∈ Subgroup.normalizer (M : Set G) := hHM (Subgroup.mem_sup_right hcA)
  have hcN : c ∈ Subgroup.normalizer (N : Set G) := hHN (Subgroup.mem_sup_right hcA)
  have hJM : LB ≤ Subgroup.normalizer (M : Set G) := (le_sup_right.trans le_sup_left).trans hHM
  have hJN : LB ≤ Subgroup.normalizer (N : Set G) := (le_sup_right.trans le_sup_left).trans hHN
  have hMΘ : M ≤ Θ := hMP.trans hPΘ
  rcases CFSG.GroupTheory.trivial_or_fixedPointFree_of_isChiefFactorUnder hchief hYc hcM hcN
    with htriv | hfpf
  ·
    have hModd : Odd (Nat.card ↥M) := by
      obtain ⟨k, hk⟩ := (hP.to_le hMP).exists_card_eq
      rw [hk]
      exact Odd.pow (hr.odd_of_ne_two (by omega))
    have hMN : M ≤ Subgroup.normalizer (N : Set G) := fun m hm => by
      rw [Subgroup.mem_normalizer_iff]
      intro n
      constructor
      · intro hn
        exact hchief.2.2.2.1 m hm n hn
      · intro hn
        have := hchief.2.2.2.1 m⁻¹ (M.inv_mem hm) _ hn
        simpa [mul_assoc] using this
    exact commutator_lB_le_of_forall_commutator_mem h hJ hdA hd1 hdc hK hKeq hMΘ hModd hNM.le
      hMN hcM hcN hJM hJN htriv
  ·
    have hker : ∀ k : ↥LB, π k = 1 → ∀ m ∈ M, (k : G) * m * (k : G)⁻¹ * m⁻¹ ∈ N := by
      intro k hk m hm
      have hkd : (k : G) ∈ Subgroup.zpowers d := by
        have := hπker k hk
        rw [hU, bot_sup_eq] at this
        exact this
      have hmd : m ∈ Subgroup.centralizer ({d} : Set G) := hΘd (hMΘ hm)
      have hkm : (k : G) * m = m * (k : G) := by
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hkd
        rw [← hj]
        have hc : Commute d m := (Subgroup.mem_centralizer_singleton_iff.mp hmd).symm
        exact (hc.zpow_left j).eq
      have : (k : G) * m * (k : G)⁻¹ * m⁻¹ = 1 := by
        rw [hkm]
        group
      rw [this]
      exact N.one_mem
    have hloc := Kcd166.card_le_sq_of_localRank_lt hr (h.localRank_lt r hr (by omega))
    have hsc : r % 3 = 1 → ∃ w : ℕ, ∀ m ∈ M, c * m * c⁻¹ * (m ^ w)⁻¹ ∈ N := fun hr3 =>
      CFSG.GroupTheory.exists_pow_of_isChiefFactorUnder hr3 hchief hc3 hYc hcM hcN
    exact Kcd166.commutator_le_of_surjective_alternatingGroup_six Kcd166.blackburnScalarAut_holds
      hr5 hloc (hP.to_le hMP) hNM.le hchief.normal
      (fun x hx y hy => by
        have := hchief.2.2.2.2.1 x hx y hy
        rwa [commutatorElement_def] at this)
      hchief.2.2.2.2.2.1 hJM hJN π hπs hker hc3 hLBc hcM hcN hfpf hsc

theorem step166KCommD_of_beta
    (h143 : Sec14.Ronan148Q.Item143QS14) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h1514 : Item1514S17) (hMeets : Claim1715Meets)
    (hbeta : ∀ {G : Type} [Group G] [Finite G],
      (∀ q : ℕ, q.Prime → 3 < q → CFSG.Assembly.RankThreeEven.localRank q G < 3) →
      ∀ {L LB Θ : Subgroup G} {d : G}, J2Residue.J2Config L d LB →
        CFSG.Open.pCoreOf 2 LB ≠ ⊥ → Group.IsSolvable Θ → ¬ 3 ∣ Nat.card Θ →
        CFSG.Open.pCoreOf 2 Θ = ⊥ → CFSG.Open.pCoreOf 2 LB ≤ Θ →
        Θ ≤ Subgroup.centralizer ({d} : Set G) →
        L ⊓ Subgroup.normalizer (Subgroup.zpowers d : Set G) ≤
          Subgroup.normalizer (Θ : Set G) → False) :
    Step166KCommD :=
  step166KCommD_of_thetaDComm h143 h134 h48 h1514 hMeets
    (step166ThetaDComm_of_thetaDCommK h134 h48 h1514 hMeets (step166ThetaDCommK_of_beta hbeta))

end CFSG.RankThree.PartTwo.Sec16.Kd166
