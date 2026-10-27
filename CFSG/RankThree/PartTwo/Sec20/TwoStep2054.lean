module

import CFSG.RankThree.PartTwo.Sec18.Item182
import CFSG.RankThree.PartTwo.Sec3.Sims321
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411L3Group
import CFSG.RankThree.PartTwo.Sec4.RonanKChevTwoLThree
public import CFSG.RankThree.PartTwo.Sec20.OneTools

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)

variable {G : Type} [Group G] [Finite G]

private theorem sup_pCoreOf_eq_of_hKC {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20 G A M L N c T)
    (h2 : ∀ C : Subgroup T, C.Characteristic → C ≠ ⊥ →
      ¬ kTwenty M c ⊔ T ≤ Subgroup.normalizer ((C.map T.subtype : Subgroup G) : Set G))
    (hKC : kTwenty M c ∈ oTwoComponentsIn M) {n : ℕ} (hn : Odd n)
    (hiso : Nonempty (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c) ≃*
      projSL 3 (GaloisField 2 n))) :
    kTwenty M c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) = kTwenty M c ⊔ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := kTwenty M c with hKdef
  have hM := hT.mem_scriptM.1
  have hKM : K ≤ M := kTwenty_le_of_hyp201 hT.toHyp201
  have hTM : T ≤ M := hT.sylow.le
  have hXM : K ⊔ T ≤ M := sup_le hKM hTM
  have hT2 : IsPGroup 2 T := hT.sylow.isPGroup
  have hT1 : T ≠ ⊥ := by
    intro hbot
    have := pCoreOf_le_of_isSylowOf hT.sylow
    rw [hbot, le_bot_iff] at this
    exact pCoreOf_ne_bot_of_isMaximalTwoLocal hM this
  have hF : CFSG.generalizedFitting ↥(K ⊔ T) = CFSG.pCore 2 ↥(K ⊔ T) := by
    obtain ⟨P, hP, hP2, hMP⟩ := hM.1
    exact generalizedFitting_eq_of_pCoreOf_le hT.charTwoType ⟨P, hP, hP2, hMP⟩ hXM
      ((pCoreOf_le_of_isSylowOf hT.sylow).trans le_sup_right)
  have hKX : K ∈ oTwoComponentsIn (K ⊔ T) := by
    obtain ⟨-, ⟨-, hsn, -⟩⟩ := mem_oTwoComponentsIn_iff.mp hKC
    exact Sec18.mem_oTwoComponentsIn_of_le hKC le_sup_left
      (Sec18.isSubnormal_subgroupOf_of_le hsn hXM)
  have hTX : CFSG.ABGLocalTools.IsSylowOf 2 T (K ⊔ T) := hT.sylow.of_le le_sup_right hXM
  rcases Sec3.Sims321.item321Split_holds G (K ⊔ T) K T n hF hKX
      (hXM.trans (le_normalizer_normalClosureIn M c)) hTX rfl hn hiso with (hJ | hV) | hLQ
  · exfalso
    have : (CFSG.higherElemThompson T 0).Characteristic := higherElemThompson_zero_characteristic
    refine h2 (CFSG.higherElemThompson T 0) this ?_ hJ
    intro hbot
    apply thompsonOf_ne_bot hT2 hT1
    rw [Sec3.thompsonOf, hbot, Subgroup.map_bot]
  · exfalso
    have : (CFSG.omegaOneCenter (⊤ : Subgroup T)).Characteristic :=
      omegaOneCenter_top_characteristic
    refine h2 (CFSG.omegaOneCenter (⊤ : Subgroup T)) this ?_ ?_
    · intro hbot
      apply omegaZOf_ne_bot hT2 hT1
      rw [Sec3.omegaZOf, hbot, Subgroup.map_bot]
    · have hZV := omegaZOf_le_omegaZOf_pCoreOf hF hTX
      have hKZ : K ≤ Subgroup.centralizer (Sec3.omegaZOf T : Set G) := by
        have h1 : ⁅Sec3.omegaZOf T, K⁆ = ⊥ :=
          le_bot_iff.mp (hV ▸ Subgroup.commutator_mono hZV le_rfl)
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h1
        exact Subgroup.le_centralizer_iff.mp h1
      refine sup_le (hKZ.trans (Subgroup.centralizer_le_normalizer _)) ?_
      exact Subgroup.le_normalizer.trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
  · exact hLQ

private theorem projectiveSL_eq_one_of_commute_three {n : ℕ} (hn : Odd n)
    {x c : projectiveSL 3 (GaloisField 2 n)} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hxc : x * c = c * x) (hc2 : c ^ 2 = 1) : c = 1 := by
  have h2n : 2 ^ n % 3 = 2 := by
    obtain ⟨k, rfl⟩ := hn
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hcard : Nat.card (GaloisField 2 n) % 3 = 2 := by
    rw [GaloisField.card 2 n hn.pos.ne', h2n]
  let e : Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n) ≃*
      projectiveSL 3 (GaloisField 2 n) :=
    (slThreeEquivProjSL hn).trans (CFSG.RankThree.PartTwo.KFacts.L34.projSLEquivProjectiveSL 3 _)
  have hx' : (e.symm x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hx1' : e.symm x ≠ 1 := fun h => hx1 (by simpa using congrArg e h)
  have hxc' : e.symm x * e.symm c = e.symm c * e.symm x := by
    rw [← map_mul, ← map_mul, hxc]
  have hc2' : (e.symm c) ^ 2 = 1 := by rw [← map_pow, hc2, map_one]
  have key := CFSG.RankThree.PartTwo.Sec4.RonanKChevTwo.sl_three_eq_one_of_commute hcard hx' hx1'
    hxc' hc2'
  simpa using congrArg e key

private theorem eq_one_of_pow_two_of_commute {n : ℕ} (hn : Odd n)
    {v : projectiveSL 3 (GaloisField 2 n)} (hv3 : v ^ 3 = 1) (hv1 : v ≠ 1) (j : ℕ) :
    ∀ u : projectiveSL 3 (GaloisField 2 n), u ^ 2 ^ j = 1 → u * v = v * u → u = 1 := by
  induction j with
  | zero => intro u hu _; simpa using hu
  | succ j ih =>
    intro u hu huv
    have hc : Commute u v := huv
    have hz2 : (u ^ 2 ^ j) ^ 2 = 1 := by
      rw [← pow_mul, ← pow_succ]
      exact hu
    by_cases hz : u ^ 2 ^ j = 1
    · exact ih u hz huv
    · exact absurd (projectiveSL_eq_one_of_commute_three hn hv3 hv1 (hc.pow_left (2 ^ j)).symm hz2)
        hz

private theorem eq_one_of_conj_eq_one {P : Type*} [Group P] (hZ : Subgroup.center P = ⊥)
    {h : P} (hh : MulAut.conj h = 1) : h = 1 := by
  have hc : h ∈ Subgroup.center P := by
    rw [Subgroup.mem_center_iff]
    intro w
    have hw := congrArg (fun φ : MulAut P => φ w) hh
    simp only [MulAut.conj_apply, MulAut.one_apply] at hw
    exact (mul_inv_eq_iff_eq_mul.mp hw).symm
  rw [hZ, Subgroup.mem_bot] at hc
  exact hc

private theorem mul_comm_of_conj_comm {P : Type*} [Group P] (hZ : Subgroup.center P = ⊥)
    {g v : P} (h : MulAut.conj g * MulAut.conj v = MulAut.conj v * MulAut.conj g) :
    g * v = v * g := by
  have h1 : MulAut.conj ((v * g)⁻¹ * (g * v)) = 1 := by
    simp only [map_mul, map_inv]
    rw [h, inv_mul_cancel]
  exact (inv_mul_eq_one.mp (eq_one_of_conj_eq_one hZ h1)).symm

private theorem conj_mem_pCoreOf_of_mem {K M : Subgroup G}
    (hMK : M ≤ Subgroup.normalizer (K : Set G))
    (hMO : M ≤ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 K : Subgroup G) : Set G))
    {q : G} (hq : ∀ k ∈ K, q * k * q⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K) {m : G} (hm : m ∈ M) :
    ∀ k ∈ K, m * q * m⁻¹ * k * (m * q * m⁻¹)⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K := by
  intro k hk
  have hk₀ : m⁻¹ * k * m ∈ K := by
    have h := (Subgroup.mem_normalizer_iff.mp (hMK (M.inv_mem hm)) k).mp hk
    rwa [inv_inv] at h
  have h1 := (Subgroup.mem_normalizer_iff.mp (hMO hm) _).mp (hq _ hk₀)
  have e : m * q * m⁻¹ * k * (m * q * m⁻¹)⁻¹ * k⁻¹ =
      m * (q * (m⁻¹ * k * m) * q⁻¹ * (m⁻¹ * k * m)⁻¹) * m⁻¹ := by
    group
  rw [e]
  exact h1

private theorem mem_of_two_elem_comm {M N T K : Subgroup G} {c : G} {n : ℕ} (hn : Odd n)
    (hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hKM : K ≤ M)
    (hMK : M ≤ Subgroup.normalizer (K : Set G))
    (hMO : M ≤ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 K : Subgroup G) : Set G))
    (hcK : c ∈ K) (hc : orderOf c = 3) {Q : Subgroup G} (hQT : Q ≤ T)
    (hQK : ∀ q ∈ Q, ∀ k ∈ K, q * k * q⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K)
    (hTQ : ∀ t ∈ T, ∃ a ∈ K, ∃ b ∈ Q, a * b = t)
    (φ : K ⧸ CFSG.pCore 2 K ≃* projSL 3 (GaloisField 2 n))
    (hCN : ∀ q ∈ M, (∀ k ∈ K, q * k * q⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K) → q ∈ N)
    {x : G} (hxM : x ∈ M) (hxc : x * c = c * x) {j : ℕ} (hj : x ^ 2 ^ j = 1) : x ∈ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc3 : c ^ 3 = 1 := by
    rw [← hc]
    exact pow_orderOf_eq_one c
  have hTM : T ≤ M := hTsyl.le
  have hxz : IsPGroup 2 (Subgroup.zpowers x) := by
    rintro ⟨g, hg⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨j, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hj, one_zpow]
  obtain ⟨S, hS, hxS⟩ := exists_isSylowOf_le hxz (Subgroup.zpowers_le.mpr hxM)
  obtain ⟨m, hmM, hSm⟩ := Sec18.exists_map_conj_eq_of_isSylowOf hTsyl hS
  have hxS' : x ∈ S := hxS (Subgroup.mem_zpowers x)
  rw [hSm] at hxS'
  obtain ⟨t, ht, hxt⟩ := Subgroup.mem_map.mp hxS'
  change m * t * m⁻¹ = x at hxt
  obtain ⟨a, ha, b, hb, hab⟩ := hTQ t ht
  have hbM : b ∈ M := hTM (hQT hb)
  have hk1 : m * a * m⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hMK hmM) a).mp ha
  have hq1M : m * b * m⁻¹ ∈ M := M.mul_mem (M.mul_mem hmM hbM) (M.inv_mem hmM)
  have hxdec : x = (m * a * m⁻¹) * (m * b * m⁻¹) := by
    rw [← hxt, ← hab]
    group
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := hMK hxM
  have hk1N : m * a * m⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hk1
  have hq1N : m * b * m⁻¹ ∈ Subgroup.normalizer (K : Set G) := hMK hq1M
  have hcN : c ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hcK
  have hdec : (⟨x, hxN⟩ : Subgroup.normalizer (K : Set G)) =
      ⟨m * a * m⁻¹, hk1N⟩ * ⟨m * b * m⁻¹, hq1N⟩ :=
    Subtype.ext hxdec
  have hρq : Sec3.Sims321.rho φ ⟨m * b * m⁻¹, hq1N⟩ = 1 :=
    (Sec3.Sims321.rho_eq_one_iff φ _).mpr (conj_mem_pCoreOf_of_mem hMK hMO (hQK b hb) hmM)
  have hρa : Sec3.Sims321.rho φ ⟨m * a * m⁻¹, hk1N⟩ =
      MulAut.conj (Sec3.Sims321.psi φ ⟨m * a * m⁻¹, hk1⟩) :=
    Sec3.Sims321.rho_eq_conj φ _ _ rfl
  have hρx : Sec3.Sims321.rho φ ⟨x, hxN⟩ =
      MulAut.conj (Sec3.Sims321.psi φ ⟨m * a * m⁻¹, hk1⟩) := by
    rw [hdec, map_mul, hρq, hρa, mul_one]
  have hρc : Sec3.Sims321.rho φ ⟨c, hcN⟩ = MulAut.conj (Sec3.Sims321.psi φ ⟨c, hcK⟩) :=
    Sec3.Sims321.rho_eq_conj φ _ _ rfl
  have hcomm : Sec3.Sims321.rho φ ⟨x, hxN⟩ * Sec3.Sims321.rho φ ⟨c, hcN⟩ =
      Sec3.Sims321.rho φ ⟨c, hcN⟩ * Sec3.Sims321.rho φ ⟨x, hxN⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hxc
  have hpow : Sec3.Sims321.rho φ ⟨x, hxN⟩ ^ 2 ^ j = 1 := by
    have h1 : (⟨x, hxN⟩ : Subgroup.normalizer (K : Set G)) ^ 2 ^ j = 1 :=
      Subtype.ext (by simpa using hj)
    have h2 := congrArg (Sec3.Sims321.rho φ) h1
    rwa [map_pow, map_one] at h2
  rw [hρx, hρc] at hcomm
  rw [hρx] at hpow
  have hZ : Subgroup.center (projectiveSL 3 (GaloisField 2 n)) = ⊥ :=
    Sec3.Sims321.center_projectiveSL_eq_bot
  set g := Sec3.Sims321.psi φ ⟨m * a * m⁻¹, hk1⟩ with hg
  set v := Sec3.Sims321.psi φ ⟨c, hcK⟩ with hv
  have hv3 : v ^ 3 = 1 := by
    have h3 : (⟨c, hcK⟩ : K) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [hv, ← map_pow, h3, map_one]
  have hv1 : v ≠ 1 := by
    intro h
    have hcO : c ∈ CFSG.Open.pCoreOf 2 K := (Sec3.Sims321.psi_eq_one_iff φ ⟨c, hcK⟩).mp h
    obtain ⟨i, hi⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K) ⟨c, hcO⟩
    have hci : c ^ 2 ^ i = 1 := by simpa using congrArg Subtype.val hi
    have h3 : 3 ∣ 2 ^ i := by
      rw [← hc]
      exact orderOf_dvd_of_pow_eq_one hci
    have h32 := Nat.prime_three.dvd_of_dvd_pow h3
    norm_num at h32
  have hgpow : g ^ 2 ^ j = 1 := by
    apply eq_one_of_conj_eq_one hZ
    rw [map_pow]
    exact hpow
  have hgv : g * v = v * g := mul_comm_of_conj_comm hZ hcomm
  have hg1 : g = 1 := eq_one_of_pow_two_of_commute hn hv3 hv1 j g hgpow hgv
  have hρx1 : Sec3.Sims321.rho φ ⟨x, hxN⟩ = 1 := by
    rw [hρx, hg1, map_one]
  exact hCN x hxM ((Sec3.Sims321.rho_eq_one_iff φ ⟨x, hxN⟩).mp hρx1)

private theorem exists_isSylowOf_le_inf_of_hO2N {M N : Subgroup G} {c : G}
    (hO2N : CFSG.Open.pCoreOf 2 (kTwenty M c) ≤ N)
    (hpar : Sec18.IsMaxParabolicRankTwo (((kTwenty M c ⊓ N).subgroupOf (kTwenty M c)).map
        (QuotientGroup.mk' (CFSG.pCore 2 (kTwenty M c))))) :
    ∃ S₀ : Subgroup G, S₀ ≤ kTwenty M c ⊓ N ∧
      CFSG.ABGLocalTools.IsSylowOf 2 S₀ (kTwenty M c) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := kTwenty M c with hKdef
  obtain ⟨-, S, hS⟩ := hpar
  have hodd : ¬ 2 ∣ (((K ⊓ N).subgroupOf K).map
      (QuotientGroup.mk' (CFSG.pCore 2 K))).index := by
    intro h
    have hle : (S : Subgroup (K ⧸ CFSG.pCore 2 K)) ≤
        ((K ⊓ N).subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 K)) :=
      Subgroup.le_normalizer.trans hS
    exact S.not_dvd_index (h.trans (Subgroup.index_dvd_of_le hle))
  have hker : (QuotientGroup.mk' (CFSG.pCore 2 K)).ker ≤ (K ⊓ N).subgroupOf K := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    refine ⟨x.2, hO2N ?_⟩
    exact ⟨x, hx, rfl⟩
  rw [Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _) hker] at hodd
  obtain ⟨S₀, hS₀⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 (K ⊓ N)
  exact ⟨S₀, hS₀.le, isSylowOf_of_le_of_not_dvd hS₀ inf_le_left hodd⟩

theorem step2054Two_of {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20 G A M L N c T) (hc : orderOf c = 3)
    (h2 : ∀ C : Subgroup T, C.Characteristic → C ≠ ⊥ →
      ¬ kTwenty M c ⊔ T ≤ Subgroup.normalizer ((C.map T.subtype : Subgroup G) : Set G))
    (hKC : kTwenty M c ∈ oTwoComponentsIn M) {n : ℕ} (hn : Odd n)
    (hKs : Nonempty (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c) ≃* projSL 3 (GaloisField 2 n)))
    (hpar : Sec18.IsMaxParabolicRankTwo (((kTwenty M c ⊓ N).subgroupOf (kTwenty M c)).map
      (QuotientGroup.mk' (CFSG.pCore 2 (kTwenty M c)))))
    (hCN : ∀ q ∈ M, (∀ k ∈ kTwenty M c,
      q * k * q⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 (kTwenty M c)) → q ∈ N) :
    ¬ 2 ∣ (M ⊓ N).relIndex M ∧ ∃ T' : Subgroup G, Ctx20 G A M L N c T' ∧ T' ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := kTwenty M c with hKdef
  have hKM : K ≤ M := kTwenty_le_of_hyp201 hT.toHyp201
  have hTM : T ≤ M := hT.sylow.le
  have hMK : M ≤ Subgroup.normalizer (K : Set G) := le_normalizer_normalClosureIn M c
  have hMO : M ≤ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 K : Subgroup G) : Set G) :=
    (le_normalizer_normalClosureIn M c).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have hcK : c ∈ K := self_mem_normalClosureIn M c
  set Q := CFSG.Open.pCoreOf 2 (K ⊔ T) with hQdef
  have hQT : Q ≤ T := pCoreOf_le_of_isSylowOf (hT.sylow.of_le le_sup_right (sup_le hKM hTM))
  have hXQ : K ⊔ T ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hQK : ∀ q ∈ Q, ∀ k ∈ K, q * k * q⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K := by
    have hle : Q ⊓ K ≤ CFSG.Open.pCoreOf 2 K := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left)
      intro k hk
      exact mem_normalizer_inf_of_mem (hXQ (Subgroup.mem_sup_left hk))
        (Subgroup.le_normalizer hk)
    intro q hq k hk
    refine hle ⟨?_, ?_⟩
    · have h1 : k * q⁻¹ * k⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hXQ (Subgroup.mem_sup_left hk)) _).mp (Q.inv_mem hq)
      have : q * k * q⁻¹ * k⁻¹ = q * (k * q⁻¹ * k⁻¹) := by group
      rw [this]
      exact Q.mul_mem hq h1
    · have h1 : q * k * q⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hMK (hTM (hQT hq))) k).mp hk
      exact K.mul_mem h1 (K.inv_mem hk)
  have hLQ : K ⊔ Q = K ⊔ T := sup_pCoreOf_eq_of_hKC hT h2 hKC hn hKs
  have hTQ : ∀ t ∈ T, ∃ a ∈ K, ∃ b ∈ Q, a * b = t := by
    intro t ht
    have htX : t ∈ K ⊔ Q := by
      rw [hLQ]
      exact Subgroup.mem_sup_right ht
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right K Q
      (le_sup_left.trans hXQ)] at htX
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp htX
    exact ⟨a, ha, b, hb, hab⟩
  have hO2N : CFSG.Open.pCoreOf 2 K ≤ N := by
    intro q hq
    refine hCN q (hKM (CFSG.LieType.BorelTits.pCoreOf_le 2 K hq)) (fun k hk => ?_)
    have hkN : k ∈ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 K : Subgroup G) : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hk
    have h1 : k * q⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K :=
      (Subgroup.mem_normalizer_iff.mp hkN q⁻¹).mp ((CFSG.Open.pCoreOf 2 K).inv_mem hq)
    have e : q * k * q⁻¹ * k⁻¹ = q * (k * q⁻¹ * k⁻¹) := by group
    rw [e]
    exact (CFSG.Open.pCoreOf 2 K).mul_mem hq h1
  obtain ⟨φ⟩ := hKs
  have hkey : ∀ x ∈ M, x * c = c * x → ∀ j : ℕ, x ^ 2 ^ j = 1 → x ∈ N :=
    fun x hx hxc j hj =>
      mem_of_two_elem_comm hn hT.sylow hKM hMK hMO hcK hc hQT hQK hTQ φ hCN hx hxc hj
  obtain ⟨S₀, hS₀N, hS₀⟩ := exists_isSylowOf_le_inf_of_hO2N (M := M) (c := c) hO2N hpar
  have hTK : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ K) K := hT.sylow.inf_of_le_normalizer hKM hMK
  obtain ⟨k, hk, hkS⟩ := Sec18.exists_map_conj_eq_of_isSylowOf hTK hS₀
  have hTkN : T.map (MulAut.conj k).toMonoidHom ≤ N := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨a, ha, b, hb, hab⟩ := hTQ t ht
    have haT : a ∈ T := by
      have : a = t * b⁻¹ := by
        rw [← hab]
        group
      rw [this]
      exact T.mul_mem ht (T.inv_mem (hQT hb))
    have h1 : k * a * k⁻¹ ∈ N := hS₀N (hkS ▸ ⟨a, ⟨haT, ha⟩, rfl⟩) |>.2
    have hkM : k ∈ M := hKM hk
    have hbM : b ∈ M := hTM (hQT hb)
    have h2' : k * b * k⁻¹ ∈ N :=
      hCN (k * b * k⁻¹) (M.mul_mem (M.mul_mem hkM hbM) (M.inv_mem hkM))
        (conj_mem_pCoreOf_of_mem hMK hMO (hQK b hb) hkM)
    change k * t * k⁻¹ ∈ N
    have e : k * t * k⁻¹ = (k * a * k⁻¹) * (k * b * k⁻¹) := by
      rw [← hab]
      group
    rw [e]
    exact N.mul_mem h1 h2'
  have hTkM := isSylowOf_map_conj hT.sylow (hKM hk)
  have hodd : ¬ 2 ∣ (M ⊓ N).relIndex M :=
    not_dvd_relIndex_of_isSylowOf_le hTkM (le_inf hTkM.le hTkN) inf_le_left
  refine ⟨hodd, ?_⟩
  obtain ⟨Sc, hSc⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 (M ⊓ Subgroup.centralizer {c})
  have hScN : Sc ≤ M ⊓ N := by
    intro x hx
    have hxC : x ∈ M ⊓ Subgroup.centralizer {c} := hSc.le hx
    have hxc : x * c = c * x := Subgroup.mem_centralizer_singleton_iff.mp hxC.2
    obtain ⟨j, hj⟩ := hSc.isPGroup ⟨x, hx⟩
    have hj' : x ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    exact Subgroup.mem_inf.mpr ⟨hxC.1, hkey x hxC.1 hxc j hj'⟩
  obtain ⟨T', hT', hScT'⟩ := exists_isSylowOf_le hSc.isPGroup hScN
  have hT'M : CFSG.ABGLocalTools.IsSylowOf 2 T' M :=
    isSylowOf_of_le_of_not_dvd hT' inf_le_left hodd
  have heq : T' ⊓ Subgroup.centralizer {c} = Sc :=
    hSc.eq_of_le (le_inf hScT' (hSc.le.trans inf_le_right)) (inf_le_inf_right _ hT'M.le)
      (hT'M.isPGroup.to_le inf_le_left)
  refine ⟨T', ⟨hT.toHyp201, hT'M, ?_⟩, hT'.le.trans inf_le_right⟩
  rw [heq]
  exact hSc

end CFSG.RankThree.PartTwo.Sec20
