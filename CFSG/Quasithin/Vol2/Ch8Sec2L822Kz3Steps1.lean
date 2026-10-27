module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822Kz3Steps1d
public import CFSG.Quasithin.Vol2.Ch8Sec2L822Kz3Tail
public import CFSG.Quasithin.Vol2.Ch8Sec2L822KzSetup

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem kzPCoreCentralizerNeBot_kz3 {G : Type} [Group G] {z : G} (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1) :
    CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ≠ ⊥ := by
  set Gz : Subgroup G := Subgroup.centralizer ({z} : Set G) with hGz
  have hzGz : z ∈ Gz := by
    rw [hGz, Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
  have hzpow2 : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hfwd : ∀ g ∈ Gz, ∀ x ∈ Subgroup.zpowers z, g * x * g⁻¹ ∈ Subgroup.zpowers z := by
    intro g hg x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hcomm : Commute g z := (Subgroup.mem_centralizer_iff.mp hg z (Set.mem_singleton z)).symm
    have hfix : g * z ^ k * g⁻¹ = z ^ k := by
      rw [(hcomm.zpow_right k).eq, mul_inv_cancel_right]
    rw [hfix]
    exact Subgroup.zpow_mem_zpowers z k
  intro hbot
  have hle : Subgroup.zpowers z ≤ CFSG.Open.pCoreOf 2 Gz := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ ?_
    · exact Subgroup.zpowers_le.mpr hzGz
    · intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · exact hfwd g hg x
      · intro hx
        have h1 := hfwd g⁻¹ (Subgroup.inv_mem _ hg) _ hx
        have h2 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
        rw [← h2]
        exact h1
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzpow2]; norm_num)
  have hz0 : z ∈ CFSG.Open.pCoreOf 2 Gz := hle (Subgroup.mem_zpowers z)
  rw [hbot, Subgroup.mem_bot] at hz0
  exact hz1 hz0

theorem kz3_steps12 {G : Type} [Group G] [Finite G] {T L I : Subgroup G}
    (hyp : Hyp7_0_2 G T L I) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hAut : KzAutE9Perfect_kz3)
    {H : Subgroup G} (hXi : IsXi T (twoResidual H))
    (hrel : (CFSG.Open.pCoreOf 2 (twoResidual H)).relIndex (twoResidual H) = 9)
    {z : G} (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1)
    (hHz : H ≤ Subgroup.centralizer ({z} : Set G)) (hTz : T ≤ Subgroup.centralizer ({z} : Set G))
    {P Lz : Subgroup G} (hPX : P ≤ twoResidual H) (hP3 : IsPGroup 3 P) (hPc : Nat.card P = 9)
    (hcon : Kz134Concl_kz (Subgroup.centralizer ({z} : Set G)) T (twoResidual H) P)
    (hLzG : Lz ≤ Subgroup.centralizer ({z} : Set G)) (hTLz : T ≤ Subgroup.normalizer (Lz : Set G))
    (hLzF : Lz ∈ lFamily T)
    (hLzq : CFSG.Quasithin.IsAlt 6 (↥Lz ⧸ CFSG.pCore 2 ↥Lz) ∨
      CFSG.Quasithin.IsHat (↥Lz ⧸ CFSG.pCore 2 ↥Lz) (alternatingGroup (Fin 6))) :
    ∃ K : Subgroup G, K ∈ cComp (Subgroup.centralizer ({z} : Set G)) ∧ Lz ≤ K ∧
      twoResidual H ≤ K ∧ T ≤ Subgroup.normalizer (K : Set G) ∧
      CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) ∧
      Kz134Tail_kz (Subgroup.centralizer ({z} : Set G)) T K P := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Gz : Subgroup G := Subgroup.centralizer ({z} : Set G) with hGz
  have hpC : CFSG.Open.pCoreOf 2 Gz ≠ ⊥ := kzPCoreCentralizerNeBot_kz3 hz1 hz2
  have hTsyl : IsSylowTwoOf T Gz := isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow hTz
  have hqtke := hyp.fsu.qtke
  have hsimple := hyp.fsu.simple
  have hnab := hyp.fsu.nonabelian
  have hSQ := sqtkHyp_quotient_of_pCoreOf_ne_bot hqtke hsimple hnab hpC
  have hrk : CFSG.Open.SQTKTauCeti.StronglyQuasithin (↥Gz ⧸ CFSG.pCore 2 ↥Gz) := hSQ.sqt
  have hA37Q : CFSG.Quasithin.A37Statement (↥Gz ⧸ CFSG.pCore 2 ↥Gz) := h37 _ hSQ
  have hXH : twoResidual H ≤ H := by
    rw [F6.twoResidual_eq_oTwoUpper H]
    exact oTwoUpper_le H
  have hXGz : twoResidual H ≤ Gz := hXH.trans hHz
  obtain ⟨-, hTX, -, p, hp, hp2, hxp, hrelp, -⟩ := hXi
  have hp3 : p = 3 := by
    rcases hrelp with h | ⟨h, -⟩
    · rw [hrel] at h
      have hlt : p < 4 := by
        by_contra hc
        have hc' : 4 ≤ p := Nat.le_of_not_lt hc
        have h16 : 4 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hc' 2
        norm_num at h16
        linarith
      interval_cases p <;> first | rfl | (norm_num at h)
    · rw [hrel] at h
      have hlt : p < 3 := by
        by_contra hc
        have hc' : 3 ≤ p := Nat.le_of_not_lt hc
        have h27 : 3 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hc' 3
        norm_num at h27
        linarith
      interval_cases p <;> first | rfl | (norm_num at h)
  subst hp3
  have hXexp : ∀ x ∈ twoResidual H, x ^ 3 ∈ CFSG.Open.pCoreOf 2 (twoResidual H) := hxp
  have hPexp : ∀ q ∈ P, q ^ 3 = 1 := by
    intro q hq
    have hq3 : q ^ 3 ∈ P := P.pow_mem hq 3
    have hq3' : q ^ 3 ∈ CFSG.Open.pCoreOf 2 (twoResidual H) := hXexp q (hPX hq)
    have hinf : P ⊓ CFSG.Open.pCoreOf 2 (twoResidual H) = ⊥ :=
      (IsPGroup.disjoint_of_ne 3 2 (by norm_num) P _ hP3 (kzIsPGroupPCoreOf_kz3 _)).eq_bot
    have hmem : q ^ 3 ∈ P ⊓ CFSG.Open.pCoreOf 2 (twoResidual H) := ⟨hq3, hq3'⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    exact hmem
  have hPG : P ≤ Gz := (hPX).trans hXGz
  obtain ⟨K0, hK0, hLzK0⟩ :=
    lemma_1_2_4_exists hqtke hsimple hnab h37 h39 hpC hTsyl hLzG hLzF
  have hK0G : K0 ≤ Gz := le_of_mem_cComp hK0
  have hK0n := lemma_1_2_4_normal hqtke hsimple hnab h37 h38 hpC hTsyl hLzF hLzK0 hK0 hTLz
  have hGzN : Gz ≤ Subgroup.normalizer (K0 : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK0G).mp hK0n
  have hTGz : T ≤ Gz := hTsyl.1
  have hTN : T ≤ Subgroup.normalizer (K0 : Set G) := fun t ht => hGzN (hTGz ht)
  have hK0perf : ⁅K0, K0⁆ = K0 := perfect_of_mem_cComp hK0
  have hrelX : (CFSG.Open.pCoreOf 2 (twoResidual H)).relIndex (twoResidual H) = 9 := hrel
  have hcon' : Gz ≤ Subgroup.normalizer ((twoResidual H : Subgroup G) : Set G) ∨
      ∃ L' ∈ cComp Gz, CFSG.IsQuasisimple (↥L' ⧸ CFSG.pCore 2 ↥L') ∧
        twoResidual H ≤ conjClosure L' T ∧ Kz134Tail_kz Gz T L' P := hcon
  rcases hcon' with h0 | ⟨L', hL', hqL', hXL', htail'⟩
  ·
    have hcomm := kzCase0Comm_kz3 hXGz h0 hK0G hK0perf hAut hrelX hXexp
    exact (kzKey_kz3 hrk hLzG hLzK0 hK0G hLzq hPG hP3 hPc hPexp
      (fun q hq k hk => hcomm q (hPX hq) k hk)).elim
  · by_cases hLK : L' = K0
    ·
      rw [hLK] at hqL' htail' hXL'
      have hXK0 : twoResidual H ≤ K0 := by
        refine hXL'.trans (conjClosure_le ?_)
        intro t ht z' hz'
        exact (Subgroup.mem_normalizer_iff.mp (hTN ht) z').mp hz'
      exact ⟨K0, hK0, hLzK0, hXK0, hTN, hqL', htail'⟩
    ·
      exfalso
      have hcomm := kzConjComm_kz3 hA37Q hL' hK0 hLK hTGz hTN hXL'
      exact kzKey_kz3 hrk hLzG hLzK0 hK0G hLzq hPG hP3 hPc hPexp
        (fun q hq k hk => hcomm q (hPX hq) k hk)

end CFSG.Quasithin.H13
