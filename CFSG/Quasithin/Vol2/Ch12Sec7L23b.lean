module

public import CFSG.Quasithin.Vol2.Ch12Sec2Statements
public import CFSG.Quasithin.SteinbergBSConjugateOrbits
public import CFSG.Quasithin.Vol2.Ch12Sec7L24

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits E3
open scoped IsMulCommutative

namespace S127

variable {G : Type} [Group G] [Finite G]

theorem mem_L_of_orderOf_three (h128 : Stmt12_2_8) {T L V : Subgroup G} (h : Hyp1271 G T L V)
    {x : G} (hxM : x ∈ Subgroup.normalizer (L : Set G)) (hx3 : orderOf x = 3) : x ∈ L := by
  rcases h128 G T L V h.hyp with h1 | (he | hL32) | ⟨-, h3⟩
  · rw [← h1]
    exact Subgroup.subset_closure ⟨hxM, 1, by rw [pow_one, ← hx3, pow_orderOf_eq_one]⟩
  · exfalso
    obtain ⟨e⟩ := he
    have h135 := dvd_card_quot_pCore h.hatA6 e
    rw [nat_card_alternatingGroup, Nat.card_fin] at h135
    exact absurd h135 (by decide)
  · exfalso
    have h135 := dvd_card_quot_pCore h.hatA6 (MulEquiv.refl _)
    rcases hL32 with ⟨-, hM⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · rw [card_of_statedPSL (by norm_num) hM] at h135
      exact absurd h135 (by decide)
    all_goals exact absurd h0 (by norm_num)
  · rw [h3]
    exact Subgroup.subset_closure ⟨hxM, hx3⟩

theorem not_orderOf_three_of_mem_centralizer (h1222 : Stmt12_2_2) (h128 : Stmt12_2_8)
    {T L V : Subgroup G} (h : Hyp1271 G T L V) {x : G}
    (hxM : x ∈ Subgroup.normalizer (L : Set G)) (hxV : x ∈ Subgroup.centralizer (V : Set G)) :
    orderOf x ≠ 3 := by
  intro hx3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxL := mem_L_of_orderOf_three h128 h hxM hx3
  have hxO : x ∈ pCoreOf 2 L := by
    rw [← inf_centralizer_eq_of_1222 h1222 h]
    exact ⟨hxL, hxV⟩
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 L) ⟨x, hxO⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h3 := orderOf_dvd_of_pow_eq_one hk'
  rw [hx3] at h3
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

theorem card_autOn_L {L V : Subgroup G} (h : HatA6Quot L V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) : Nat.card (autOn L V) = 1080 := by
  have h1080 := card_quot_of_hatA6Quot h
  obtain ⟨_, -⟩ := h
  let eQ : ↥L ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf L ≃* ↥(autOn L V) :=
    (QuotientGroup.quotientMulEquivOfEq (ker_autOnSurj hLV).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (autOnSurj_surjective hLV))
  rw [← Nat.card_congr eQ.toEquiv, h1080]

omit [Finite G] in
theorem card_orbitIn_mul_card_stab' {W : Type*} [CommGroup W] [Finite W]
    (H : Subgroup (MulAut W)) (a : W) :
    Nat.card (Orbit.orbitIn H a) * Nat.card ↥(H ⊓ MulAction.stabilizer (MulAut W) a) =
      Nat.card H := by
  classical
  have horb : Orbit.orbitIn H a = MulAction.orbit ↥H a := by
    ext w
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, hh⟩, rfl⟩
    · rintro ⟨h, rfl⟩
      exact ⟨h, h.2, rfl⟩
  have hstab : MulAction.stabilizer ↥H a =
      (H ⊓ MulAction.stabilizer (MulAut W) a).subgroupOf H := by
    ext h
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff,
      MulAction.mem_stabilizer_iff]
    exact ⟨fun h1 => ⟨h.2, h1⟩, fun h1 => h1.2⟩
  have hcard : Nat.card (MulAction.stabilizer ↥H a) =
      Nat.card ↥(H ⊓ MulAction.stabilizer (MulAut W) a) := by
    rw [hstab]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [horb, ← hcard, Nat.card_congr (MulAction.orbitEquivQuotientStabilizer ↥H a), mul_comm]
  exact (MulAction.stabilizer ↥H a).card_mul_index

theorem relIndex_z (h1222 : Stmt12_2_2) {T L V : Subgroup G} {t z : G}
    (hS : Setting1274 G T L V t z) : (Subgroup.centralizer ({z} : Set G)).relIndex L = 45 := by
  obtain ⟨z₀, -, t₀, -, h45, h18, horb⟩ := orbits_of_1222 h1222 hS.hyp
  have hzV : z ∈ V := (Subgroup.mem_inf.1 hS.z_mem).1
  have hodd := not_two_dvd_relIndex hS.hyp.hyp hS.T_le_Gz
  rcases horb z hzV hS.z_ne_one with ⟨l, hl, hlz⟩ | ⟨l, hl, hlz⟩
  · rw [← relIndex_centralizer_conj hl, hlz, h45]
  · rw [← hlz, relIndex_centralizer_conj hl] at h18
    exact absurd ⟨9, h18⟩ hodd

omit [Finite G] in
theorem autOn_le_normalizer_autOn {T L V : Subgroup G}
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) :
    autOn T V ≤ Subgroup.normalizer (autOn L V : Set (MulAut ↥V)) :=
  CFSG.Quasithin.AutOn.autOn_le_normalizer_autOn hTL

theorem card_le_three (h1222 : Stmt12_2_2) (h2 : Lemma12_7_2) (h128 : Stmt12_2_8)
    {T L V : Subgroup G} {t z : G} (hS : Setting1274 G T L V t z) {P : Subgroup G}
    (hP3 : IsPGroup 3 P)
    (hPM : P ≤ Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({z} : Set G)) :
    Nat.card P ≤ 3 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hcomm, -, hTV⟩ := card_eq_of_1222 h1222 hS.hyp
  have := hcomm
  have hy := hS.hyp.hyp
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hy.irrPlus.2.2.1
  have hzV : z ∈ V := (Subgroup.mem_inf.1 hS.z_mem).1
  have hPV : P ≤ Subgroup.normalizer (V : Set G) := by
    intro p hp
    obtain ⟨-, -, hall⟩ := ((h1222 G T hy.simple hy.nonabelian hy.qtke hy.sylow).resolve_left
      hy.notAlt) L hy.maximal hy.faithful hy.quasisimple
    rcases (hall V hy.irrPlus).2.1 p (hPM hp).1 with h | h
    · exact SteinbergBS.mem_normalizer_of_conjugate_eq h
    · exfalso
      have hz' : z ∈ V ⊓ CFSG.conjugate V p := by
        refine Subgroup.mem_inf.2 ⟨hzV, ?_⟩
        rw [SteinbergBS.mem_conjugate_iff,
          Subgroup.mem_centralizer_singleton_iff.1 (hPM hp).2, mul_inv_cancel_right]
        exact hzV
      rw [h, Subgroup.mem_bot] at hz'
      exact hS.z_ne_one hz'
  set φ := A4.actionOn V P hPV with hφ
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro p hp1
    have hpC : (p : G) ∈ Subgroup.centralizer (V : Set G) := (A4.actionOn_eq_one_iff hPV p).1 hp1
    by_contra hne
    obtain ⟨k, hk⟩ := hP3 p
    have hpk : (p : G) ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hpk)
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hj
      exact hne (Subtype.ext hj)
    obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
    have hq3 : orderOf ((p : G) ^ 3 ^ j') = 3 := by
      rw [orderOf_pow' _ (by positivity), hj, Nat.gcd_eq_right (pow_dvd_pow 3 (Nat.le_succ j')),
        pow_succ, Nat.mul_div_cancel_left _ (by positivity)]
    have hqM : (p : G) ^ 3 ^ j' ∈ Subgroup.normalizer (L : Set G) :=
      Subgroup.pow_mem _ (hPM p.2).1 _
    have hqC : (p : G) ^ 3 ^ j' ∈ Subgroup.centralizer (V : Set G) := Subgroup.pow_mem _ hpC _
    exact not_orderOf_three_of_mem_centralizer h1222 h128 hS.hyp hqM hqC hq3
  have hT2 : IsPGroup 2 (autOn T V) :=
    (hy.sylow.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTV).symm).map (conjAct V)
  have hφL : ∀ p : ↥P,
      φ p ∈ autOn L V ⊓ MulAction.stabilizer (MulAut ↥V) (⟨z, hzV⟩ : ↥V) := by
    intro p
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have hpMV : φ p ∈ hS.hyp.hyp.MVbar :=
        (A4.mem_autOn_iff inf_le_right).2 ⟨⟨p, (hPM p.2).1, hPV p.2⟩, rfl⟩
      obtain ⟨-, h1, -⟩ := h2 G T L V hS.hyp
      rcases h1 with h1 | ⟨h1, -⟩
      · rw [h1] at hpMV
        exact hpMV
      · rw [h1] at hpMV
        obtain ⟨k, hk⟩ := exists_pow_mem_of_mem_sup hT2
          (autOn_le_normalizer_autOn hy.normalizes hTV hLV) hpMV
        obtain ⟨m, hm⟩ := hP3 p
        have hpm : φ p ^ 3 ^ m = 1 := by rw [← map_pow, hm, map_one]
        have hcop : Nat.Coprime (2 ^ k) (orderOf (φ p)) := by
          obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
            (orderOf_dvd_of_pow_eq_one hpm)
          rw [hi]
          exact Nat.Coprime.pow _ _ (by norm_num)
        exact (Subgroup.zpowers_le.2 hk) (A4.mem_zpowers_pow_of_coprime hcop)
    · rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
      apply Subtype.ext
      rw [A4.actionOn_apply_coe]
      show (p : G) * z * (p : G)⁻¹ = z
      rw [Subgroup.mem_centralizer_singleton_iff.1 (hPM p.2).2, mul_inv_cancel_right]
  have h24 : Nat.card ↥(autOn L V ⊓ MulAction.stabilizer (MulAut ↥V) (⟨z, hzV⟩ : ↥V)) = 24 := by
    have h1 := card_orbitIn_mul_card_stab' (autOn L V) (⟨z, hzV⟩ : ↥V)
    rw [card_orbitIn_autOn hLV, relIndex_z h1222 hS, card_autOn_L hS.hyp.hatA6 hLV] at h1
    omega
  have hdvd : Nat.card P ∣ 24 := by
    rw [← h24, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    refine Subgroup.card_dvd_of_le ?_
    rintro _ ⟨p, rfl⟩
    exact hφL p
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hP3
  rw [hn] at hdvd ⊢
  by_contra hlt
  have hn2 : 2 ≤ n := by
    by_contra hn2
    interval_cases n <;> simp_all
  have h9 : 3 ^ 2 ∣ 24 := (pow_dvd_pow 3 hn2).trans hdvd
  norm_num at h9

end S127

end CFSG.Quasithin.H13
