module

public import CFSG.Quasithin.Vol2.Ch12Sec7L23c
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem9Odd
public import CFSG.Quasithin.Vol2.Ch12Sec7L23a

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits E3
open scoped IsMulCommutative

namespace S127

variable {G : Type} [Group G] [Finite G]

theorem isSylowTwoOf_H {T L V : Subgroup G} {t z : G} (hS : Setting1274 G T L V t z)
    {H : Subgroup G} (hHs : IsHStar T (Subgroup.normalizer (L : Set G)) H) :
    QuasithinUnique.IsSylowTwoOf T H :=
  ⟨hHs.1.1, hS.hyp.hyp.sylow.1,
    fun h2 => hS.hyp.hyp.sylow.2 (h2.trans (Subgroup.relIndex_dvd_index_of_le hHs.1.1))⟩

theorem normalizer_T_le (h331 : Stmt3_3_1) {T L V : Subgroup G} {t z : G}
    (hS : Setting1274 G T L V t z) :
    Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have hy := hS.hyp.hyp
  have h3 := (h331 G T hy.simple hy.nonabelian hy.qtke hy.sylow).2 L hy.maximal hy.quasisimple
  rw [hy.conjClosure_eq] at h3
  exact h3.2.2.2.1

theorem minParabolic_H (h331 : Stmt3_3_1) {T L V : Subgroup G} {t z : G}
    (hS : Setting1274 G T L V t z) {H : Subgroup G}
    (hHs : IsHStar T (Subgroup.normalizer (L : Set G)) H) :
    MinParabolic H T (H ⊓ Subgroup.normalizer (L : Set G)) :=
  Sec1219Odd.minParabolic_of_isHStar hHs (isSylowTwoOf_H hS hHs) hS.hyp.hyp.normalizes
    (normalizer_T_le h331 hS)

theorem odd_dvd_three (h1222 : Stmt12_2_2)
    (h1211 : Stmt12_2_11') (h128 : Stmt12_2_8)
    (h331 : Stmt3_3_1) (hE : E2.E22StatementC) (h2 : Lemma12_7_2) (h10 : Lemma12_7_10)
    (h11 : Lemma12_7_11) (h22 : Lemma12_7_22) {T L V : Subgroup G} {t z : G}
    (hS : Setting1274 G T L V t z) {H : Subgroup G}
    (hHs : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHz : H ≤ Subgroup.centralizer ({z} : Set G)) :
    (∃ C : Subgroup G, C ≤ H ⊓ Subgroup.normalizer (L : Set G) ∧ Nat.card C = 3) ∧
      ∀ g ∈ H ⊓ Subgroup.normalizer (L : Set G), Odd (orderOf g) → orderOf g ∣ 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hy := hS.hyp.hyp
  have hn2 := nParam_eq_two h1222 h1211 h10 h11 h22 hS hHs hHz
  have hn1 : 1 < E1.nParam H := by rw [hn2]; norm_num
  have hmin := minParabolic_H h331 hS hHs
  have hSQ : SQTKGroup ↥H := sqtkGroup_of_pCoreOf_ne_bot hy.qtke hy.simple hy.nonabelian hHs.1.2
  obtain ⟨m, -, -, hB⟩ :=
    E2.e22BorelLift hE (E2.e22TorusCover_of_facts e22TorusFacts_holds) hmin hSQ hn1
  obtain ⟨-, R, hRT, hR2, hRN, ⟨C, hCM, hCodd, hCidx⟩, hall⟩ := hB
  obtain ⟨-, hMO, -, -⟩ := hall C hCM hCodd hCidx
  have hC3 := ((nParam_le_two h1222 h1211 hS hHs hHz).2 hn2 C hCM hCodd hCidx)
  have hCle : Nat.card C ≤ 3 :=
    card_le_three h1222 h2 h128 hS hC3.2 (hCM.trans (inf_le_inf_right _ hHz) |>.trans
      (by rw [inf_comm]))
  have hCcard : Nat.card C = 3 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hC3.2
    have h1 : 1 < Nat.card C := (Subgroup.one_lt_card_iff_ne_bot _).2 hC3.1
    rw [hn] at h1 hCle ⊢
    rcases n with _ | _ | n
    · norm_num at h1
    · norm_num
    · have : 3 ^ 2 ≤ 3 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  refine ⟨⟨C, hCM, hCcard⟩, fun g hg hgo => ?_⟩
  have hgO : g ∈ H ⊓ Subgroup.normalizer (L : Set G) ⊓ oTwoUpper H :=
    ⟨hg, mem_oTwoUpper_of_odd hg.1 hgo⟩
  have hgCR := hMO hgO
  have hCR : C ≤ Subgroup.normalizer (R : Set G) := hCM.trans hRN
  have hCRinf : C ⊓ R = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxC, hxR⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨k, hk⟩ := hR2 ⟨x, hxR⟩
    have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 := orderOf_dvd_of_pow_eq_one hk'
    have h2 : orderOf x ∣ 3 := by
      rw [← hCcard]
      exact Subgroup.orderOf_dvd_natCard C hxC
    have h3 : orderOf x ∣ Nat.gcd (2 ^ k) 3 := Nat.dvd_gcd h1 h2
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left k (by norm_num)), Nat.dvd_one,
      orderOf_eq_one_iff] at h3
    rw [h3]
    exact Subgroup.one_mem _
  have hcard : Nat.card ↥(C ⊔ R) = 3 * Nat.card R := by
    have h1 := B6.relIndex_inf_eq_relIndex_sup hCR
    rw [hCRinf, Subgroup.relIndex_bot_left] at h1
    have h2 := Subgroup.relIndex_mul_card (H := C) (K := C ⊔ R)
    rw [inf_of_le_left le_sup_left, ← h1, hCcard] at h2
    rw [← h2, mul_comm]
  have hdvd : orderOf g ∣ 3 * Nat.card R := hcard ▸ Subgroup.orderOf_dvd_natCard _ hgCR
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.1 hR2
  rw [hb] at hdvd
  have hcop : Nat.Coprime (orderOf g) (2 ^ b) :=
    Nat.Coprime.pow_right b (Nat.coprime_two_right.2 hgo)
  exact hcop.dvd_of_dvd_mul_right hdvd

theorem lemma12_7_23_three (h1222 : Stmt12_2_2)
    (h1211 : Stmt12_2_11') (h128 : Stmt12_2_8) (h331 : Stmt3_3_1) (hE : E2.E22StatementC)
    (h2 : Lemma12_7_2) (h10 : Lemma12_7_10) (h11 : Lemma12_7_11) (h22 : Lemma12_7_22)
    {T L V : Subgroup G} {t z : G} (hS : Setting1274 G T L V t z) {H : Subgroup G}
    (hHs : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHz : H ≤ Subgroup.centralizer ({z} : Set G)) :
    L1 T L V ⊔ T = H ⊓ Subgroup.normalizer (L : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hy := hS.hyp.hyp
  set M := Subgroup.normalizer (L : Set G) with hMdef
  obtain ⟨⟨C, hCM, hC3⟩, hodd⟩ :=
    odd_dvd_three h1222 h1211 h128 h331 hE h2 h10 h11 h22 hS hHs hHz
  obtain ⟨hcomm, -, -⟩ := card_eq_of_1222 h1222 hS.hyp
  have := hcomm
  obtain ⟨-, -, -, -, -, ⟨-, hset, -, -⟩, -⟩ := h2 G T L V hS.hyp
  have hL1 : L1 T L V ∈ {I : Subgroup G | I ≤ P1 T L V ∧ T ≤ Subgroup.normalizer (I : Set G) ∧
      oTwoUpper I = I ∧ (pCoreOf 2 I).relIndex I = 3} := by
    rw [hset]
    exact Set.mem_insert _ _
  obtain ⟨-, hTL1, -, hL13⟩ := hL1
  have h3L1 : ∀ g ∈ H ⊓ M, orderOf g = 3 → g ∈ L1 T L V := by
    intro g hg hg3
    have hgL := mem_L_of_orderOf_three h128 hS.hyp hg.2 hg3
    have hgC := centralizer_z_le h1222 h2 h128 hS ⟨hgL, hHz hg.1⟩
    exact mem_oTwoUpper_of_odd ⟨hgL, hgC⟩ (by rw [hg3]; decide)
  obtain ⟨⟨y, hyC⟩, hy3⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [hC3])
  rw [Subgroup.orderOf_mk] at hy3
  have hyHM : y ∈ H ⊓ M := hCM hyC
  have hyL1 : y ∈ L1 T L V := h3L1 y hyHM hy3
  have hO2T : pCoreOf 2 (L1 T L V) ≤ T := by
    have hSyl : QuasithinUnique.IsSylowTwoOf T (L1 T L V ⊔ T) :=
      ⟨le_sup_right, hy.sylow.1,
        fun h2' => hy.sylow.2 (h2'.trans (Subgroup.relIndex_dvd_index_of_le le_sup_right))⟩
    refine (le_pCoreOf_of_le_normalizer 2 (pCoreOf_le 2 _ |>.trans le_sup_left) ?_
      (pCoreOf_isPGroup 2 _)).trans (pCoreOf_two_le_of_isSylowTwoOf hSyl)
    exact sup_le (le_normalizer_pCoreOf 2 _)
      (hTL1.trans (normalizer_le_normalizer_pCoreOf 2 _))
  have hyO : y ∉ pCoreOf 2 (L1 T L V) := by
    intro hyO
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 (L1 T L V)) ⟨y, hyO⟩
    have hk' : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 := orderOf_dvd_of_pow_eq_one hk'
    rw [hy3] at h1
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1
    omega
  have hL1le : L1 T L V ≤ pCoreOf 2 (L1 T L V) ⊔ Subgroup.zpowers y := by
    have hle : pCoreOf 2 (L1 T L V) ⊔ Subgroup.zpowers y ≤ L1 T L V :=
      sup_le (pCoreOf_le 2 _) ((Subgroup.zpowers_le).2 hyL1)
    have hmul := Subgroup.relIndex_mul_relIndex (pCoreOf 2 (L1 T L V))
      (pCoreOf 2 (L1 T L V) ⊔ Subgroup.zpowers y) (L1 T L V) le_sup_left hle
    rw [hL13] at hmul
    rcases (Nat.dvd_prime Nat.prime_three).1 (Dvd.intro_left _ hmul) with h1 | h3
    · exact Subgroup.relIndex_eq_one.1 h1
    · exfalso
      rw [h3] at hmul
      have h1 : (pCoreOf 2 (L1 T L V)).relIndex
          (pCoreOf 2 (L1 T L V) ⊔ Subgroup.zpowers y) = 1 := by
        omega
      have hle' := Subgroup.relIndex_eq_one.1 h1
      exact hyO (hle' (le_sup_right (a := pCoreOf 2 (L1 T L V)) (Subgroup.mem_zpowers y)))
  have hL1HM : L1 T L V ≤ H ⊓ M :=
    hL1le.trans (sup_le (hO2T.trans (le_inf hHs.1.1 hy.normalizes))
      ((Subgroup.zpowers_le).2 hyHM))
  have hLT : L1 T L V ⊔ T ≤ H ⊓ M := sup_le hL1HM (le_inf hHs.1.1 hy.normalizes)
  refine le_antisymm hLT ?_
  set n := (L1 T L V ⊔ T).relIndex (H ⊓ M) with hn
  have hnodd : ¬ 2 ∣ n := by
    intro h2'
    have hdvd : n ∣ T.relIndex (H ⊓ M) := Subgroup.relIndex_dvd_of_le_left _ le_sup_right
    exact hy.sylow.2 ((h2'.trans hdvd).trans (Subgroup.relIndex_dvd_index_of_le
      (le_inf hHs.1.1 hy.normalizes)))
  have hn1 : n = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hne
    have hp2 : p ≠ 2 := fun h => hnodd (h ▸ hpn)
    have hmul := Subgroup.relIndex_mul_card (H := L1 T L V ⊔ T) (K := H ⊓ M)
    rw [inf_of_le_left hLT] at hmul
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨⟨g, hg⟩, hgp⟩ := exists_prime_orderOf_dvd_card' p
      ((hpn.trans (Dvd.intro _ hmul)) : p ∣ Nat.card ↥(H ⊓ M))
    rw [Subgroup.orderOf_mk] at hgp
    have hgo : Odd (orderOf g) := by rw [hgp]; exact hp.odd_of_ne_two hp2
    have hp3 : p = 3 := by
      have := hodd g hg hgo
      rw [hgp] at this
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 this
    have h3LT : 3 ∣ Nat.card ↥(L1 T L V ⊔ T) := by
      have := Subgroup.orderOf_dvd_natCard (L1 T L V ⊔ T)
        (le_sup_left (b := T) hyL1)
      rwa [hy3] at this
    have h9 : 3 ^ 2 ∣ Nat.card ↥(H ⊓ M) := by
      rw [← hmul, sq]
      exact mul_dvd_mul (hp3 ▸ hpn) h3LT
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 h9
    have hKP : IsPGroup 3 ↥(K.map (H ⊓ M).subtype) := by
      refine IsPGroup.of_card (n := 2) ?_
      rw [Subgroup.card_map_of_injective (H ⊓ M).subtype_injective, hK]
    have hKle : K.map (H ⊓ M).subtype ≤ M ⊓ Subgroup.centralizer ({z} : Set G) := by
      rintro _ ⟨k, -, rfl⟩
      exact ⟨k.2.2, hHz k.2.1⟩
    have := card_le_three h1222 h2 h128 hS hKP hKle
    rw [Subgroup.card_map_of_injective (H ⊓ M).subtype_injective, hK] at this
    norm_num at this
  exact Subgroup.relIndex_eq_one.1 hn1

end S127

end CFSG.Quasithin.H13
