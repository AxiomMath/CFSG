module

public import CFSG.Quasithin.Vol2.Ch11SecE3Glue
public import CFSG.Quasithin.Vol2.Ch10SecKHBC
public import CFSG.Quasithin.Vol2.Ch11SecBHBCore
public import CFSG.Quasithin.Vol2.Ch11SecKGBorelComm
public import CFSG.Quasithin.Vol2.Ch11SecB35C
public import CFSG.Quasithin.Vol2.Ch11SecB35G1
public import CFSG.Quasithin.Vol2.Ch11SecBNPSyl
public import CFSG.Quasithin.Vol2.Ch10SecQ3CI

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.H13
open CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem inf_eq_bot_of_odd_of_isPGroup {B P : Subgroup G} (hB : Odd (Nat.card B))
    (hP : IsPGroup 2 P) : B ⊓ P = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
  obtain ⟨k, hk⟩ := hP ⟨x, hx.2⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h2 : Odd (orderOf x) := Odd.of_dvd_nat hB (Subgroup.orderOf_dvd_natCard B hx.1)
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  rcases i with _ | i
  · exact orderOf_eq_one_iff.mp (by simpa using hi)
  · rw [hi] at h2
    exact absurd h2 (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero i⟩))

omit [Finite G] in
theorem mul_comm_of_subset {A B : Subgroup G} (h : (A : Set G) * (B : Set G) ⊆ B * A) :
    (B : Set G) * (A : Set G) = A * B := by
  refine Set.Subset.antisymm (fun x hx => ?_) h
  obtain ⟨b, hb, a, ha, rfl⟩ := hx
  obtain ⟨b', hb', a', ha', he⟩ := h ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, rfl⟩
  refine ⟨a'⁻¹, A.inv_mem ha', b'⁻¹, B.inv_mem hb', ?_⟩
  simp only at he ⊢
  rw [← mul_inv_rev, he, mul_inv_rev, inv_inv, inv_inv]

theorem mul_comm_of_le_sup {X T B : Subgroup G} (hT : IsSylowTwoOf T X) (hBX : B ≤ X)
    (hTQ : T ≤ pCoreOf 2 X ⊔ (T ⊓ Subgroup.normalizer (B : Set G))) :
    (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G) := by
  have hXO : X ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hOT : pCoreOf 2 X ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf hT
  have hle : T ⊓ Subgroup.normalizer (B : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 X : Set G) := inf_le_left.trans (hT.1.trans hXO)
  have hprod := Subgroup.coe_mul_of_right_le_normalizer_left (pCoreOf 2 X)
    (T ⊓ Subgroup.normalizer (B : Set G)) hle
  refine mul_comm_of_subset ?_
  rintro _ ⟨t, ht, b, hb, rfl⟩
  have ht' : t ∈ ((pCoreOf 2 X ⊔ (T ⊓ Subgroup.normalizer (B : Set G)) : Subgroup G) : Set G) :=
    hTQ ht
  rw [hprod] at ht'
  obtain ⟨q, hq, m, hm, rfl⟩ := ht'
  have hb₁ : m * b * m⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hm.2 b).mp hb
  have hq₁ : (m * b * m⁻¹)⁻¹ * q * (m * b * m⁻¹) ∈ pCoreOf 2 X := by
    have h := (Subgroup.mem_normalizer_iff.mp
      (hXO (X.inv_mem (hBX hb₁))) q).mp hq
    simpa [mul_assoc] using h
  refine ⟨m * b * m⁻¹, hb₁, (m * b * m⁻¹)⁻¹ * q * (m * b * m⁻¹) * m,
    T.mul_mem (hOT hq₁) hm.1, ?_⟩
  group

theorem exists_hall_cartan (hE22 : E2.E22StatementC) {T M H : Subgroup G}
    (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) (hK : quasithinIsQTKECat G)
    (hT : quasithinIsSylowTwo T) (hTM : T ≤ M) (hH : IsHStar T M H) (hn : 1 < E1.nParam H) :
    ∃ n : ℕ, E1.nParam H ≤ n ∧ ∃ B : Subgroup G,
      QuasithinUnique.Lin2.IsHallTwoPrimeOf B (H ⊓ M) ∧ (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧
      (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G) ∧
      ∃ b ∈ B, orderOf b = 2 ^ n - 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := H ⊓ M with hXdef
  have hTH : T ≤ H := hH.1.1
  have hTX : T ≤ X := le_inf hTH hTM
  have hTS : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo hT hTH
  obtain ⟨P, hP⟩ := exists_sylow_of_quasithinIsSylowTwo hT
  have hU : IsUniqueMaxOver H T X := by
    have := IsHStar.isUniqueMaxOver P (hP ▸ hH) (hP ▸ hTM)
    rwa [hP] at this
  have hnn : ¬ H ≤ Subgroup.normalizer (T : Set G) := by
    intro hNS
    have hTn : (T.subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hTS.1).mpr hNS
    exact absurd hn (not_lt.mpr (Vol2.Ch11.SecB.nParam_le_one_of_normal_sylow hTS.2.1 hTS.1 hTn
      fun A hAH hA2 => E1.le_of_isSylowIn_of_normal ⟨hTS.1, hTS.2.1, hTS.2.2⟩ hTn hAH hA2))
  have hmin : MinParabolic H T X := ⟨hTS, hnn, hU⟩
  have hns : ¬ Group.IsSolvable ↥H := fun hsol =>
    absurd hn (not_lt.mpr (E1.solvable_nParam_le_one hsol))
  obtain ⟨⟨K, hKc, hHK, -, hcases⟩, -⟩ := hE22.exists_cases hmin
    (sqtkGroup_of_pCoreOf_ne_bot hK hs hnab hH.1.2) hns
  obtain ⟨n, hn2, htype, ⟨S, hS, hBor⟩, hnH⟩ := E2.exists_borel_of_e22CasesC hn hcases
  obtain ⟨B, hB, hBab, hTQ⟩ := Vol2.Ch11.SecB.derivedHallBorel_core
    Vol2.Ch11.SecB.factBorelComm_holds hT hTH hTM hU hns hKc hHK
    (Vol2.Ch11.SecB.e22LieCases_of_e22CasesC hn hcases)
  have hTXS : IsSylowTwoOf T X := isSylowTwoOf_of_quasithinIsSylowTwo hT hTX
  refine ⟨n, hnH, B, hB, hBab, mul_comm_of_le_sup hTXS hB.1 hTQ, ?_⟩
  obtain ⟨d, hdN, hdo⟩ := Vol2.Ch10.SecB.factBorelCartan _ n hn2 htype _
    (isSylowTwoOf_top_subgroupOf hS)
  have hdM : (d : E2.StarQuot X H) ∈ E2.star X H (X ⊓ K) := by
    rw [hBor]
    exact ⟨d.2, coe_mem_normalizer hS.1 hdN⟩
  obtain ⟨⟨x, hxH⟩, hx, hxe⟩ := hdM
  have hxXK : x ∈ X ⊓ K := hx
  have hdvd : 2 ^ n - 1 ∣ orderOf x := by
    rw [← hdo, ← Subgroup.orderOf_coe d, ← hxe]
    have h := orderOf_map_dvd (QuotientGroup.mk' ((kerIn X H).subgroupOf H)) (⟨x, hxH⟩ : ↥H)
    rwa [← Subgroup.orderOf_coe] at h
  obtain ⟨a, r, hr, hxar⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  have hyo : orderOf (x ^ 2 ^ a) = r := by
    rw [orderOf_pow_of_dvd (by positivity) (by rw [hxar]; exact dvd_mul_right _ _), hxar,
      Nat.mul_div_cancel_left _ (by positivity)]
  have hodd : Odd (2 ^ n - 1) := Nat.Even.sub_odd (Nat.one_le_two_pow) (Nat.even_pow.mpr
    ⟨even_two, by omega⟩) odd_one
  have hdvr : 2 ^ n - 1 ∣ r := by
    rw [hxar] at hdvd
    exact (Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)).dvd_of_dvd_mul_left hdvd
  obtain ⟨b, hb, hbdvd⟩ := exists_mem_orderOf_dvd hTXS hB hTQ hB (X.pow_mem hxXK.1 _)
    (by rw [hyo]; exact hr)
  rw [hyo] at hbdvd
  have hfin : 2 ^ n - 1 ∣ orderOf b := hdvr.trans hbdvd
  exact ⟨b ^ (orderOf b / (2 ^ n - 1)), B.pow_mem hb _,
    orderOf_pow_orderOf_div (orderOf_pos b).ne' hfin⟩

theorem nParam_le_nPrime_of_e22 (hE22 : E2.E22StatementC) {T V M H : Subgroup G}
    (hV : IsElemAbelian 2 V) (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (h322 : E3.HypE322 T V) (hK : quasithinIsQTKECat G)
    (hM : IsUniqueM
      (Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G)) M)
    (hH : IsHStar T M H) (hn : 1 < E1.nParam H)
    (heq : H ⊓ M = H ⊓ Subgroup.normalizer (V : Set G))
    (hC : H ⊓ M ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (H ⊓ M)) :
    E1.nParam H ≤ (E3.nPrime (autI hV ⊤) : ℕ∞) := by
  have hT : quasithinIsSylowTwo T := ⟨h322.sylow.2.1, by
    rw [← Subgroup.relIndex_top_right]
    exact h322.sylow.2.2⟩
  have hTN : T ≤ Subgroup.normalizer (V : Set G) := h322.normal
  have hTM : T ≤ M := (B2F.le_normalizer_inf Subgroup.le_normalizer
    (B2F.le_normalizer_centralizer hTN)).trans hM.1.2
  obtain ⟨n, hnH, B, hB, hBab, hBT, b, hb, hbo⟩ :=
    exists_hall_cartan hE22 hs hnab hK hT hTM hH hn
  have hXN : H ⊓ M ≤ Subgroup.normalizer (V : Set G) := heq.le.trans inf_le_right
  have hBN : B ≤ Subgroup.normalizer (V : Set G) := hB.1.trans hXN
  have hBU : B ⊓ Subgroup.centralizer (V : Set G) = ⊥ := by
    have h1 : B ⊓ Subgroup.centralizer (V : Set G) ≤ B ⊓ pCoreOf 2 (H ⊓ M) :=
      le_inf inf_le_left ((inf_le_inf_right _ hB.1).trans hC)
    rw [inf_eq_bot_of_odd_of_isPGroup hB.2.1
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (H ⊓ M))] at h1
    exact le_bot_iff.mp h1
  have hTS : IsSylowTwoOf T (Subgroup.normalizer (V : Set G)) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hT hTN
  have hle : n ≤ E3.nPrime (autI hV ⊤) :=
    Vol2.Ch11.SecB.le_nPrime_autI hV hBN hTN hBU hTS hBab hB.2.1 hBT
      (Subgroup.zpowers_le.mpr hb) inferInstance (by rw [Nat.card_zpowers, hbo])
  exact hnH.trans (by exact_mod_cast hle)

theorem nParam_le_nPrime_of_e22_hyp (hE22 : E2.E22StatementC) {T V M H : Subgroup G}
    (hV : IsElemAbelian 2 V) (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hyp : E3.HypE336 T V M) (hH : IsHStar T M H) :
    E1.nParam H ≤ (E3.nPrime (autI hV ⊤) : ℕ∞) := by
  by_cases hn : 1 < E1.nParam H
  · obtain ⟨h1, h2⟩ := hyp.local_structure H hH hn
    exact nParam_le_nPrime_of_e22 hE22 hV hs hnab hyp.hyp322 hyp.qtke hyp.unique hH hn h1 h2
  · exact (not_lt.1 hn).trans (by exact_mod_cast E3.one_le_nPrime (autI hV ⊤))

theorem as_e_3_38_perH_of_e22 (hE22 : E2.E22StatementC) : ASInputs.AS_E_3_38_perH :=
  fun _ _ _ _ _ _ _ hV _ hs hnab h322 hK hM hH hn heq hC =>
    nParam_le_nPrime_of_e22 hE22 hV hs hnab h322 hK hM hH hn heq hC

theorem as_e_3_39_of_e22 (hE22 : E2.E22StatementC) {T V M H : Subgroup G}
    (hV : IsElemAbelian 2 V) (hV1 : V ≠ ⊥) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hyp : E3.HypE336 T V M)
    (hCM : Subgroup.centralizer (V : Set G) ≤ M)
    (hnr : (E3.nPrime (autI hV ⊤) : ℕ∞) < E3.rParam V) (hH : IsHStar T M H) :
    (E3.wParam T V ≤ E1.nParam H ∧ E1.nParam H ≤ (E3.nPrime (autI hV ⊤) : ℕ∞)) ∧
      (E3.aParam (autI hV ⊤) < E3.sParam hV →
        0 < E3.sParam hV - E3.aParam (autI hV ⊤) ∧
          ((E3.sParam hV - E3.aParam (autI hV ⊤) : ℕ) : ℕ∞) ≤ E3.wParam T V) :=
  e3_39_of_le hV hV1 hyp hCM hnr hH (nParam_le_nPrime_of_e22_hyp hE22 hV hs hnab hyp hH)

end CFSG.Quasithin.Vol2.Ch11.SecE3
