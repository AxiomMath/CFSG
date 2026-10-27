module

public import CFSG.Quasithin.Vol2.Ch11SecE3PerH

public section

namespace CFSG.Quasithin.RonanE338

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.H13
open CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS
open CFSG.Quasithin.Vol2.Ch11.SecE3
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem hStar_ne_top {T M H : Subgroup G} (hM : IsMaxTwoLocalSubgroup M) (hH : IsHStar T M H) :
    H ≠ ⊤ := by
  rintro rfl
  have hne : pCoreOf 2 (⊤ : Subgroup G) ≠ ⊥ := hH.1.2
  have hle : (⊤ : Subgroup G) ≤ Subgroup.normalizer (pCoreOf 2 (⊤ : Subgroup G) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 ⊤
  have hloc : IsTwoLocal (⊤ : Subgroup G) :=
    ⟨pCoreOf 2 ⊤, hne, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 ⊤, (top_le_iff.mp hle).symm⟩
  exact hH.2.1 ((hM.2 ⊤ hloc le_top) ▸ le_top)

theorem exists_hall_cartan (hE22 : E2.E22StatementC) {T M H : Subgroup G}
    (hsq : SQTKGroup ↥H) (hT : quasithinIsSylowTwo T) (hTM : T ≤ M) (hH : IsHStar T M H)
    (hn : 1 < E1.nParam H) :
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
  obtain ⟨⟨K, hKc, hHK, -, hcases⟩, -⟩ := hE22.exists_cases hmin hsq hns
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
    (hV : IsElemAbelian 2 V) (hsq : SQTKGroup ↥H)
    (h322 : E3.HypE322 T V)
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
    exists_hall_cartan hE22 hsq hT hTM hH hn
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

theorem nParam_le_nPrime (hE22 : E2.E22StatementC) {T V M H : Subgroup G}
    (hV : IsElemAbelian 2 V) (hyp : E3.HypE336 T V M) (hH : IsHStar T M H) :
    E1.nParam H ≤ (E3.nPrime (autI hV ⊤) : ℕ∞) := by
  by_cases hn : 1 < E1.nParam H
  · have hsq : SQTKGroup ↥H :=
      ⟨stronglyQuasithin_of_pCoreOf_ne_bot hyp.qtke hH.1.2,
        kGroup_of_ne_top hyp.qtke (hStar_ne_top hyp.unique.1.1 hH)⟩
    obtain ⟨h1, h2⟩ := hyp.local_structure H hH hn
    exact nParam_le_nPrime_of_e22 hE22 hV hsq hyp.hyp322 hyp.unique hH hn h1 h2
  · exact (not_lt.1 hn).trans (by exact_mod_cast E3.one_le_nPrime (autI hV ⊤))

end CFSG.Quasithin.RonanE338

end
