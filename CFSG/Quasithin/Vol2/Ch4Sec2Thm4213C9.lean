module

public import CFSG.Quasithin.Vol2.Ch4Sec2Lem4212C
public import CFSG.Quasithin.EmptyFaithful.SBc11List
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4

variable {G : Type} [Group G] [Finite G]

namespace C489

section Orders

variable {X : Type} [Group X]

theorem card_of_isE2 {k : ℕ} (h : IsE2 k X) : Nat.card X = 2 ^ k := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  simp [Nat.card_eq_fintype_card]

theorem card_of_isZ4Cubed (h : IsZ4Cubed X) : Nat.card X = 64 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  simp [Nat.card_eq_fintype_card]

theorem card_of_isSpecial2Group {a b : ℕ} (h : IsSpecial2Group a b X) :
    Nat.card X = 2 ^ (a + b) := by
  obtain ⟨h1, -, h2⟩ := h
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)
  rw [h3, h1, card_of_isE2 h2, pow_add, mul_comm]

theorem card_of_isAlt {n : ℕ} (h : IsAlt n X) :
    Nat.card X = Nat.card (alternatingGroup (Fin n)) := by
  obtain ⟨e⟩ := h
  exact Nat.card_congr e.toEquiv

theorem card_of_isHat_alt6 (h : IsHat X (alternatingGroup (Fin 6))) : Nat.card X = 1080 := by
  obtain ⟨-, h3, ⟨e⟩⟩ := h
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)
  rw [h1, h3, Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  decide

theorem card_of_isPSL_two_two {n : ℕ} (h : IsPSL 2 2 n X) :
    Nat.card X = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  have hf : 1 ≤ n := h.1.2.1
  have h1 := (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl
  have hodd : Odd (2 ^ n - 1) := by
    simpa using CFSG.Timmesfeld.ClassicalOrders.odd_two_pow_pow_sub_one hf (n := 1) le_rfl
  have hgcd : Nat.gcd 2 (2 ^ n - 1) = 1 := Nat.coprime_two_left.mpr hodd
  rw [h1]
  unfold CFSG.Open.ordA
  norm_num [Finset.Icc_self, hgcd]

theorem card_of_isPSL_two {n : ℕ} (h : IsPSL n 2 1 X) :
    Nat.card X = CFSG.Open.ordA (n - 1) (2 ^ 1) :=
  (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl

theorem card_of_isExt {PN PQ : ∀ (V : Type) [Group V], Prop} (h : IsExt X PN PQ) :
    ∃ (N : Subgroup X) (_ : N.Normal), PN ↥N ∧ PQ (X ⧸ N) ∧
      Nat.card X = Nat.card (X ⧸ N) * Nat.card N := by
  obtain ⟨N, hN, hPN, hPQ⟩ := h
  exact ⟨N, hN, hPN, hPQ, Subgroup.card_eq_card_quotient_mul_card_subgroup N⟩

end Orders

theorem card_statedSL_three_two :
    Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) = 168 :=
  CFSG.Open.StatedAPI.card_statedSL_three_zmod_two

theorem card_of_isLnBlock_three {L : Subgroup G} (h : IsLnBlock L 3) :
    (∃ a : ℕ, Nat.card L = 2 ^ a * 168) ∧ Nat.card (ModO2 L) = 168 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, α, hα, hker, -⟩ := h
  have hq : Nat.card (ModO2 L) = 168 := by
    have e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα)
    rw [Nat.card_congr e.toEquiv, card_statedSL_three_two]
  refine ⟨?_, hq⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
  refine ⟨a, ?_⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L)
  rw [h1, ha, show Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 168 from hq, mul_comm]

theorem card_of_isDoubleCover_alt8 {K : Type} [Group K]
    (h : IsDoubleCover K ↥(alternatingGroup (Fin 8))) :
    Nat.card (K ⧸ Subgroup.center K) = 20160 ∧ Nat.card K = 40320 := by
  obtain ⟨-, h2, ⟨e⟩⟩ := h
  have h1 : Nat.card (K ⧸ Subgroup.center K) = 20160 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  refine ⟨h1, ?_⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K), h1, h2]

theorem not_charTwo_of_quasisimple {K : Subgroup G} (hK : K ≠ ⊥) (hKp : ⁅K, K⁆ = K)
    (hq : CFSG.IsQuasisimple ↥K) : ¬ CharTwo K := by
  intro hc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKO : K ≤ pCoreOf 2 K := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq
      (CFSG.LieType.BorelTits.pCore_normal 2 : (CFSG.Open.pCore 2 ↥K).Normal) with htop | hcen
    · intro k hk
      exact ⟨⟨k, hk⟩, htop ▸ Subgroup.mem_top _, rfl⟩
    · refine fun k hk => hc (Subgroup.mem_inf.mpr ⟨hk, ?_⟩)
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨x, hx, rfl⟩
      have h1 := Subgroup.mem_center_iff.mp (hcen hx) ⟨k, hk⟩
      exact (congrArg Subtype.val h1).symm
  exact hK (eq_bot_of_commutator_eq_self_of_isPGroup_two hKp ((pCoreOf_isPGroup 2 K).to_le hKO))

theorem card_alt6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem card_alt7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem twentyThree_dvd_card_M23 : 23 ∣ Nat.card ↥NativeSporadic.M23 := by
  have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  have ha : (List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 7] *
      List.formPerm [8, 9] * List.formPerm [12, 13] * List.formPerm [14, 15] *
      List.formPerm [18, 19] * List.formPerm [20, 21] : Equiv.Perm (Fin 23)) ∈
      NativeSporadic.M23 :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : (List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] *
      List.formPerm [3, 4, 7, 22] * List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] *
      List.formPerm [14, 16] : Equiv.Perm (Fin 23)) ∈ NativeSporadic.M23 :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hx : ((List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 7] *
      List.formPerm [8, 9] * List.formPerm [12, 13] * List.formPerm [14, 15] *
      List.formPerm [18, 19] * List.formPerm [20, 21] : Equiv.Perm (Fin 23)) *
      (List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] *
      List.formPerm [3, 4, 7, 22] * List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] *
      List.formPerm [14, 16] : Equiv.Perm (Fin 23))) ^ 23 = 1 := by decide +kernel
  have hx1 : ((List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 7] *
      List.formPerm [8, 9] * List.formPerm [12, 13] * List.formPerm [14, 15] *
      List.formPerm [18, 19] * List.formPerm [20, 21] : Equiv.Perm (Fin 23)) *
      (List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] *
      List.formPerm [3, 4, 7, 22] * List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] *
      List.formPerm [14, 16] : Equiv.Perm (Fin 23))) ≠ 1 := by decide +kernel
  have key : ∀ {σ : Equiv.Perm (Fin 23)}, σ ∈ NativeSporadic.M23 → σ ^ 23 = 1 → σ ≠ 1 →
      23 ∣ Nat.card ↥NativeSporadic.M23 := by
    intro σ hσ hpow hne
    have h : orderOf (⟨σ, hσ⟩ : ↥NativeSporadic.M23) = 23 :=
      orderOf_eq_prime (Subtype.ext (by rw [Subgroup.coe_pow]; exact hpow))
        fun h1 => hne (congrArg Subtype.val h1)
    have h2 := orderOf_dvd_natCard (⟨σ, hσ⟩ : ↥NativeSporadic.M23)
    rwa [h] at h2
  exact key (Subgroup.mul_mem _ ha hb) hx hx1

omit [Finite G] in
theorem case10_of_c31 {H R M L V K : Subgroup G}
    (hK2 : IsDoubleCover ↥K ↥(alternatingGroup (Fin 8))) (hLK : L ≤ K)
    (hL : Nat.card L ∣ 2688) (h168 : Nat.card (ModO2 L) = 168) (hL0 : L = conjClosure L M)
    (h : C31Case1 H R M L V K ∨ C31Case2 H R M L V K ∨ C31Case3 H R M L V K ∨
      C31Case4 H R M L V K ∨ C31Case5 H R M L V K ∨ C31Case6 H R M L V K ∨
      C31Case7 H R M L V K ∨ C31Case8 H R M L V K ∨ C31Case9 H R M L V K ∨
      C31Case10 H R M L V K) :
    C31Case10 H R M L V K := by
  obtain ⟨hKZ, hK⟩ := card_of_isDoubleCover_alt8 hK2
  have hL' : Nat.card ↥(conjClosure L M) ∣ 2688 := by
    rw [← hL0]
    exact hL
  have h168' : Nat.card (ModO2 (conjClosure L M)) = 168 := by
    rw [← hL0]
    exact h168
  have himg : Nat.card ↥(imageModCenter K (conjClosure L M)) ∣ 2688 := by
    rw [← hL0]
    unfold imageModCenter
    refine (Subgroup.card_map_dvd (H := L.subgroupOf K)
      (QuotientGroup.mk' (Subgroup.center ↥K))).trans ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLK).toEquiv]
    exact hL
  have h5 : ∀ {n : ℕ}, n ∣ 2688 → ¬ 5 ∣ n := fun hn h5 => by
    have := h5.trans hn
    norm_num at this
  have h256 : ∀ {n : ℕ}, n ∣ 2688 → ¬ 2 ^ 8 ∣ n := fun hn h8 => by
    have := h8.trans hn
    norm_num at this
  rcases h with h1 | h2 | h3 | h4 | h5' | h6 | h7 | h8 | h9 | h10
  ·
    exfalso
    obtain ⟨n, -, -, -, hpsl, -⟩ := h1
    have hc := h168'.symm.trans (card_of_isPSL_two_two hpsl)
    have hn : n ≤ 3 := by
      by_contra hn
      have h16 : 2 ^ 4 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
      have h16' : 2 ^ 4 ∣ 168 := h16.trans ⟨_, hc⟩
      norm_num at h16'
    interval_cases n <;> norm_num at hc
  ·
    exfalso
    obtain ⟨n, hn, hpsl, -⟩ := h2
    have hc := hK.symm.trans (card_of_isPSL_two hpsl)
    rcases hn with rfl | rfl <;> revert hc <;> decide
  ·
    exfalso
    obtain ⟨⟨e⟩, -⟩ := h3
    have hc := Nat.card_congr e.toEquiv
    rw [hKZ, show Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M22) = _ from
      CFSG.Sporadic.Mathieu.card_M22] at hc
    norm_num at hc
  ·
    exfalso
    obtain ⟨hM23, hext | hext | -⟩ := h4
    · obtain ⟨N, _, hN, hQ, hc⟩ := card_of_isExt hext
      rw [card_of_isE2 hN, card_of_isPSL_two_two hQ] at hc
      exact h5 hL' (by rw [hc]; norm_num)
    · obtain ⟨N, _, hN, hQ, hc⟩ := card_of_isExt hext
      rw [card_of_isE2 hN, card_of_isAlt hQ, card_alt7] at hc
      exact h5 hL' (by rw [hc]; norm_num)
    · obtain ⟨e⟩ := hM23
      have hc : Nat.card ↥K = Nat.card ↥NativeSporadic.M23 := Nat.card_congr e.toEquiv
      have h23 := twentyThree_dvd_card_M23
      rw [← hc, hK] at h23
      norm_num at h23
  ·
    exfalso
    obtain ⟨-, hext | hext | hext⟩ := h5'
    · obtain ⟨N, _, hN, hQ, hc⟩ := card_of_isExt hext
      rw [card_of_isE2 hN, card_of_isHat_alt6 hQ] at hc
      exact h5 hL' (by rw [hc]; norm_num)
    · obtain ⟨N, _, hN, hQ, hc⟩ := card_of_isExt hext
      rw [card_of_isE2 hN, card_of_isPSL_two hQ] at hc
      exact h5 hL' (by rw [hc]; decide)
    · obtain ⟨N, _, hN, hQ, hc⟩ := card_of_isExt hext
      rw [card_of_isE2 hN, card_of_isPSL_two hQ] at hc
      exact h256 hL' (by rw [hc]; decide)
  ·
    exfalso
    obtain ⟨-, hext | hext | hext⟩ := h6
    · obtain ⟨N, _, hN, -, hc⟩ := card_of_isExt hext
      rw [card_of_isE2 hN] at hc
      exact h256 hL' ⟨Nat.card (↥(conjClosure L M) ⧸ N) * 2 ^ 3, by rw [hc]; ring⟩
    · obtain ⟨N, _, hN, -, hc⟩ := card_of_isExt hext
      rw [card_of_isSpecial2Group hN] at hc
      exact h256 hL' ⟨Nat.card (↥(conjClosure L M) ⧸ N) * 2 ^ 7, by rw [hc]; ring⟩
    · obtain ⟨N, _, hN, -, hc⟩ := card_of_isExt hext
      rw [card_of_isE2 hN] at hc
      exact h256 hL' ⟨Nat.card (↥(conjClosure L M) ⧸ N) * 2 ^ 2, by rw [hc]; ring⟩
  ·
    exfalso
    obtain ⟨-, hext | hext⟩ := h7
    · obtain ⟨N, _, hN, hQ, hc⟩ := card_of_isExt hext
      rw [card_of_isZ4Cubed hN, card_of_isPSL_two hQ] at hc
      exact h256 himg (by rw [hc]; decide)
    · obtain ⟨N, _, hN, hQ, hc⟩ := card_of_isExt hext
      rw [card_of_isE2 hN, card_of_isAlt hQ, card_alt6] at hc
      exact h5 himg (by rw [hc]; norm_num)
  ·
    exfalso
    obtain ⟨-, hext⟩ := h8
    obtain ⟨N, _, hN, hQ, hc⟩ := card_of_isExt hext
    rw [card_of_isE2 hN, card_of_isHat_alt6 hQ] at hc
    exact h5 hL' (by rw [hc]; norm_num)
  ·
    exfalso
    obtain ⟨-, hext | hext⟩ := h9
    · obtain ⟨N, _, hN, -, hc⟩ := card_of_isExt hext
      rw [card_of_isSpecial2Group hN] at hc
      exact h256 himg ⟨Nat.card (↥(imageModCenter K (conjClosure L M)) ⧸ N) * 2 ^ 3,
        by rw [hc]; ring⟩
    · obtain ⟨N, _, hN, hQ, hc⟩ := card_of_isExt hext
      rw [card_of_isE2 hN, CFSG.Quasithin.SBc11.card_of_isPSU_three_three hQ] at hc
      exact h256 himg (by rw [hc]; norm_num)
  · exact h10

end C489

namespace Conf4212

variable {T M L I H K : Subgroup G} (c : Conf4212 G T M L I H K)
include c

theorem false_of_case9 (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK)
    (h9 : C48Case9 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆
      K) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set LH := perfectCore (L ⊓ H) with hLHdef
  set V := ⁅reducedAggregate (L ⊔ T), L⁆ with hVdef
  obtain ⟨hK2, hblk, -⟩ := h9
  have hKne : K ≠ ⊥ := ne_bot_of_mem_cComp c.K_mem
  have hKp : ⁅K, K⁆ = K := perfect_of_mem_cComp c.K_mem
  obtain ⟨⟨a, ha⟩, h168⟩ := C489.card_of_isLnBlock_three hblk
  obtain ⟨-, hK⟩ := C489.card_of_isDoubleCover_alt8 hK2
  have hLdvd : Nat.card LH ∣ 2688 := by
    have h1 : Nat.card LH ∣ Nat.card K := Subgroup.card_dvd_of_le c.LH_le
    rw [ha, hK, show 40320 = 240 * 168 by norm_num] at h1
    have h2 : 2 ^ a ∣ 240 := Nat.dvd_of_mul_dvd_mul_right (by norm_num) h1
    have h3 : a ≤ 4 := by
      by_contra h3
      have h32 : 2 ^ 5 ∣ 240 := (pow_dvd_pow 2 (by omega)).trans h2
      norm_num at h32
    rw [ha, show 2688 = 2 ^ 4 * 168 by norm_num]
    exact Nat.mul_dvd_mul_right (pow_dvd_pow 2 h3) _
  have hLH0 : conjClosure LH (H ⊓ M) = LH := conjClosure_eq_self c.LH_normal
  obtain ⟨hZ, hZ2⟩ : centerOf K = V ⊓ Subgroup.centralizer (LH : Set G) ∧
      IsPGroup 2 ↥(centerOf K) := by
    rcases c.described with ⟨-, h31⟩ | ⟨-, hchar, -⟩
    · obtain ⟨hL0, -, -, -, hZ2, hcases⟩ := h31
      obtain ⟨-, hZ, -⟩ := C489.case10_of_c31 hK2 c.LH_le hLdvd h168 hL0 hcases
      rw [hLH0] at hZ
      exact ⟨hZ, hZ2⟩
    · exact absurd hchar (C489.not_charTwo_of_quasisimple hKne hKp hK2.1)
  have hTN : T ≤ Subgroup.normalizer (L : Set G) := c.hyp421.T_le.trans c.normal
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := _root_.sup_le Subgroup.le_normalizer hTN
  have hRN : L ⊔ T ≤ Subgroup.normalizer (reducedAggregate (L ⊔ T) : Set G) := by
    rw [← c.omega_eq]
    exact (le_normalizer_pCoreOf 2 _).trans (normalizer_le_normalizer_omegaOneCenterOf _)
  have hVΩ : V ≤ omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) := by
    rw [c.omega_eq]
    exact commutator_le_left_of_le_normalizer (le_sup_left.trans hRN)
  have hO2L : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left)
      (hLTN.trans (normalizer_le_normalizer_pCoreOf 2 L)) (pCoreOf_isPGroup 2 L)
  have hVC : V ≤ Subgroup.centralizer (pCoreOf 2 L : Set G) :=
    le_centralizer_of_le_omegaOneCenterOf hVΩ hO2L
  have hZL : centerOf K = V ⊓ Subgroup.centralizer (L : Set G) := by
    rw [hZ]
    apply le_antisymm
    · refine le_inf inf_le_left ?_
      rw [← Subgroup.le_centralizer_iff]
      refine c.L_le.trans (_root_.sup_le ?_ ?_)
      · rw [Subgroup.le_centralizer_iff]
        exact inf_le_right
      · rw [Subgroup.le_centralizer_iff]
        exact inf_le_left.trans hVC
    · exact inf_le_inf_left _ (Subgroup.centralizer_le ((perfectCore_le _).trans inf_le_left))
  have hZne : centerOf K ≠ ⊥ := by
    intro hbot
    obtain ⟨z, hz1⟩ : ∃ z : ↥(Subgroup.center ↥K), z ≠ 1 := by
      by_contra hne
      push Not at hne
      have h1 : Nat.card (Subgroup.center ↥K) = 1 :=
        Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (hne a).trans (hne b).symm⟩, ⟨1⟩⟩
      have h2 := hK2.2.1
      omega
    have hzc : ((z : ↥K) : G) ∈ centerOf K := by
      refine ⟨(z : ↥K).2, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
      have h1 := Subgroup.mem_center_iff.mp z.2 ⟨k, hk⟩
      exact congrArg Subtype.val h1
    rw [hbot, Subgroup.mem_bot] at hzc
    exact hz1 (Subtype.ext (Subtype.ext hzc))
  have hLTZ : L ⊔ T ≤ Subgroup.normalizer (centerOf K : Set G) := by
    rw [hZL]
    intro g hg
    exact mem_normalizer_inf (mem_normalizer_commutator (hRN hg) (hLTN hg))
      (mem_normalizer_centralizer_of_mem_normalizer (hLTN hg))
  have hNM : Subgroup.normalizer (centerOf K : Set G) ≤ M := by
    refine isUniqueM_le_of_inH (c.hyp421.isUniqueM_sup h37 h38 h39).1 ⟨hLTZ, fun hbot => hZne ?_⟩
    have h1 : centerOf K ≤ pCoreOf 2 (Subgroup.normalizer (centerOf K : Set G)) :=
      le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hZ2
    rw [hbot] at h1
    exact le_bot_iff.mp h1
  have hKC : K ≤ Subgroup.centralizer (centerOf K : Set G) :=
    Subgroup.le_centralizer_iff.mpr inf_le_right
  exact c.K_not_le (hKC.trans ((Subgroup.centralizer_le_normalizer _).trans hNM))

end Conf4212

end CFSG.Quasithin.H13.Ch4
