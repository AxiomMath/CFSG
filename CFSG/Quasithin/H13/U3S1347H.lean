module

import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.H13.A5S1327d
public import CFSG.Quasithin.H13.U3S1347C

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem eq_bot_of_coprime_three {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (h3 : 3 ∣ Nat.card Q) (M : Subgroup Q) [hM : M.Normal] (hc : Nat.Coprime 3 (Nat.card M)) :
    M = ⊥ := by
  rcases hM.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    rw [h, card_top] at hc
    have := Nat.Coprime.eq_one_of_dvd hc h3
    omega

theorem le_pCore_of_coprime_three {K : Type*} [Group K] [Finite K]
    (hs : IsSimpleGroup (K ⧸ CFSG.pCore 2 K)) (h3 : 3 ∣ Nat.card (K ⧸ CFSG.pCore 2 K))
    (M : Subgroup K) [hM : M.Normal] (hc : Nat.Coprime 3 (Nat.card M)) :
    M ≤ CFSG.pCore 2 K := by
  have hn : (M.map (QuotientGroup.mk' (CFSG.pCore 2 K))).Normal :=
    hM.map _ (QuotientGroup.mk'_surjective _)
  have hc' : Nat.Coprime 3 (Nat.card ↥(M.map (QuotientGroup.mk' (CFSG.pCore 2 K)))) :=
    Nat.Coprime.coprime_dvd_right (M.card_map_dvd _) hc
  have hb := eq_bot_of_coprime_three h3 _ hc'
  intro x hx
  have hx' : QuotientGroup.mk' (CFSG.pCore 2 K) x ∈ M.map (QuotientGroup.mk' _) :=
    mem_map_of_mem _ hx
  rw [hb, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
  exact hx'

theorem s1347_not_hat (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G} (h : Hyp1347 T H₁ H₂)
    (hH₀ : InH T (H₁ ⊔ H₂)) {K₀ : Subgroup G} (hK₀H : K₀ ≤ H₁ ⊔ H₂)
    (hcent : K₀ ⊓ centralizer (reducedAggregate (H₁ ⊔ H₂) : Set G) = A6.o2Z K₀) :
    ¬ A6.IsHatA6 K₀ := by
  rintro ⟨-, hZ3, -⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hred := s1347_reduced S hH₀
  have hVR := A7.le_reducedAggregate_of_isTwoReducedIn hred
  obtain ⟨⟨cb, hcb⟩, hcb1⟩ := ne_bot_iff_exists_ne_one.1
    ((one_lt_card_iff_ne_bot (center (↥K₀ ⧸ CFSG.pCore 2 ↥K₀))).1 (by omega))
  have hcb1' : cb ≠ 1 := fun e => hcb1 (Subtype.ext e)
  have hcb3 : cb ^ 3 = 1 := by
    have h1 := pow_card_eq_one' (G := ↥(center (↥K₀ ⧸ CFSG.pCore 2 ↥K₀))) (x := ⟨cb, hcb⟩)
    rw [hZ3] at h1
    simpa using congrArg Subtype.val h1
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective cb
  obtain ⟨a, m, hm, ham⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  have hyb : ((c ^ 2 ^ a : ↥K₀) : ↥K₀ ⧸ CFSG.pCore 2 ↥K₀) ≠ 1 := by
    rw [QuotientGroup.mk_pow]
    exact fun e => hcb1' (eq_one_of_two_pow_of_cube e hcb3)
  have hy3 : (c ^ 2 ^ a) ^ 3 = 1 := by
    have hmem : (c ^ 2 ^ a) ^ 3 ∈ CFSG.pCore 2 ↥K₀ := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_pow, ← pow_mul,
        mul_comm, pow_mul, hcb3, one_pow]
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥K₀) 2) ⟨_, hmem⟩
    have h2 : ((c ^ 2 ^ a) ^ 3) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hmm : ((c ^ 2 ^ a) ^ 3) ^ m = 1 := by
      rw [← pow_mul, ← pow_mul, show 2 ^ a * (3 * m) = 2 ^ a * m * 3 by ring, pow_mul, ← ham,
        pow_orderOf_eq_one, one_pow]
    exact A5.eq_one_of_pow_coprime h2 hmm (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm))
  have hyZ : ((c ^ 2 ^ a : ↥K₀) : G) ∈ A6.o2Z K₀ := by
    refine ⟨c ^ 2 ^ a, ?_, rfl⟩
    show ((c ^ 2 ^ a : ↥K₀) : ↥K₀ ⧸ CFSG.pCore 2 ↥K₀) ∈ center _
    rw [QuotientGroup.mk_pow]
    exact pow_mem hcb _
  rw [← hcent] at hyZ
  have hyC : ((c ^ 2 ^ a : ↥K₀) : G) ∈ centralizer (v0Of T H₁ H₂ : Set G) :=
    centralizer_le (SetLike.coe_subset_coe.2 hVR) hyZ.2
  have h1 := s1347_eq_one_of_threePow S h hH₀ ⟨hK₀H hyZ.1, hyC⟩ (k := 1)
    (by rw [pow_one]; simpa using congrArg Subtype.val hy3)
  apply hyb
  rw [show (c ^ 2 ^ a : ↥K₀) = 1 from Subtype.ext h1, QuotientGroup.mk_one]

omit [Finite G] in
theorem simple_of_cases {K : Subgroup G}
    (h : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) ∨
      LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 ∨
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 6))) :
    IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) ∧
      (Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 60 ∨ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 168 ∨
        Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 360) := by
  rcases h with he | h | he
  · obtain ⟨e⟩ := he
    have : IsSimpleGroup (alternatingGroup (Fin 5)) :=
      alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 5))
    refine ⟨e.isSimpleGroup, Or.inl ?_⟩
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  · obtain ⟨e⟩ := nonempty_equiv_SL32_of_lieModel h
    have := HSType.isSimpleGroup_SL_three_two
    refine ⟨e.isSimpleGroup, Or.inr (Or.inl ?_)⟩
    rw [Nat.card_congr e.toEquiv, HSType.card_SL_three_two]
  · obtain ⟨e⟩ := he
    have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 6))
    refine ⟨e.isSimpleGroup, Or.inr (Or.inr ?_)⟩
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide

omit [Finite G] in
theorem pCoreOf_subgroupOf_eq_pCore (K : Subgroup G) :
    (pCoreOf 2 K).subgroupOf K = CFSG.pCore 2 ↥K := CFSG.openPCoreOf_subgroupOf 2 K

theorem inf_le_pCoreOf_of_coprime_three {K N : Subgroup G}
    (hKN : K ≤ normalizer (N : Set G)) (hN : Nat.Coprime 3 (Nat.card N))
    (hs : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K)) (h3 : 3 ∣ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K)) :
    K ⊓ N ≤ pCoreOf 2 K := by
  have hn : ((K ⊓ N).subgroupOf K).Normal :=
    (normal_subgroupOf_iff_le_normalizer inf_le_left).2 fun k hk =>
      mem_normalizer_inf_of (le_normalizer hk) (hKN hk)
  have hc : Nat.Coprime 3 (Nat.card ↥((K ⊓ N).subgroupOf K)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv]
    exact Nat.Coprime.coprime_dvd_right (card_dvd_of_le inf_le_right) hN
  have hle := le_pCore_of_coprime_three hs h3 _ hc
  intro x hx
  have hx' : (⟨x, hx.1⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := hle (mem_subgroupOf.2 hx)
  rw [← pCoreOf_subgroupOf_eq_pCore, mem_subgroupOf] at hx'
  exact hx'

end CFSG.Quasithin.H13.U3
