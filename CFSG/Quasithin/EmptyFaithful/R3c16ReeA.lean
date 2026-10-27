module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6ResidualRee
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6ReeRankOne

public section

namespace CFSG.Quasithin.R3c16

open CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Setup.X6
  CFSG.LieType.Ree.LargeReeInvolution
open scoped commutatorElement

section Group

variable {G : Type*} [Group G]

theorem pow_mem_sup_of_pow_eq_one {W H : Subgroup G} (hH : H ≤ Subgroup.normalizer (W : Set G))
    {m : ℕ} (hm : ∀ h ∈ H, h ^ m = 1) {x : G} (hx : x ∈ W ⊔ H) : x ^ m ∈ W := by
  have hx' : x ∈ ((W ⊔ H : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left W H hH] at hx'
  obtain ⟨w, hw, h, hh, rfl⟩ := hx'
  obtain ⟨u', hu', e⟩ := exists_mul_pow_eq_mul_pow hw (hH hh) m
  rw [e, hm h hh, mul_one]
  exact hu'

theorem mem_of_pow_mem_of_threePow {W : Subgroup G} {x : G} {m k : ℕ} (hk : x ^ (3 ^ k) = 1)
    (hm : ¬ 3 ∣ m) (hxm : x ^ m ∈ W) : x ∈ W := by
  have hcop : Nat.Coprime m (orderOf x) := by
    have h3 : Nat.Coprime m (3 ^ k) :=
      Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hm).symm
    exact h3.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hk)
  obtain ⟨n, hn⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hn]
  exact pow_mem hxm n

theorem eq_one_of_isPGroup_two_of_threePow {W : Subgroup G} (hW : IsPGroup 2 ↥W) {x : G}
    (hxW : x ∈ W) {k : ℕ} (hk : x ^ (3 ^ k) = 1) : x = 1 := by
  obtain ⟨i, hi⟩ := hW ⟨x, hxW⟩
  have h2 : x ^ (2 ^ i) = 1 := congrArg Subtype.val hi
  have hcop : Nat.Coprime (2 ^ i) (3 ^ k) := Nat.Coprime.pow _ _ (by norm_num)
  have : orderOf x = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one hk)
  exact orderOf_eq_one_iff.1 this

theorem isPerfect_of_isSimpleGroup_of_nonabelian {R : Type*} [Group R] [IsSimpleGroup R]
    (h : ∃ x y : R, x * y ≠ y * x) : Group.IsPerfect R := by
  refine ⟨?_⟩
  rcases (Subgroup.commutator_normal (⊤ : Subgroup R) ⊤).eq_bot_or_eq_top with hb | ht
  · exfalso
    obtain ⟨x, y, hxy⟩ := h
    have hmem : ⁅x, y⁆ ∈ commutator R :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    have hb' : commutator R = ⊥ := hb
    rw [hb', Subgroup.mem_bot] at hmem
    exact hxy (commutatorElement_eq_one_iff_mul_comm.1 hmem)
  · exact ht

end Group

theorem not_three_dvd_two_pow_sub_one (a : ℕ) : ¬ 3 ∣ 2 ^ (2 * a + 1) - 1 := by
  have h4 : 4 ^ a % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h2 : 2 ^ (2 * a + 1) = 2 * 4 ^ a := by
    rw [pow_succ, pow_mul]
    norm_num
    ring
  have hpos : 0 < 4 ^ a := by positivity
  rw [h2]
  omega

section Ree

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem reeFixedTorus_pow_card_sub_one
    {h : ModGL F4.tag K} (hh : h ∈ F4.reeFixedTorus K a) :
    h ^ (Nat.card K - 1) = 1 :=
  pow_card_sub_one_eq_one_of_mem_diagonalGroup (torusGroup_le_diagonalGroup (Subgroup.mem_inf.1 hh).1)

theorem ree_threeElement_mem_sup_block
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {M : Subgroup (ModGL F4.tag K)}
    (hMΓ : M ≤ F4.reeGamma K a) (hUM : F4.reeFixedPosUnipotent K a ≤ M)
    (hMne : M ≠ F4.reeGamma K a) {y : ModGL F4.tag K} (hy : y ∈ M) {k : ℕ} (hk : y ^ (3 ^ k) = 1)
    (hy1 : y ≠ 1) :
    ∃ j : Fin F4.fixedOrbitCount,
      y ∈ F4.reeFixedPosUnipotent K a ⊔ F4.reeLocalBlock K a j ∧
        F4.reeLocalBlock K a j ≤ M ∧ Group.IsPerfect ↥(F4.reeLocalBlock K a j) := by
  classical
  have h3 : ¬ 3 ∣ Nat.card K - 1 := by
    rw [hK]
    exact not_three_dvd_two_pow_sub_one a
  have hU2 : IsPGroup 2 ↥(F4.reeFixedPosUnipotent K a) :=
    (isPGroup_posUnipotent F4.prime F4.tag).to_le
      (inf_le_left : F4.reeFixedPosUnipotent K a ≤ _)
  obtain ⟨hle, hiff, -⟩ := large_Ree_positive_root_overgroup_parabolic_containment hK hMΓ hUM
  set J : Set (Fin F4.fixedOrbitCount) :=
    {j | canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) ∈ M} with hJ
  by_cases hJe : J = ∅
  · exfalso
    rw [hJe, reeParabolic_empty] at hle
    have hyU : y ^ (Nat.card K - 1) ∈ F4.reeFixedPosUnipotent K a :=
      pow_card_sub_one_mem_reeFixedPosUnipotent (hle hy)
    exact hy1 (eq_one_of_isPGroup_two_of_threePow hU2 (mem_of_pow_mem_of_threePow hk h3 hyU) hk)
  · obtain ⟨j₀, hj₀⟩ := Set.nonempty_iff_ne_empty.2 hJe
    have hJsub : J ⊆ {j₀} := by
      intro j hj
      by_contra hne
      apply hMne
      apply hiff.1
      refine Set.eq_univ_of_forall fun i => ?_
      have h2 : ∀ x y z : Fin F4.fixedOrbitCount, x ≠ y → z = x ∨ z = y := by decide
      rcases h2 j j₀ i (fun h => hne (by rw [h]; exact Set.mem_singleton _)) with rfl | rfl
      · exact hj
      · exact hj₀
    have hMP : M ≤ F4.reeParabolic K a {j₀} :=
      hle.trans (sup_le_sup_left (Subgroup.closure_mono (Set.image_mono hJsub)) _)
    have hyP : y ∈ F4.reeFixedTorus K a ⊔ reePosWeylGroup K a j₀ := by
      rw [← reeParabolic_singleton_eq_sup]
      exact hMP hy
    have hyN : y ^ (Nat.card K - 1) ∈ reePosWeylGroup K a j₀ :=
      pow_mem_sup_of_pow_eq_one (W := reePosWeylGroup K a j₀) (H := F4.reeFixedTorus K a)
        (reeFixedTorus_le_normalizer_reePosWeylGroup j₀) (fun h hh => reeFixedTorus_pow_card_sub_one hh)
        (by rw [sup_comm]; exact hyP)
    have hyN' : y ∈ reePosWeylGroup K a j₀ := mem_of_pow_mem_of_threePow hk h3 hyN
    have hn : canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j₀) ∈
        F4.reeLocalBlock K a j₀ := canonicalRep_fixedOrbitElement_mem_reeLocalBlock j₀
    have hNle : reePosWeylGroup K a j₀ ≤ F4.reeFixedPosUnipotent K a ⊔ F4.reeLocalBlock K a j₀ :=
      sup_le_sup_left ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 hn)) _
    have hNM : reePosWeylGroup K a j₀ ≤ M :=
      sup_le hUM ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 hj₀))
    refine ⟨j₀, hNle hyN', (reeLocalBlock_le_reePosWeylGroup j₀).trans hNM, ?_⟩
    obtain ⟨⟨h0, -, -⟩, ⟨h1, -, -⟩⟩ := large_Ree_opposite_simple_blocks_generate_rank_one_model
      (K := K) (a := a) ha hK
    have hcases : ∀ j : Fin F4.fixedOrbitCount, j = ⟨0, by decide⟩ ∨ j = ⟨1, by decide⟩ := by
      decide
    rcases hcases j₀ with rfl | rfl
    · rw [h0]
      obtain ⟨hs, hnab⟩ := isSimpleGroup_rankOneGroupOne ha hK
      exact @isPerfect_of_isSimpleGroup_of_nonabelian _ _ hs hnab
    · rw [h1]
      obtain ⟨hs, hnab⟩ := isSimpleGroup_rankOneGroupTwo ha hK
      exact @isPerfect_of_isSimpleGroup_of_nonabelian _ _ hs hnab

end Ree

end CFSG.Quasithin.R3c16
