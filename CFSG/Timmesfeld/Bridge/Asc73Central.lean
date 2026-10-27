module

public import CFSG.Timmesfeld.Bridge.StrongEmbedding
public import CFSG.StronglyEmbedded.BenderNormalSeries
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.PFchapter1section1
open scoped MatrixGroups

@[expose] def SchurNarrowInput : Prop :=
  ∀ (E : Type) [Group E] [Finite E] (x : E) (_ : (Subgroup.zpowers x).Normal),
    x ∈ Subgroup.center E → orderOf x = 2 → x ∈ commutator E →
    ∀ (M N : Subgroup (E ⧸ Subgroup.zpowers x)) (_ : M.Normal) (_ : N.Normal)
      (_ : (M.subgroupOf N).Normal),
      M ≤ N → Odd (Nat.card M) → Odd N.index →
      ((∃ f : ℕ, 2 ≤ f ∧ Nonempty ((N ⧸ M.subgroupOf N) ≃* PSU3 2 f)) ∨
        (∃ a : ℕ, 1 ≤ a ∧ Nonempty ((N ⧸ M.subgroupOf N) ≃* Sz a))) →
      ∃ z : E, orderOf z = 2 ∧ z ∉ Subgroup.zpowers x ∧ IsConj z (z * x)

variable {G : Type} [Group G]

theorem commutator_eq_top_of_mul_mem {D : Set G} (hgen : Subgroup.closure D = ⊤)
    (hclass : ∀ a ∈ D, ∀ b ∈ D, IsConj a b) {u v : G} (hu : u ∈ D) (hv : v ∈ D)
    (huv : u * v ∈ D) : commutator G = ⊤ := by
  have himg : ∀ a ∈ D, (Abelianization.of a : Abelianization G) = Abelianization.of u := by
    intro a ha
    obtain ⟨c, rfl⟩ := isConj_iff.1 (hclass u hu a ha)
    rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  have hv1 : (Abelianization.of v : Abelianization G) = 1 := by
    have h := himg _ huv
    rw [map_mul] at h
    exact mul_eq_left.1 h
  rw [eq_top_iff, ← hgen, Subgroup.closure_le, ← Abelianization.ker_of]
  intro a ha
  rw [SetLike.mem_coe, MonoidHom.mem_ker, himg a ha, ← himg v hv, hv1]

theorem eq_one_of_pow_two_pow_of_odd {K : Type*} [Group K] [Finite K] (hK : Odd (Nat.card K))
    {k : K} {n : ℕ} (hk : k ^ 2 ^ n = 1) : k = 1 := by
  have h1 : orderOf k ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf k ∣ Nat.card K := orderOf_dvd_natCard k
  have hcop : Nat.Coprime (Nat.card K) (2 ^ n) :=
    Nat.Coprime.pow_right n (Nat.coprime_two_right.2 hK)
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h2 h1)

theorem zpowers_normal_of_mem_center {x : G} (hx : x ∈ Subgroup.center G) :
    (Subgroup.zpowers x).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hnc : n ∈ Subgroup.center G := (Subgroup.zpowers_le.2 hx) hn
  rw [Subgroup.mem_center_iff.1 hnc g, mul_inv_cancel_right]
  exact hn

theorem mem_sylow_of_mem_center [Finite G] {x : G} (hx : x ∈ Subgroup.center G)
    (hx2 : orderOf x = 2) (S : Sylow 2 G) : x ∈ (S : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : (Subgroup.zpowers x).Normal := zpowers_normal_of_mem_center hx
  have h2 : IsPGroup 2 (Subgroup.zpowers x) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one, hx2]
  exact h2.le_sylow_of_normal S (Subgroup.mem_zpowers x)

theorem not_mem_commutator_of_sylow_commute [Finite G] {x : G} (hx : x ∈ Subgroup.center G)
    (hx2 : orderOf x = 2) (S : Sylow 2 G)
    (hS : ∀ a ∈ (S : Subgroup G), ∀ b ∈ (S : Subgroup G), Commute a b) :
    x ∉ commutator G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxS := mem_sylow_of_mem_center hx hx2 S
  set ψ : (S : Subgroup G) →* Abelianization (S : Subgroup G) := Abelianization.of
  have key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * x ^ k * g₀ ∈ (S : Subgroup G) →
      g₀⁻¹ * x ^ k * g₀ = x ^ k := by
    intro k g₀ _
    have hxk : x ^ k ∈ Subgroup.center G := Subgroup.pow_mem _ hx k
    rw [mul_assoc, ← Subgroup.mem_center_iff.1 hxk g₀, ← mul_assoc, inv_mul_cancel, one_mul]
  have htr := MonoidHom.transfer_eq_pow ψ x key
  have hodd : Odd (S : Subgroup G).index := by
    have := S.not_dvd_index
    rcases Nat.even_or_odd (S : Subgroup G).index with h | h
    · exact absurd (even_iff_two_dvd.1 h) this
    · exact h
  have hpow : x ^ (S : Subgroup G).index = x := by
    obtain ⟨m, hm⟩ := hodd
    rw [hm, pow_succ, pow_mul, ← hx2, pow_orderOf_eq_one, one_pow, one_mul]
  have hψ : ψ ⟨x, hxS⟩ ≠ 1 := by
    intro h1
    have hmem : (⟨x, hxS⟩ : (S : Subgroup G)) ∈ commutator (S : Subgroup G) := by
      rw [← Abelianization.ker_of]
      exact h1
    have hbot : commutator (S : Subgroup G) = ⊥ := by
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a _
      rw [Subgroup.mem_centralizer_iff]
      intro b _
      exact Subtype.ext (hS b.1 b.2 a.1 a.2).eq
    rw [hbot, Subgroup.mem_bot] at hmem
    have := congrArg Subtype.val hmem
    simp only [OneMemClass.coe_one] at this
    rw [this, orderOf_one] at hx2
    exact absurd hx2 (by norm_num)
  intro hmem
  have h1 : ψ.transfer x = 1 := (Abelianization.commutator_subset_ker _) hmem
  rw [htr] at h1
  apply hψ
  rw [← h1]
  congr 1
  exact Subtype.ext hpow.symm

theorem sq_eq_one_of_psl2 {f : ℕ} (hf : 2 ≤ f) {y : PSL(2, GaloisField 2 f)} {n : ℕ}
    (hy : y ^ 2 ^ n = 1) : y ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q⟩ : Nonempty (Sylow 2 PSL(2, GaloisField 2 f)) := inferInstance
  obtain ⟨-, -, hZ, hZcard, hQcard⟩ := bender_psl2_borel_full f hf Q
  have hZtop : Subgroup.center (Q : Subgroup PSL(2, GaloisField 2 f)) = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [hZcard, hQcard, pow_one])
  have hQsq : ∀ q ∈ (Q : Subgroup PSL(2, GaloisField 2 f)), q ^ 2 = 1 := by
    intro q hq
    have := hZ ⟨q, hq⟩ (by rw [hZtop]; trivial)
    simpa using congrArg Subtype.val this
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow Q hy
  have h1 := hQsq _ hg
  rw [conj_pow] at h1
  have h2 : y ^ 2 = g⁻¹ * (g * y ^ 2 * g⁻¹) * g := by group
  rw [h2, h1, mul_one, inv_mul_cancel]

theorem sq_eq_one_of_bender_psl2 {X : Type} [Group X] [Finite X] {M N : Subgroup X} [M.Normal]
    [N.Normal] [(M.subgroupOf N).Normal] (hM : Odd (Nat.card M))
    (hN : Odd N.index) {f : ℕ} (hf : 2 ≤ f) (e : (N ⧸ M.subgroupOf N) ≃* PSL(2, GaloisField 2 f))
    {y : X} {n : ℕ} (hy : y ^ 2 ^ n = 1) : y ^ 2 = 1 := by
  have hyN : y ∈ N := by
    have hodd : Odd (Nat.card (X ⧸ N)) := by rwa [Subgroup.index] at hN
    have := eq_one_of_pow_two_pow_of_odd hodd (k := QuotientGroup.mk' N y) (n := n)
      (by rw [← map_pow, hy, map_one])
    exact (QuotientGroup.eq_one_iff y).1 this
  set yb : N ⧸ M.subgroupOf N := QuotientGroup.mk' _ ⟨y, hyN⟩
  have hyb : yb ^ 2 ^ n = 1 := by
    rw [← map_pow]
    have : (⟨y, hyN⟩ : N) ^ 2 ^ n = 1 := Subtype.ext (by simpa using hy)
    rw [this, map_one]
  have he : (e yb) ^ 2 = 1 := sq_eq_one_of_psl2 hf (by rw [← map_pow, hyb, map_one])
  have hyb2 : yb ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, he, map_one]
  have hmem : (⟨y, hyN⟩ : N) ^ 2 ∈ M.subgroupOf N := by
    rw [← QuotientGroup.eq_one_iff]
    have hcoe : (((⟨y, hyN⟩ : N) ^ 2 : N) : N ⧸ M.subgroupOf N) = yb ^ 2 := by
      rw [QuotientGroup.mk_pow]
      rfl
    rw [hcoe, hyb2]
  have hyM : y ^ 2 ∈ M := by simpa using Subgroup.mem_subgroupOf.1 hmem
  have := eq_one_of_pow_two_pow_of_odd hM (k := ⟨y ^ 2, hyM⟩) (n := n) (by
    apply Subtype.ext
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← pow_mul, mul_comm, pow_mul, hy, one_pow])
  simpa using congrArg Subtype.val this

theorem twoRankAtLeastTwo_of_commute {X : Type*} [Group X] {a b : X} (ha : a * a = 1)
    (hb : b * b = 1) (hab : Commute a b) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) :
    TwoRankAtLeastTwo X := by
  classical
  set E := Subgroup.closure ({a, b} : Set X) with hE
  have hpair : ({a, b} : Set X).Pairwise Commute := by
    intro s hs t ht _
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · exact Commute.refl _
    · exact hab
    · exact hab.symm
    · exact Commute.refl _
  have hsq : ∀ s ∈ ({a, b} : Set X), s * s = 1 := by
    rintro s (rfl | rfl)
    · exact ha
    · exact hb
  have habsq : (a * b) * (a * b) = 1 := by
    calc (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab.eq]
      _ = 1 := by rw [show a * (a * b) * b = (a * a) * (b * b) by group, ha, hb, one_mul]
  have hset : (E : Set X) = {1, a, b, a * b} := by
    ext g
    constructor
    · intro hg
      obtain ⟨i, rfl | rfl⟩ := exists_zpow_of_mem_closure_pair ha hb hg
      · rcases Int.even_or_odd i with ⟨k, rfl⟩ | ⟨k, rfl⟩
        · left
          rw [← two_mul, zpow_mul, zpow_two, habsq, one_zpow]
        · right; right; right
          exact Set.mem_singleton_iff.2 (by
            rw [zpow_add, zpow_mul, zpow_two, habsq, one_zpow, one_mul, zpow_one])
      · rcases Int.even_or_odd i with ⟨k, rfl⟩ | ⟨k, rfl⟩
        · right; left
          rw [← two_mul, zpow_mul, zpow_two, habsq, one_zpow, one_mul]
        · right; right; left
          rw [zpow_add, zpow_mul, zpow_two, habsq, one_zpow, one_mul, zpow_one, mul_assoc,
            ← hab.eq, ← mul_assoc, ha, one_mul]
    · rintro (rfl | rfl | rfl | rfl)
      · exact E.one_mem
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact E.mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  refine ⟨E, ?_, fun g => Subtype.ext ?_⟩
  · have hab1 : a * b ≠ 1 := fun h => hne (by
      rw [mul_eq_one_iff_eq_inv.1 h]
      exact inv_eq_of_mul_eq_one_right hb)
    have haab : a ≠ a * b := fun h => hb1 (by simpa using h)
    have hbab : b ≠ a * b := fun h => ha1 (by
      have := congrArg (· * b⁻¹) h
      simpa using this.symm)
    have hcard : Nat.card E = Nat.card ((E : Set X)) := rfl
    rw [hcard, hset, Nat.card_coe_set_eq, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
      Set.ncard_pair hbab]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hne, haab⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun h => ha1 h.symm, fun h => hb1 h.symm, fun h => hab1 h.symm⟩
  · simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [pow_two]
    exact mul_self_eq_one_of_mem_closure hpair hsq g.2

theorem exists_bender_series {X : Type} [Group X] [Finite X] {H : Subgroup X}
    (hH : fusionStronglyEmbedded H) (hrank : TwoRankAtLeastTwo X) :
    ∃ (M N : Subgroup X) (_ : M.Normal) (_ : N.Normal) (_ : (M.subgroupOf N).Normal),
      M ≤ N ∧ Odd (Nat.card M) ∧ Odd N.index ∧ fusionIsBenderGroup (N ⧸ M.subgroupOf N) := by
  let hn := hH.to_native
  rcases CFSG.BenderSuzuki.theorem_SE H hn with hlow | hB
  · exact absurd (twoRankAtLeastTwo_involutionCore_iff.mpr hrank) hlow
  · let N : Subgroup X := involutionCore X
    let O : Subgroup N := twoPrimeCore N
    let M : Subgroup X := O.map N.subtype
    let : N.Normal := inferInstance
    let : O.Characteristic := by
      simpa [O, twoPrimeCore] using (CFSG.pPrimeCore_characteristic (p := 2) (G := N))
    let : M.Normal := ConjAct.normal_of_characteristic_of_normal
    have hsub : M.subgroupOf N = O := by
      change (O.map N.subtype).comap N.subtype = O
      exact Subgroup.comap_map_eq_self_of_injective N.subtype_injective O
    let : (M.subgroupOf N).Normal := by rw [hsub]; infer_instance
    have hMcard : Nat.card M = Nat.card O :=
      Subgroup.card_map_of_injective N.subtype_injective
    have hodd : Odd (Nat.card O) := by
      let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact Nat.coprime_two_left.mp
        (CFSG.pPrimeCore_coprime_card (p := 2) (G := N))
    refine ⟨M, N, inferInstance, inferInstance, inferInstance,
      Subgroup.map_subtype_le O, hMcard ▸ hodd,
      hn.involutionCore_index_odd_of_bender hB, ?_⟩
    apply fusionIsBenderGroup_of_isSimpleBenderGroup
    exact hB.1.map_mulEquiv (QuotientGroup.quotientMulEquivOfEq hsub.symm)

end CFSG.Timmesfeld.Bridge
