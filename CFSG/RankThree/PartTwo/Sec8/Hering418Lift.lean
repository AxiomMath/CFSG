module

public import CFSG.RankThree.PartTwo.Sec4.HeringK419OneFieldRank

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG.Open

theorem isPGroup_zpowers_three {G : Type*} [Group G] {x : G} (hx : x ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers x) := by
  rw [IsPGroup.iff_orderOf]
  rintro ⟨g, hg⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have h1 : (⟨x ^ k, hg⟩ : Subgroup.zpowers x) ^ 3 = 1 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, Subgroup.coe_one, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, hx, one_zpow]
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
    (orderOf_dvd_of_pow_eq_one (by rw [show (3 : ℕ) = 3 ^ 1 by norm_num] at h1; exact h1))
  exact ⟨i, hi⟩

theorem mem_closure_pair_iff {M : Type*} [Group M] {x y z : M} (hxy : Commute x y) :
    z ∈ Subgroup.closure ({x, y} : Set M) ↔ ∃ i j : ℤ, z = x ^ i * y ^ j := by
  constructor
  · intro hz
    induction hz using Subgroup.closure_induction with
    | mem s hs =>
      rcases hs with rfl | hs
      · exact ⟨1, 0, by simp⟩
      · rw [Set.mem_singleton_iff] at hs
        subst hs
        exact ⟨0, 1, by simp⟩
    | one => exact ⟨0, 0, by simp⟩
    | mul u v _ _ hu hv =>
      obtain ⟨i, j, rfl⟩ := hu
      obtain ⟨k, l, rfl⟩ := hv
      refine ⟨i + k, j + l, ?_⟩
      have hc : Commute (y ^ j) (x ^ k) := (hxy.symm.zpow_zpow j k)
      calc x ^ i * y ^ j * (x ^ k * y ^ l) = x ^ i * (y ^ j * x ^ k) * y ^ l := by group
        _ = x ^ i * (x ^ k * y ^ j) * y ^ l := by rw [hc.eq]
        _ = x ^ (i + k) * y ^ (j + l) := by
          rw [zpow_add, zpow_add]; group
    | inv u _ hu =>
      obtain ⟨i, j, rfl⟩ := hu
      refine ⟨-i, -j, ?_⟩
      have hc : Commute (y ^ (-j)) (x ^ (-i)) := hxy.symm.zpow_zpow (-j) (-i)
      rw [mul_inv_rev, ← zpow_neg, ← zpow_neg]
      exact hc.eq
  · rintro ⟨i, j, rfl⟩
    exact mul_mem (zpow_mem (Subgroup.subset_closure (by simp)) i)
      (zpow_mem (Subgroup.subset_closure (by simp)) j)

theorem exists_orderOf_three_commute {G : Type*} [Group G] [Finite G] {K : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (K : Set G)) (ha3 : a ^ 3 = 1) (hK : 3 ∣ Nat.card K) :
    ∃ x ∈ K, orderOf x = 3 ∧ a * x = x * a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : Subgroup.zpowers a ≤ Subgroup.normalizer (K : Set G) :=
    Subgroup.zpowers_le.mpr ha
  let ψ : Subgroup.zpowers a →* MulAut K :=
    (Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hle)
  letI : MulAction (Subgroup.zpowers a) K := MulAction.compHom K ψ
  have hP : IsPGroup 3 (Subgroup.zpowers a) := isPGroup_zpowers_three ha3
  have hmod := hP.card_modEq_card_fixedPoints K
  have h3 : 3 ∣ Nat.card (MulAction.fixedPoints (Subgroup.zpowers a) K) := by
    have h1 : Nat.card K ≡ 0 [MOD 3] := (Nat.modEq_zero_iff_dvd).2 hK
    exact (Nat.modEq_zero_iff_dvd).1 (hmod.symm.trans h1)
  set C : Subgroup G := K ⊓ Subgroup.centralizer ({a} : Set G) with hC
  have hfix : ∀ k : K, k ∈ MulAction.fixedPoints (Subgroup.zpowers a) K ↔
      (k : G) ∈ Subgroup.centralizer ({a} : Set G) := by
    intro k
    rw [MulAction.mem_fixedPoints, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h1 := h ⟨a, Subgroup.mem_zpowers a⟩
      have h2 : ((⟨a, Subgroup.mem_zpowers a⟩ : Subgroup.zpowers a) • k : K) = k := h1
      have h3 := congrArg (fun y : K => (y : G)) h2
      change a * (k : G) * a⁻¹ = k at h3
      calc (k : G) * a = a * (k : G) * a⁻¹ * a := by rw [h3]
        _ = a * (k : G) := by group
    · intro h g
      obtain ⟨g, hg⟩ := g
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      apply Subtype.ext
      change a ^ m * (k : G) * (a ^ m)⁻¹ = k
      have hc : Commute a (k : G) := h.symm
      rw [(hc.zpow_left m).eq, mul_inv_cancel_right]
  have hcard : Nat.card (MulAction.fixedPoints (Subgroup.zpowers a) K) = Nat.card C := by
    refine Nat.card_congr ⟨fun k => ⟨(k.1 : G), k.1.2, (hfix k.1).1 k.2⟩,
      fun c => ⟨⟨c.1, c.2.1⟩, (hfix ⟨c.1, c.2.1⟩).2 c.2.2⟩, fun k => rfl, fun c => rfl⟩
  rw [hcard] at h3
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := C) 3 h3
  refine ⟨(x : G), x.2.1, ?_, ?_⟩
  · exact (Subgroup.orderOf_coe x).trans hx
  · exact (Subgroup.mem_centralizer_singleton_iff.mp x.2.2).symm

theorem three_mul_card_le {M : Type*} [Group M] [Finite M] {E F : Subgroup M} (hEF : E ≤ F)
    (hF : IsPGroup 3 F) (hne : E ≠ F) : 3 * Nat.card E ≤ Nat.card F := by
  obtain ⟨k, hk⟩ := hF.exists_card_eq
  obtain ⟨j, hj, hjE⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (hk ▸ Subgroup.card_dvd_of_le hEF)
  have hjk : j < k := by
    rcases hj.lt_or_eq with h | h
    · exact h
    · exfalso
      exact hne (Subgroup.eq_of_le_of_card_ge hEF (le_of_eq (by rw [hjE, hk, h])))
  rw [hjE, hk]
  calc 3 * 3 ^ j = 3 ^ (j + 1) := by ring
    _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hjk

theorem isElemAbelian_closure_three {M : Type*} [Group M] [Finite M] {x y z : M}
    (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hz3 : z ^ 3 = 1) (hx1 : x ≠ 1)
    (hxy : x * y = y * x) (hxz : x * z = z * x) (hyz : y * z = z * y)
    (hy : y ∉ Subgroup.zpowers x) (hz : z ∉ Subgroup.closure ({x, y} : Set M)) :
    IsElemAbelian 3 (Subgroup.closure ({x, y, z} : Set M)) ∧
      27 ≤ Nat.card (Subgroup.closure ({x, y, z} : Set M)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpair : ({x, y, z} : Set M).Pairwise Commute := by
    intro a ha b hb hab
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    all_goals first | exact absurd rfl hab | assumption | exact Eq.symm ‹_›
  have h3 : ∀ s ∈ ({x, y, z} : Set M), s ^ 3 = 1 := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl <;> assumption
  have hF := Sec4.HeringOF.isElemAbelian_closure hpair h3
  refine ⟨hF, ?_⟩
  have hpair2 : ({x, y} : Set M).Pairwise Commute := by
    intro a ha b hb hab
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    all_goals first | exact absurd rfl hab | assumption | exact Eq.symm ‹_›
  have hE := Sec4.HeringOF.isElemAbelian_closure hpair2 (by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl <;> assumption)
  set E := Subgroup.closure ({x, y} : Set M) with hEdef
  set F := Subgroup.closure ({x, y, z} : Set M) with hFdef
  have hEF : E ≤ F := Subgroup.closure_mono
    (Set.insert_subset_insert (Set.singleton_subset_iff.mpr (Set.mem_insert y _)))
  have hzF : z ∈ F := Subgroup.subset_closure (by simp)
  have hFp : IsPGroup 3 F := fun w => ⟨1, Subtype.ext (by simpa using hF.2 w.1 w.2)⟩
  have hEp : IsPGroup 3 E := fun w => ⟨1, Subtype.ext (by simpa using hE.2 w.1 w.2)⟩
  have hne : E ≠ F := fun h => hz (h ▸ hzF)
  have h1 := three_mul_card_le hEF hFp hne
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hxE : Subgroup.zpowers x ≤ E :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have hyE : y ∈ E := Subgroup.subset_closure (by simp)
  have hne2 : Subgroup.zpowers x ≠ E := fun h => hy (h ▸ hyE)
  have h2 := three_mul_card_le hxE hEp hne2
  rw [Nat.card_zpowers, hxo] at h2
  omega

end CFSG.RankThree.PartTwo.Sec8.Hering418
