module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD7QA2Aux
public import CFSG.LocalAnalysis.StandardType.FS81.TwD7QCanonAux

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open
open Subgroup

open TwD7Q in
theorem isCyclic_of_le_centralizer_img_m0_twD7 {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdAssumptions b₀ K E Row.twD7) {B : Basis3 G 8}
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD7 B b₀)
    (S : Subgroup (Q (B.b 0 * B.b 1)))
    (hS : S ≤ centralizer (img (B.b 0 * B.b 1) (twD7M0 K B) : Set (Q (B.b 0 * B.b 1))))
    (h3 : IsPGroup 3 S) : IsCyclic S := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hKC, -, -, -, -, -, -⟩ := hstd.2.1.1
  have hb0 := hB.2.1
  have hM₀K : twD7M0 K B ≤ K := (commutator_le_self _).trans inf_le_right
  have hM₀C1 : twD7M0 K B ≤ centralizer ({B.b 1} : Set G) :=
    (commutator_le_self _).trans inf_le_left
  have hMβ : twD7M0 K B ≤ cen (B.b 0 * B.b 1) := fun m hm => by
    have h0 : m * B.b 0 = B.b 0 * m := by
      rw [hb0]; exact mem_centralizer_singleton_iff.mp (hKC (hM₀K hm))
    have h1 : m * B.b 1 = B.b 1 * m := mem_centralizer_singleton_iff.mp (hM₀C1 hm)
    show m ∈ centralizer ({B.b 0 * B.b 1} : Set G)
    rw [mem_centralizer_singleton_iff, ← mul_assoc, h0, mul_assoc, h1, mul_assoc]
  obtain ⟨-, hperf, -⟩ := centralizer_inf_eq_zpowers_sup_commutator_twD7 hstd hB hrec
  have hperf' : Group.IsPerfect ↥(twD7M0 K B) := hperf
  have hMM : twD7M0 K B ≤ ⁅twD7M0 K B, twD7M0 K B⁆ := by
    have h : (commutator ↥(twD7M0 K B)).map (twD7M0 K B).subtype =
        ⁅twD7M0 K B, twD7M0 K B⁆ := by
      rw [commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    rw [← h, hperf'.commutator_eq_top, ← MonoidHom.range_eq_map, range_subtype]
  obtain ⟨St, hStdef⟩ : ∃ St : Subgroup G,
      St = (S.comap (pr (B.b 0 * B.b 1))).map (cen (B.b 0 * B.b 1)).subtype := ⟨_, rfl⟩
  have hStcard : Nat.card St = 3 * Nat.card S := by
    rw [hStdef, card_map_of_injective (cen _).subtype_injective]
    have h := QuotientGroup.card_preimage_mk (zb (B.b 0 * B.b 1)) (S : Set (Q (B.b 0 * B.b 1)))
    rw [card_zb_twD7 B, SetLike.coe_sort_coe] at h
    exact h
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h3
  have hSt3 : IsPGroup 3 St :=
    IsPGroup.of_card (n := n + 1) (by rw [hStcard, hn, pow_succ, mul_comm])
  have hStC : St ≤ centralizer (twD7M0 K B : Set G) ⊓
      centralizer ({B.b 0 * B.b 1} : Set G) := by
    intro x hx
    rw [hStdef, mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨mem_centralizer_of_pr_mem_centralizer_img hMβ hMM (hS (mem_comap.mp hy)), y.2⟩
  have h9 :=
    card_le_nine_of_isPGroup_centralizer_m0_inf_centralizer_beta_twD7 hstd hB hrec hStC hSt3
  rw [hStcard, hn] at h9
  have hn1 : n ≤ 1 := by
    by_contra hcon
    have : 3 ^ 2 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases n
  · have : Subsingleton S := (Nat.card_eq_one_iff_unique.mp (by simpa using hn)).1
    exact isCyclic_of_subsingleton
  · exact isCyclic_of_prime_card (p := 3) (by simpa using hn)

open TwD7Q in
theorem isMaxElemAb3_twD7Quot {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdAssumptions b₀ K E Row.twD7) {B : Basis3 G 8}
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD7 B b₀) :
    IsMaxElemAb3 (centralizer ({B.twD7Quot.b 0} : Set (Q (B.b 0 * B.b 1))))
      B.twD7Quot.span := by
  classical
  have hrec' : RecOutTwD7 B (B.b 0) := by rw [hB.2.1]; exact hrec
  have hEl := B.twD7Quot.isElemAbelian_span
  refine ⟨fun y hy => ?_, hEl, fun E' _ hE'el hle => le_antisymm (fun q hq => ?_) hle⟩
  · rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hEl.1.is_comm.comm ⟨y, hy⟩ ⟨_, B.twD7Quot.b_mem_span 0⟩)
  · obtain ⟨x, rfl⟩ := pr_surjective (B.b 0 * B.b 1) q
    have hqc : pr _ x ∈ centralizer (B.twD7Quot.span : Set (Q (B.b 0 * B.b 1))) := by
      rw [mem_centralizer_iff]
      intro z hz
      exact congrArg Subtype.val (hE'el.1.is_comm.comm ⟨z, hle hz⟩ ⟨_, hq⟩)
    have hxE : (x : G) ∈ centralizer (E : Set G) := by
      rw [← hB.1]
      exact (B.pr_mem_centralizer_twD7Quot_span_iff hrec' x).mp hqc
    have h1 : pr (B.b 0 * B.b 1) (x ^ 3) = 1 := by
      rw [map_pow]
      exact hE'el.2 _ hq
    rw [pr_eq_one_iff] at h1
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h1
    have hβ3 : (B.b 0 * B.b 1) ^ 3 = 1 := by
      rw [← orderOf_b_mul_b B (by decide : (0 : Fin 8) ≠ 1)]
      exact pow_orderOf_eq_one _
    have hx9 : (x : G) ^ (3 ^ 2) = 1 := by
      have h33 : ((x : G) ^ 3) ^ 3 = 1 := by
        rw [← Subgroup.coe_pow, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
          zpow_natCast, hβ3, one_zpow]
      rw [show (3 : ℕ) ^ 2 = 3 * 3 by norm_num, pow_mul]
      exact h33
    have hxE' : (x : G) ∈ E := mem_E_of_three_element_centralizer_E_twD7 hstd hB hrec hxE
      (by norm_num) hx9
    rw [B.twD7Quot_span, hB.1]
    exact pr_mem_img hxE'


end CFSG.StandardType.FrameRoute.FS81
