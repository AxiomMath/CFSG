module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS152J2

open Subgroup

theorem exists_conj_sq_mem {G : Type*} [Group G] [Finite G] (T : Sylow 2 G) {Q : Subgroup G}
    (hQ : IsPGroup 2 Q) (hcard : Nat.card (T : Subgroup G) ≤ 2 * Nat.card Q) :
    ∃ g : G, ∀ x ∈ (T : Subgroup G), g * x ^ 2 * g⁻¹ ∈ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T', hQT'⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T T'
  have hT'card : Nat.card (T' : Subgroup G) = Nat.card (T : Subgroup G) := by
    rw [Sylow.card_eq_multiplicity T', Sylow.card_eq_multiplicity T]
  have key : ∀ t ∈ (T' : Subgroup G), t ^ 2 ∈ Q := by
    intro t ht
    set Q' : Subgroup (T' : Subgroup G) := Q.subgroupOf (T' : Subgroup G) with hQ'
    have hQcard : Nat.card Q' = Nat.card Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQT').toEquiv
    have hmul : Nat.card Q' * Q'.index = Nat.card (T' : Subgroup G) := Subgroup.card_mul_index Q'
    have hQpos : 0 < Nat.card Q := Nat.card_pos
    have hidx : Q'.index ≤ 2 := by
      by_contra hlt
      push Not at hlt
      have : Nat.card Q * 3 ≤ Nat.card Q * Q'.index := Nat.mul_le_mul_left _ hlt
      rw [hQcard] at hmul
      omega
    have hidx0 : Q'.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hsq : (⟨t, ht⟩ : (T' : Subgroup G)) ^ 2 ∈ Q' := by
      rcases (by omega : Q'.index = 1 ∨ Q'.index = 2) with h1 | h2
      · rw [Subgroup.index_eq_one.mp h1]
        exact Subgroup.mem_top _
      · exact Subgroup.sq_mem_of_index_two h2 _
    exact Subgroup.mem_subgroupOf.mp hsq
  refine ⟨g, fun x hx => ?_⟩
  have hxT' : g * x * g⁻¹ ∈ (T' : Subgroup G) := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨x, hx, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
  have := key _ hxT'
  rwa [conj_pow] at this

theorem exists_conj_zpowers_eq {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {K : Subgroup G} (hK : ¬ p ^ 2 ∣ Nat.card K) {y y' : G} (hy : y ∈ K) (hy' : y' ∈ K)
    (hoy : orderOf y = p) (hoy' : orderOf y' = p) :
    ∃ k ∈ K, zpowers y' = zpowers (k * y * k⁻¹) := by
  have hfac : (Nat.card K).factorization p = 1 := by
    have h1 : p ∣ Nat.card K := by
      have := orderOf_dvd_natCard (⟨y, hy⟩ : K)
      rwa [Subgroup.orderOf_mk, hoy] at this
    have hne : Nat.card K ≠ 0 := Nat.card_pos.ne'
    have h1' : 1 ≤ (Nat.card K).factorization p :=
      (hp.out.pow_dvd_iff_le_factorization hne).mp (by simpa using h1)
    have h2' : ¬ 2 ≤ (Nat.card K).factorization p := fun h =>
      hK ((hp.out.pow_dvd_iff_le_factorization hne).mpr h)
    omega
  have hcard : ∀ {w : G} (hw : w ∈ K), orderOf w = p →
      Nat.card ((zpowers w).subgroupOf K) = p ^ (Nat.card K).factorization p := by
    intro w hw how
    rw [hfac, pow_one, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Subgroup.zpowers_le.mpr hw)).toEquiv, Nat.card_zpowers, how]
  let S₁ : Sylow p K := Sylow.ofCard ((zpowers y).subgroupOf K) (hcard hy hoy)
  let S₂ : Sylow p K := Sylow.ofCard ((zpowers y').subgroupOf K) (hcard hy' hoy')
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K S₁ S₂
  have hmem : (⟨y', hy'⟩ : K) ∈ (S₂ : Subgroup K) := by
    show (⟨y', hy'⟩ : K) ∈ (zpowers y').subgroupOf K
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers y')
  rw [← hk, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hmem
  obtain ⟨s, hs, hse⟩ := hmem
  have hs' : (s : G) ∈ zpowers y := Subgroup.mem_subgroupOf.mp hs
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hs'
  have hy'eq : y' = (k : G) * (s : G) * (k : G)⁻¹ := by
    have := congrArg Subtype.val hse
    simpa [MulAut.smul_def, MulAut.conj_apply] using this.symm
  have hy'mem : y' ∈ zpowers ((k : G) * y * (k : G)⁻¹) := by
    refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
    rw [hy'eq, ← hj, conj_zpow]
  have hord : orderOf ((k : G) * y * (k : G)⁻¹) = p := by
    have := orderOf_injective (MulAut.conj (k : G)).toMonoidHom (MulAut.conj (k : G)).injective y
    rw [← hoy, ← this]
    rfl
  refine ⟨k, k.2, ?_⟩
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hy'mem) ?_
  rw [Nat.card_zpowers, Nat.card_zpowers, hord, hoy']

end CFSG.RankThree.PartTwo.KFacts.KS152J2
