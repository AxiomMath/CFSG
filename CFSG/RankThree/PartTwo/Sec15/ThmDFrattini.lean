module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.RankThree.PartTwo.Sec15.ThmD

open Subgroup

variable {M : Type*} [Group M] [Finite M]

theorem inf_eq_bot_of_isPGroup_of_not_dvd {p : ℕ} [hp : Fact p.Prime] {N A : Subgroup M}
    (hN : ¬ p ∣ Nat.card N) (hA : IsPGroup p A) : A ⊓ N = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxA : (⟨x, hx.1⟩ : A) ∈ (⊤ : Subgroup A) := trivial
  obtain ⟨k, hk⟩ := hA ⟨x, hx.1⟩
  have h1 : orderOf x ∣ p ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    have := congrArg Subtype.val hk
    simpa using this
  have h2 : orderOf x ∣ Nat.card N := by
    have : orderOf (⟨x, hx.2⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
    simpa [Subgroup.orderOf_mk] using this
  obtain ⟨j, hj, hjx⟩ := (Nat.dvd_prime_pow hp.out).mp h1
  by_contra hne
  have hx1 : x ≠ 1 := fun h => hne (by simpa using h)
  have hj0 : j ≠ 0 := by
    intro h
    rw [h, pow_zero] at hjx
    exact hx1 (orderOf_eq_one_iff.mp hjx)
  apply hN
  refine (dvd_pow_self p hj0).trans ?_ |>.trans h2
  rw [hjx]

theorem card_sup_of_inf_eq_bot {N A : Subgroup M} [N.Normal] (h : A ⊓ N = ⊥) :
    Nat.card ↥(A ⊔ N) = Nat.card A * Nat.card N := by
  have hdisj : Disjoint N A := by
    rw [disjoint_iff, inf_comm]
    exact h
  have h1 : N.relIndex (N ⊔ A) = N.relIndex A := relIndex_sup_left A N
  have h2 : N.relIndex A = Nat.card A := by
    rw [relIndex, Subgroup.subgroupOf_eq_bot.mpr hdisj, Subgroup.index_bot]
  have h3 : Nat.card N * N.relIndex (N ⊔ A) = Nat.card ↥(N ⊔ A) := by
    have := card_mul_index (N.subgroupOf (N ⊔ A))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv] at this
    exact this
  rw [sup_comm, ← h3, h1, h2, mul_comm]

theorem exists_conj_into_of_sylow {N A : Subgroup M} [N.Normal] (hN : ¬ 3 ∣ Nat.card N)
    (hA : IsPGroup 3 A) (y : M) (hy : ∀ a ∈ A, y * a * y⁻¹ ∈ A ⊔ N) :
    ∃ w ∈ A ⊔ N, ∀ a ∈ A, w * (y * a * y⁻¹) * w⁻¹ ∈ A := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X := A ⊔ N with hX
  have hAN : A ⊓ N = ⊥ := inf_eq_bot_of_isPGroup_of_not_dvd hN hA
  have hcardX : Nat.card ↥X = Nat.card A * Nat.card N := card_sup_of_inf_eq_bot hAN
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA
  have hfac : (Nat.card ↥X).factorization 3 = k := by
    rw [hcardX, hk, Nat.factorization_mul (pow_ne_zero _ (by norm_num)) Nat.card_pos.ne',
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three,
      Nat.factorization_eq_zero_of_not_dvd hN]
    simp
  set A₂ : Subgroup M := A.map (MulAut.conj y).toMonoidHom with hA₂
  have hA₂X : A₂ ≤ X := by
    rintro _ ⟨a, ha, rfl⟩
    simpa [MulAut.conj_apply] using hy a ha
  have hA₂card : Nat.card A₂ = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj y).injective
  have hP₁ : Nat.card ↥(A.subgroupOf X) = 3 ^ (Nat.card ↥X).factorization 3 := by
    rw [hfac, ← hk]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
  have hP₂ : Nat.card ↥(A₂.subgroupOf X) = 3 ^ (Nat.card ↥X).factorization 3 := by
    rw [hfac, ← hk, ← hA₂card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₂X).toEquiv
  let P₁ : Sylow 3 ↥X := Sylow.ofCard (A.subgroupOf X) hP₁
  let P₂ : Sylow 3 ↥X := Sylow.ofCard (A₂.subgroupOf X) hP₂
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥X P₂ P₁
  refine ⟨g, g.2, fun a ha => ?_⟩
  have h1 : (⟨y * a * y⁻¹, hy a ha⟩ : ↥X) ∈ (P₂ : Subgroup ↥X) :=
    ⟨a, ha, by simp [MulAut.conj_apply]⟩
  have h2 : g * ⟨y * a * y⁻¹, hy a ha⟩ * g⁻¹ ∈ (P₁ : Subgroup ↥X) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨_, h1, by simp [MulAut.conj_apply]⟩
  exact h2

theorem exists_normalizer_lift {N A : Subgroup M} [N.Normal] (hN : ¬ 3 ∣ Nat.card N)
    (hA : IsPGroup 3 A) (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (y : M)
    (hy : ∀ a ∈ A, QuotientGroup.mk' N (y * a * y⁻¹) ∈ A.map (QuotientGroup.mk' N)) :
    ∃ m ∈ Subgroup.normalizer (A : Set M), ∀ a ∈ A,
      QuotientGroup.mk' N (m * a * m⁻¹) = QuotientGroup.mk' N (y * a * y⁻¹) := by
  have hy' : ∀ a ∈ A, y * a * y⁻¹ ∈ A ⊔ N := by
    intro a ha
    obtain ⟨a', ha', h⟩ := hy a ha
    have h1 : (a')⁻¹ * (y * a * y⁻¹) ∈ N := by
      rw [← QuotientGroup.eq]
      exact h
    have h2 : y * a * y⁻¹ = a' * ((a')⁻¹ * (y * a * y⁻¹)) := by group
    rw [h2]
    exact (A ⊔ N).mul_mem (Subgroup.mem_sup_left ha') (Subgroup.mem_sup_right h1)
  obtain ⟨w, hw, hwA⟩ := exists_conj_into_of_sylow hN hA y hy'
  have hconj : ∀ a, (w * y) * a * (w * y)⁻¹ = w * (y * a * y⁻¹) * w⁻¹ := fun a => by group
  refine ⟨w * y, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      rw [hconj]
      exact hwA a ha
    · intro hma
      let f : A → A := fun b => ⟨(w * y) * b * (w * y)⁻¹, by rw [hconj]; exact hwA b b.2⟩
      have hinj : Function.Injective f := by
        intro b c hbc
        have := congrArg Subtype.val hbc
        simp only [f] at this
        have h3 : (b : M) = c := mul_left_cancel (mul_right_cancel this)
        exact Subtype.ext h3
      obtain ⟨b, hb⟩ := Finite.surjective_of_injective hinj ⟨(w * y) * a * (w * y)⁻¹, hma⟩
      have := congrArg Subtype.val hb
      simp only [f] at this
      have h3 : (b : M) = a := mul_left_cancel (mul_right_cancel this)
      rw [← h3]
      exact b.2
  · intro a ha
    obtain ⟨a₁, ha₁, n, hn, hw'⟩ := Subgroup.mem_sup_of_normal_right.mp hw
    obtain ⟨a', ha', h⟩ := hy a ha
    have hn1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    have hmw : QuotientGroup.mk' N w = QuotientGroup.mk' N a₁ := by
      rw [← hw', map_mul, hn1, mul_one]
    have h2 : QuotientGroup.mk' N a₁ * QuotientGroup.mk' N a' =
        QuotientGroup.mk' N a' * QuotientGroup.mk' N a₁ := by
      rw [← map_mul, ← map_mul, hAab a₁ ha₁ a' ha']
    rw [hconj, map_mul, map_mul, map_inv, hmw, ← h]
    exact mul_inv_eq_iff_eq_mul.mpr h2

end CFSG.RankThree.PartTwo.Sec15.ThmD
