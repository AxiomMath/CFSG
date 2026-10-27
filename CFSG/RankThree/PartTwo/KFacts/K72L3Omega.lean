module

public import CFSG.RankThree.PartTwo.KFacts.K72L3Linear
public import CFSG.RankThree.PartTwo.KFacts.K72L3Unitary
public import CFSG.RankThree.PartTwo.Sec8.Notation

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag

theorem exists_pow_mul_eq_one_of_orderOf_eq_three {K : Type*} [Field K] [Finite K]
    {s s' : K ≃+* K} (hs : orderOf s = 3) (hs' : orderOf s' = 3) : ∃ i : ℕ, s ^ i * s' = 1 := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨p, -, m, hp, hK⟩ := FiniteField.card' K
  have := (card_ringAut_and_isCyclic hp K (by rw [Nat.card_eq_fintype_card, hK])).2
  have heq : Subgroup.zpowers s' = Subgroup.zpowers s := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers, hs, hs']
  have hmem : s' ∈ Subgroup.zpowers s := by
    rw [← heq]
    exact Subgroup.mem_zpowers s'
  have hfin : IsOfFinOrder s := orderOf_pos_iff.mp (by rw [hs]; norm_num)
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp (hfin.mem_powers_iff_mem_zpowers.mpr hmem)
  refine ⟨2 * k, ?_⟩
  rw [← hk, ← pow_add, show 2 * k + k = 3 * k by ring, pow_mul, ← hs, pow_orderOf_eq_one,
    one_pow]

section Linear

variable {K : Type} [Field K]

theorem exists_pow_mul_isInnerAut_of_mulEquiv_projSL {X : Type} [Group X] [Finite K]
    (hK : Nat.card K % 3 = 2) (e : X ≃* CFSG.Assembly.RankThreeEven.projSL 3 K)
    {σ τ : MulAut X} (hσ3 : σ ^ 3 = 1) (hσ : ¬ IsInnerAut σ) (hτ3 : τ ^ 3 = 1)
    (hτ : ¬ IsInnerAut τ) : ∃ i : ℕ, IsInnerAut (σ ^ i * τ) := by
  obtain ⟨φ⟩ := nonempty_projSL_mulEquiv 3 K
  have key : ∀ α : MulAut X, α ^ 3 = 1 → ¬ IsInnerAut α → ∃ s : K ≃+* K, orderOf s = 3 ∧
      ∃ H : GL (Fin 3) K, MulAut.congr (e.trans φ) α =
        conjAut 3 K H * fieldAut 3 K s * (conjAut 3 K H)⁻¹ := fun α hα3 hα => by
    have hβ3 : MulAut.congr (e.trans φ) α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
    have hD : MulAut.congr (e.trans φ) α ∉ linearAutGroup 3 K := fun h =>
      hα ((isInnerAut_congr (e.trans φ) α).mp (isInnerAut_of_mem_linearAutGroup hK h))
    exact linear_order_three_field_descent le_rfl _ hβ3 hD
  obtain ⟨s, hs, H, hσH⟩ := key σ hσ3 hσ
  obtain ⟨s', hs', H', hτH⟩ := key τ hτ3 hτ
  obtain ⟨i, hi⟩ := exists_pow_mul_eq_one_of_orderOf_eq_three hs hs'
  refine ⟨i, (isInnerAut_congr (e.trans φ) _).mp (isInnerAut_of_mem_linearAutGroup hK ?_)⟩
  have : (linearAutGroup 3 K).Normal := (stdPinnedPSL_stable (n := 3) (K := K) le_rfl).normal
  have hc : ∀ (A : GL (Fin 3) K) (g : MulAut (projectiveSL 3 K)),
      ((conjAut 3 K A * g * (conjAut 3 K A)⁻¹ : MulAut (projectiveSL 3 K)) :
        MulAut (projectiveSL 3 K) ⧸ linearAutGroup 3 K) = g := fun A g => by
    have h1 : ((conjAut 3 K A : MulAut (projectiveSL 3 K)) :
        MulAut (projectiveSL 3 K) ⧸ linearAutGroup 3 K) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (conjAut_mem_linearAutGroup A)
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1, one_mul, inv_one,
      mul_one]
  rw [← QuotientGroup.eq_one_iff, map_mul, map_pow, hσH, hτH, QuotientGroup.mk_mul,
    QuotientGroup.mk_pow, hc, hc, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_mul, ← map_pow,
    ← map_mul, hi, map_one, QuotientGroup.mk_one]

theorem center_projectiveSL_three_eq_bot (hK : Nat.card K % 3 = 2) :
    Subgroup.center (projectiveSL 3 K) = ⊥ := by
  have e := MulEquiv.ofBijective (proj 3 K) ⟨proj_three_injective hK, proj_surjective 3 K⟩
  have hS : Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) = ⊥ := by
    rw [← scalars_eq_center, scalars_three_eq_bot_of_mod_three hK]
  rw [← Subgroup.map_center_eq e, hS, Subgroup.map_bot]

end Linear

section Unitary

variable {p f : ℕ} {K : Type} [Field K]

theorem exists_pow_mul_isInnerAut_of_mulEquiv_unitaryPSU {X : Type} [Group X]
    (h : UnitaryFieldData p f K) (hq : p ^ f % 3 = 1) (hq2 : 2 < p ^ f)
    (e : X ≃* unitaryPSU h 3) {σ τ : MulAut X} (hσ3 : σ ^ 3 = 1) (hσ : ¬ IsInnerAut σ)
    (hτ3 : τ ^ 3 = 1) (hτ : ¬ IsInnerAut τ) : ∃ i : ℕ, IsInnerAut (σ ^ i * τ) := by
  have := h.finite
  have key : ∀ α : MulAut X, α ^ 3 = 1 → ¬ IsInnerAut α → ∃ s : K ≃+* K, orderOf s = 3 ∧
      ∃ H : unitaryIsom3 h, MulAut.congr e α =
        psuConj h H * psuField h s * (psuConj h H)⁻¹ := fun α hα3 hα => by
    have hβ3 : MulAut.congr e α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
    have hD : MulAut.congr e α ∉ (psuConj h).range := fun hm =>
      hα ((isInnerAut_congr e α).mp (isInnerAut_of_mem_psuConj_range h hq hm))
    exact unitary_order_three_field_descent hq2 _ hβ3 hD
  obtain ⟨s, hs, H, hσH⟩ := key σ hσ3 hσ
  obtain ⟨s', hs', H', hτH⟩ := key τ hτ3 hτ
  obtain ⟨i, hi⟩ := exists_pow_mul_eq_one_of_orderOf_eq_three hs hs'
  refine ⟨i, (isInnerAut_congr e _).mp (isInnerAut_of_mem_psuConj_range h hq ?_)⟩
  have : (psuConj h).range.Normal := (stdPinnedPSU3_stable (h := h) hq2).normal
  have hc : ∀ (A : unitaryIsom3 h) (g : MulAut (unitaryPSU h 3)),
      ((psuConj h A * g * (psuConj h A)⁻¹ : MulAut (unitaryPSU h 3)) :
        MulAut (unitaryPSU h 3) ⧸ (psuConj h).range) = g := fun A g => by
    have h1 : ((psuConj h A : MulAut (unitaryPSU h 3)) :
        MulAut (unitaryPSU h 3) ⧸ (psuConj h).range) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨A, rfl⟩
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1, one_mul, inv_one,
      mul_one]
  rw [← QuotientGroup.eq_one_iff, map_mul, map_pow, hσH, hτH, QuotientGroup.mk_mul,
    QuotientGroup.mk_pow, hc, hc, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_mul, ← map_pow,
    ← map_mul, hi, map_one, QuotientGroup.mk_one]

private theorem center_unitaryPSU_three_eq_bot (h : UnitaryFieldData p f K) (hq : p ^ f % 3 = 1)
    (hq2 : 2 < p ^ f) : Subgroup.center (unitaryPSU h 3) = ⊥ := by
  have e := MulEquiv.ofBijective (unitaryProj h 3)
    ⟨unitaryProj_three_injective h hq, unitaryProj_surjective h 3⟩
  have hS : Subgroup.center (unitarySU p f K 3) = ⊥ := by
    rw [center_unitarySU_three (h := h) hq2, unitaryScalars_three_eq_bot_of_mod_three h hq]
  rw [← Subgroup.map_center_eq e, hS, Subgroup.map_bot]

end Unitary

theorem center_eq_bot_of_mulEquiv_of_center_eq_bot {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (hY : Subgroup.center Y = ⊥) : Subgroup.center X = ⊥ := by
  have h := Subgroup.map_center_eq e
  rw [hY] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ (by exact e.injective)).mp h

theorem exists_pow_mul_isInnerAut_of_isoLThreeMinusPi {X : Type} [Group X] [Finite X] {n : ℕ}
    (hn : 1 ≤ n) (hX : Sec8.IsoLThreeMinusPi X 2 (3 * n)) {P : Subgroup (MulAut X)}
    (_hP : IsPGroup 3 P) {σ τ : MulAut X} (_hσP : σ ∈ P) (_hτP : τ ∈ P) (hσ3 : σ ^ 3 = 1)
    (hσ : ¬ IsInnerAut σ) (hτ3 : τ ^ 3 = 1) : ∃ i : ℕ, IsInnerAut (σ ^ i * τ) := by
  by_cases hτ : IsInnerAut τ
  · exact ⟨0, by rwa [pow_zero, one_mul]⟩
  have hq2 : 2 < 2 ^ (3 * n) :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ 3 * n))
  rcases hX with ⟨hq, ⟨e⟩⟩ | ⟨hq, ⟨e⟩⟩
  · have h : UnitaryFieldData 2 (3 * n) (GaloisField 2 (2 * (3 * n))) :=
      ⟨Nat.prime_two, by omega, GaloisField.card 2 _ (by omega)⟩
    obtain ⟨φ⟩ := nonempty_unitaryPSU_mulEquiv_projSU h
    exact exists_pow_mul_isInnerAut_of_mulEquiv_unitaryPSU h hq hq2 (e.trans φ.symm) hσ3 hσ hτ3
      hτ
  · exact exists_pow_mul_isInnerAut_of_mulEquiv_projSL
      (by rwa [GaloisField.card 2 (3 * n) (by omega)]) e hσ3 hσ hτ3 hτ

theorem center_eq_bot_of_isoLThreeMinusPi {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 1 ≤ n)
    (hX : Sec8.IsoLThreeMinusPi X 2 (3 * n)) : Subgroup.center X = ⊥ := by
  have hq2 : 2 < 2 ^ (3 * n) :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ 3 * n))
  rcases hX with ⟨hq, ⟨e⟩⟩ | ⟨hq, ⟨e⟩⟩
  · have h : UnitaryFieldData 2 (3 * n) (GaloisField 2 (2 * (3 * n))) :=
      ⟨Nat.prime_two, by omega, GaloisField.card 2 _ (by omega)⟩
    obtain ⟨φ⟩ := nonempty_unitaryPSU_mulEquiv_projSU h
    exact center_eq_bot_of_mulEquiv_of_center_eq_bot (e.trans φ.symm)
      (center_unitaryPSU_three_eq_bot h hq hq2)
  · obtain ⟨φ⟩ := nonempty_projSL_mulEquiv 3 (GaloisField 2 (3 * n))
    exact center_eq_bot_of_mulEquiv_of_center_eq_bot (e.trans φ)
      (center_projectiveSL_three_eq_bot (by rwa [GaloisField.card 2 (3 * n) (by omega)]))

end CFSG.RankThree.PartTwo.KFacts
