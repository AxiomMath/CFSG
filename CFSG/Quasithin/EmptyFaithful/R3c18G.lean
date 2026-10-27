module

public import CFSG.RankThree.SubgroupLists.CentralizerPerfect

public section

namespace CFSG.Quasithin

namespace R3c18

theorem dvd_pow_sub_one_iff_of_pow {p q : ℕ} (hp : p.Prime) (hq : 0 < q) (j : ℕ) :
    p ∣ (q ^ p) ^ j - 1 ↔ p ∣ q ^ j - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 : q ^ p ≡ q [MOD p] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    exact ZMod.pow_card _
  have h2 : (q ^ p) ^ j ≡ q ^ j [MOD p] := h1.pow j
  have hQj : 1 ≤ (q ^ p) ^ j := Nat.one_le_pow _ _ (pow_pos hq _)
  have hqj : 1 ≤ q ^ j := Nat.one_le_pow _ _ hq
  rw [← (Nat.modEq_iff_dvd' hQj), ← (Nat.modEq_iff_dvd' hqj)]
  exact ⟨fun h => h.trans h2, fun h => h.trans h2.symm⟩

theorem exists_fixed_subfield {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (σ : K ≃+* K) {p : ℕ} (hσ : orderOf σ = p) :
    p ∣ f ∧ ∃ k : Subfield K, (∀ c ∈ k, σ c = c) ∧ Nat.card k = 2 ^ (f / p) := by
  obtain ⟨-, -, -, -, -, hA⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hf hK
  obtain ⟨hdvd, S, hS, hcard⟩ := hA (Subgroup.zpowers σ)
  rw [Nat.card_zpowers, hσ] at hdvd hcard
  refine ⟨hdvd, S, fun c hc => ?_, hcard⟩
  have : c ∈ (S : Set K) := hc
  rw [hS] at this
  exact this σ (Subgroup.mem_zpowers σ)

theorem dvd_card_of_two_le_pRank {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (h : 2 ≤ CFSG.pRank p G) : p ∣ Nat.card G := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h
  obtain ⟨E, -, -, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup G)
  have : p ∣ Nat.card E := by
    rw [hcard]
    exact dvd_pow_self p (by omega)
  exact this.trans (Subgroup.card_subgroup_dvd_card E)

theorem eq_one_of_forall_commute_sl2 {K : Type} [Field K] [CharP K 2]
    {b : Matrix.SpecialLinearGroup (Fin 2) K} (hb : ∀ A : Matrix.SpecialLinearGroup (Fin 2) K,
      b * A = A * b) : b = 1 := by
  have hcent : b ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) :=
    Subgroup.mem_center_iff.2 fun g => (hb g).symm
  obtain ⟨r, hr, hrb⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hcent
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hr1 : r = 1 := by
    have h0 : (r - 1) ^ 2 = 0 := by linear_combination hr2 + (1 - r) * h2
    exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h0)
  subst hr1
  apply Subtype.ext
  rw [← hrb]
  simp

theorem exists_fixed_sl2_elem {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {k : Subfield K}
    (hk : ∀ c ∈ k, σ c = c) {p : ℕ} (hp : p.Prime) (hd : p ∣ Nat.card k ^ 2 - 1) :
    ∃ a : Matrix.SpecialLinearGroup (Fin 2) K, orderOf a = p ∧
      Matrix.SpecialLinearGroup.map σ.toRingHom a = a := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite k := inferInstance
  have hcard : p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) k) := by
    rw [CFSG.RankThree.SubgroupLists.card_sl2_field]
    exact Dvd.dvd.mul_left hd _
  obtain ⟨a₀, ha₀⟩ := exists_prime_orderOf_dvd_card' p hcard
  have hinj : Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2) k.subtype) := by
    intro A B h
    apply Subtype.ext
    ext i j
    have := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 2) K =>
      (X : Matrix (Fin 2) (Fin 2) K) i j) h
    simpa using this
  refine ⟨Matrix.SpecialLinearGroup.map k.subtype a₀, ?_, ?_⟩
  · rw [← ha₀]
    exact (orderOf_injective _ hinj a₀)
  · apply Subtype.ext
    ext i j
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact hk _ (a₀ i j).2

end R3c18

end CFSG.Quasithin
