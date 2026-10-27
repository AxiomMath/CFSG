module

public import CFSG.Permutation.UnitaryThreeRecognition.AbelianQ

public section

open MulAction

open scoped Classical

namespace CFSG.UnitaryThreeRecognition

variable {G Ω : Type*} [Group G] [MulAction G Ω]

namespace AbelianQ

variable {Q : Subgroup G} {j : G} {hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x}

section Count

variable [Fintype G] [Fintype Ω]

@[expose] noncomputable def levelPairs (Q : Subgroup G) (j : G)
    (hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) (a c : Ω) : Finset (Ω × Ω) :=
  Finset.univ.filter fun xy =>
    xy.1 ≠ c ∧ xy.2 ≠ c ∧ xy.1 ≠ xy.2 ∧ SameLevel Q j hQab a c xy.1 xy.2

@[expose] noncomputable def levelPoints (Q : Subgroup G) (j : G)
    (hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) (a x y : Ω) : Finset Ω :=
  Finset.univ.filter fun c => c ≠ x ∧ c ≠ y ∧ SameLevel Q j hQab a c x y

theorem card_filter_mem (H : Subgroup G) : (Finset.univ.filter (· ∈ H)).card = Nat.card H := by
  rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]

theorem sum_ite_ne (a : Ω) (n : ℕ) :
    ∑ x : Ω, (if x = a then 0 else n) = (Fintype.card Ω - 1) * n := by
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul,
    Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ]

theorem card_level_base {a b : Ω} (hQ : IsRootSubgroup Q a) (hb : b ≠ a)
    (hcomm : ∀ t₁ ∈ pairStab G a b, ∀ t₂ ∈ pairStab G a b, t₁ * t₂ = t₂ * t₁)
    (hj : j ∈ pairStab G a b) {x : Ω} (hx : x ≠ a) :
    (Finset.univ.filter fun y => y ≠ a ∧ x ≠ y ∧ SameLevel Q j hQab a a x y).card =
      Nat.card (invSub Q j hQab) - 1 := by
  have hset : (Finset.univ.filter fun y => y ≠ a ∧ x ≠ y ∧ SameLevel Q j hQab a a x y) =
      ((Finset.univ.filter (· ∈ invSub Q j hQab)).erase 1).image (· • x) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_erase, sameLevel_base_iff hQ hb hcomm hj]
    constructor
    · rintro ⟨-, hxy, v, hv, rfl⟩
      refine ⟨v, ⟨?_, hv⟩, rfl⟩
      rintro rfl
      exact hxy (one_smul _ _).symm
    · rintro ⟨v, ⟨hv1, hv⟩, rfl⟩
      refine ⟨hQ.smul_ne (invSub_le hv) hx, ?_, v, hv, rfl⟩
      intro h
      exact hv1 (hQ.eq_one_of_smul_eq (invSub_le hv) hx h.symm)
  rw [hset, Finset.card_image_of_injOn, Finset.card_erase_of_mem, card_filter_mem]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (invSub Q j hQab).one_mem
  · intro v hv w hw hvw
    simp only [Finset.coe_erase, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_sdiff,
      Set.mem_ofPred_eq, Set.mem_singleton_iff] at hv hw
    exact hQ.eq_of_smul_eq (invSub_le hv.1) (invSub_le hw.1) hx hvw

theorem card_levelPairs_base {a b : Ω} (hQ : IsRootSubgroup Q a) (hb : b ≠ a)
    (hcomm : ∀ t₁ ∈ pairStab G a b, ∀ t₂ ∈ pairStab G a b, t₁ * t₂ = t₂ * t₁)
    (hj : j ∈ pairStab G a b) :
    (levelPairs Q j hQab a a).card =
      (Fintype.card Ω - 1) * (Nat.card (invSub Q j hQab) - 1) := by
  rw [levelPairs, Finset.card_filter, Fintype.sum_prod_type, ← sum_ite_ne a]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x = a
  · subst hx
    simp
  · rw [ite_eq_right hx, ← card_level_base hQ hb hcomm hj hx, Finset.card_filter]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [hx, ne_eq, not_false_eq_true, true_and]

omit [Fintype G] in
theorem card_levelPairs_smul {a : Ω} (k : G) (c : Ω) :
    (levelPairs Q j hQab a (k • c)).card = (levelPairs Q j hQab a c).card := by
  symm
  apply Finset.card_nbij' (fun xy => (k • xy.1, k • xy.2)) (fun xy => (k⁻¹ • xy.1, k⁻¹ • xy.2))
  · rintro ⟨x, y⟩ h
    simp only [levelPairs, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at h ⊢
    obtain ⟨hx, hy, hxy, hl⟩ := h
    exact ⟨fun h => hx (smul_left_cancel k h), fun h => hy (smul_left_cancel k h),
      fun h => hxy (smul_left_cancel k h), (sameLevel_smul_iff k).mpr hl⟩
  · rintro ⟨x, y⟩ h
    simp only [levelPairs, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at h ⊢
    obtain ⟨hx, hy, hxy, hl⟩ := h
    refine ⟨fun h => hx (by rw [← h, smul_inv_smul]), fun h => hy (by rw [← h, smul_inv_smul]),
      fun h => hxy (by rw [← smul_inv_smul k x, h, smul_inv_smul]), ?_⟩
    rw [← sameLevel_smul_iff k, smul_inv_smul, smul_inv_smul]
    exact hl
  · rintro ⟨x, y⟩ -
    simp
  · rintro ⟨x, y⟩ -
    simp

omit [Fintype G] in
theorem card_levelPoints_smul {a : Ω} (k : G) (x y : Ω) :
    (levelPoints Q j hQab a (k • x) (k • y)).card = (levelPoints Q j hQab a x y).card := by
  symm
  apply Finset.card_nbij' (fun c => k • c) (fun c => k⁻¹ • c)
  · intro c h
    simp only [levelPoints, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at h ⊢
    obtain ⟨hx, hy, hl⟩ := h
    exact ⟨fun h => hx (smul_left_cancel k h), fun h => hy (smul_left_cancel k h),
      (sameLevel_smul_iff k).mpr hl⟩
  · intro c h
    simp only [levelPoints, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at h ⊢
    obtain ⟨hx, hy, hl⟩ := h
    refine ⟨fun h => hx (by rw [← h, smul_inv_smul]), fun h => hy (by rw [← h, smul_inv_smul]),
      ?_⟩
    rw [← sameLevel_smul_iff k, smul_inv_smul]
    exact hl
  · intro c _
    simp
  · intro c _
    simp

omit [Fintype G] in
theorem sum_card_levelPairs (a : Ω) :
    ∑ c : Ω, (levelPairs Q j hQab a c).card =
      ∑ xy : Ω × Ω, if xy.1 = xy.2 then 0 else (levelPoints Q j hQab a xy.1 xy.2).card := by
  simp only [levelPairs, levelPoints, Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun xy _ => ?_
  by_cases hxy : xy.1 = xy.2
  · rw [ite_eq_left hxy]
    exact Finset.sum_eq_zero fun c _ => by simp [hxy]
  · rw [ite_eq_right hxy]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    apply propext
    constructor
    · rintro ⟨h1, h2, -, h4⟩
      exact ⟨fun h => h1 h.symm, fun h => h2 h.symm, h4⟩
    · rintro ⟨h1, h2, h4⟩
      exact ⟨fun h => h1 h.symm, fun h => h2 h.symm, hxy, h4⟩

end Count

end AbelianQ

end CFSG.UnitaryThreeRecognition
