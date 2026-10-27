module

public import CFSG.RankThree.PartTwo.Sec21.Item2131One

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item222Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts.KP14 (Mat3 signedMat monomial IsReflection isReflection_iff
  card_range_eq)
open Matrix

set_option synthInstance.maxHeartbeats 1000000 in
set_option synthInstance.maxSize 100000 in
theorem card_stab_le : ∀ v : Fin 3 → ZMod 3, v ≠ 0 →
    ((Finset.univ.filter fun p : (Fin 3 → Fin 3) × (Fin 3 → ZMod 3) =>
        Function.Bijective p.1 ∧ (∀ j, p.2 j ≠ 0) ∧ signedMat p.1 p.2 *ᵥ v = v).image
      fun p => signedMat p.1 p.2).card ≤ 8 := by
  decide +kernel

set_option synthInstance.maxHeartbeats 1000000 in
set_option synthInstance.maxSize 100000 in
theorem mat_commute_four : ∀ v : Fin 3 → ZMod 3, v ≠ 0 →
    ∀ π : Fin 3 → Fin 3, Function.Bijective π → ∀ s : Fin 3 → ZMod 3, (∀ j, s j ≠ 0) →
      signedMat π s *ᵥ v = v → signedMat π s * signedMat π s ≠ 1 →
      signedMat π s * signedMat π s * signedMat π s * signedMat π s = 1 →
      ∀ π' : Fin 3 → Fin 3, Function.Bijective π' → ∀ s' : Fin 3 → ZMod 3, (∀ j, s' j ≠ 0) →
        signedMat π' s' *ᵥ v = v → signedMat π' s' * signedMat π' s' ≠ 1 →
        signedMat π' s' * signedMat π' s' * signedMat π' s' * signedMat π' s' = 1 →
        signedMat π s * signedMat π' s' = signedMat π' s' * signedMat π s := by
  decide +kernel

set_option synthInstance.maxHeartbeats 1000000 in
set_option synthInstance.maxSize 100000 in
theorem mat_refl_of_not_commute : ∀ v : Fin 3 → ZMod 3, v ≠ 0 →
    ∀ π : Fin 3 → Fin 3, Function.Bijective π → ∀ s : Fin 3 → ZMod 3, (∀ j, s j ≠ 0) →
      signedMat π s *ᵥ v = v → signedMat π s * signedMat π s = 1 →
      ∀ π' : Fin 3 → Fin 3, Function.Bijective π' → ∀ s' : Fin 3 → ZMod 3, (∀ j, s' j ≠ 0) →
        signedMat π' s' *ᵥ v = v → signedMat π' s' * signedMat π' s' = 1 →
        signedMat π s * signedMat π' s' ≠ signedMat π' s' * signedMat π s →
        (Finset.univ.image fun w : Fin 3 → ZMod 3 => (signedMat π s - 1) *ᵥ w).card = 3 := by
  decide +kernel

set_option synthInstance.maxHeartbeats 1000000 in
set_option synthInstance.maxSize 100000 in
theorem mat_orderFour : ∀ v : Fin 3 → ZMod 3, v ≠ 0 →
    ∀ π : Fin 3 → Fin 3, Function.Bijective π → ∀ s : Fin 3 → ZMod 3, (∀ j, s j ≠ 0) →
      signedMat π s *ᵥ v = v → signedMat π s * signedMat π s ≠ 1 →
      signedMat π s * signedMat π s * signedMat π s * signedMat π s = 1 →
      (Finset.univ.image fun w : Fin 3 → ZMod 3 => (signedMat π s - 1) *ᵥ w).card = 9 ∧
        v ∉ Finset.univ.image fun w : Fin 3 → ZMod 3 => (signedMat π s - 1) *ᵥ w := by
  decide +kernel

set_option synthInstance.maxHeartbeats 1000000 in
set_option synthInstance.maxSize 100000 in
theorem mat_fixed_orderThree : ∀ v : Fin 3 → ZMod 3, v ≠ 0 →
    ∀ π : Fin 3 → Fin 3, Function.Bijective π → ∀ s : Fin 3 → ZMod 3, (∀ j, s j ≠ 0) →
      signedMat π s *ᵥ v = v → signedMat π s * signedMat π s * signedMat π s = 1 →
      signedMat π s ≠ 1 →
      ∀ w : Fin 3 → ZMod 3, signedMat π s *ᵥ w = w → w = 0 ∨ w = v ∨ w = v + v := by
  decide +kernel

set_option synthInstance.maxHeartbeats 1000000 in
set_option synthInstance.maxSize 100000 in
theorem mat_mem_sup_commOf : ∀ v : Fin 3 → ZMod 3, v ≠ 0 →
    ∀ π : Fin 3 → Fin 3, Function.Bijective π → ∀ s : Fin 3 → ZMod 3, (∀ j, s j ≠ 0) →
      signedMat π s *ᵥ v = v → signedMat π s * signedMat π s = 1 →
      ∀ π' : Fin 3 → Fin 3, Function.Bijective π' → ∀ s' : Fin 3 → ZMod 3, (∀ j, s' j ≠ 0) →
        signedMat π' s' *ᵥ v = v → signedMat π' s' * signedMat π' s' = 1 →
        signedMat π s * signedMat π' s' ≠ signedMat π' s' * signedMat π s →
        signedMat π s * signedMat π' s' * (signedMat π s * signedMat π' s') *
          (signedMat π s * signedMat π' s') = 1 →
        ∃ w₁ w₂ : Fin 3 → ZMod 3,
          v = (signedMat π s - 1) *ᵥ w₁ + (signedMat π' s' - 1) *ᵥ w₂ := by
  decide +kernel

variable {G : Type} [Group G] {A : Subgroup G}

theorem apply_coord (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) (σ : MulAut A)
    (w : Fin 3 → ZMod 3) :
    σ (f (Multiplicative.ofAdd w)) = f (Multiplicative.ofAdd (Item2131One.matOf f σ *ᵥ w)) := by
  rw [Item2131One.matOf_apply, Item2131One.coordGL_mulVec_eq]

theorem commHom_coord (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) (σ : MulAut A)
    (w : Fin 3 → ZMod 3) :
    (f (Multiplicative.ofAdd w))⁻¹ * σ (f (Multiplicative.ofAdd w)) =
      f (Multiplicative.ofAdd ((Item2131One.matOf f σ - 1) *ᵥ w)) := by
  rw [apply_coord, ← map_inv, ← map_mul, ← ofAdd_neg, ← ofAdd_add]
  congr 2
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  abel

theorem eq_coord (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) (a : A) :
    a = f (Multiplicative.ofAdd (Multiplicative.toAdd (f.symm a))) := by
  rw [ofAdd_toAdd, MulEquiv.apply_symm_apply]

theorem coord_injective (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) {w w' : Fin 3 → ZMod 3}
    (h : f (Multiplicative.ofAdd w) = f (Multiplicative.ofAdd w')) : w = w' :=
  Multiplicative.ofAdd.injective (f.injective h)

theorem exists_signedMat (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) {σ : MulAut A}
    (hm : coordGL f σ ∈ monomial) :
    ∃ π : Fin 3 → Fin 3, Function.Bijective π ∧ ∃ s : Fin 3 → ZMod 3, (∀ j, s j ≠ 0) ∧
      Item2131One.matOf f σ = signedMat π s :=
  hm

theorem mul_eq_one_iff (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) {σ τ : MulAut A} :
    σ * τ = 1 ↔ Item2131One.matOf f σ * Item2131One.matOf f τ = 1 := by
  rw [← map_mul, ← map_one (Item2131One.matOf f)]
  exact (Item2131One.matOf_injective f).eq_iff.symm

theorem pow_four_eq_one_iff (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) {σ : MulAut A} :
    σ * σ * σ * σ = 1 ↔
      Item2131One.matOf f σ * Item2131One.matOf f σ * Item2131One.matOf f σ *
        Item2131One.matOf f σ = 1 := by
  rw [← map_mul, ← map_mul, ← map_mul, ← map_one (Item2131One.matOf f)]
  exact (Item2131One.matOf_injective f).eq_iff.symm

theorem pow_three_eq_one_iff (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) {σ : MulAut A} :
    σ * σ * σ = 1 ↔
      Item2131One.matOf f σ * Item2131One.matOf f σ * Item2131One.matOf f σ = 1 := by
  rw [← map_mul, ← map_mul, ← map_one (Item2131One.matOf f)]
  exact (Item2131One.matOf_injective f).eq_iff.symm

variable (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) {v : Fin 3 → ZMod 3}

theorem card_le_eight (hv : v ≠ 0) {S : Subgroup (MulAut A)}
    (hS : ∀ σ ∈ S, coordGL f σ ∈ monomial ∧ Item2131One.matOf f σ *ᵥ v = v) :
    Nat.card S ≤ 8 := by
  set F := (Finset.univ.filter fun p : (Fin 3 → Fin 3) × (Fin 3 → ZMod 3) =>
      Function.Bijective p.1 ∧ (∀ j, p.2 j ≠ 0) ∧ signedMat p.1 p.2 *ᵥ v = v).image
    fun p => signedMat p.1 p.2 with hF
  have hmem : ∀ σ : S, Item2131One.matOf f σ ∈ F := by
    intro σ
    obtain ⟨π, hπ, s, hs, he⟩ := exists_signedMat f (hS σ σ.2).1
    rw [hF, Finset.mem_image]
    refine ⟨(π, s), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hπ, hs, ?_⟩, he.symm⟩
    rw [← he]
    exact (hS σ σ.2).2
  have hinj : Function.Injective fun σ : S => (⟨Item2131One.matOf f σ, hmem σ⟩ : F) := by
    intro σ τ h
    exact Subtype.ext (Item2131One.matOf_injective f (congrArg Subtype.val h))
  calc Nat.card S ≤ Nat.card F := Nat.card_le_card_of_injective _ hinj
    _ = F.card := Nat.card_eq_finsetCard F
    _ ≤ 8 := card_stab_le v hv

theorem commute_of_orderOf_four (hv : v ≠ 0) {σ τ : MulAut A}
    (hσ : coordGL f σ ∈ monomial ∧ Item2131One.matOf f σ *ᵥ v = v)
    (hτ : coordGL f τ ∈ monomial ∧ Item2131One.matOf f τ *ᵥ v = v)
    (hσ2 : σ * σ ≠ 1) (hσ4 : σ * σ * σ * σ = 1) (hτ2 : τ * τ ≠ 1)
    (hτ4 : τ * τ * τ * τ = 1) : σ * τ = τ * σ := by
  obtain ⟨π, hπ, s, hs, he⟩ := exists_signedMat f hσ.1
  obtain ⟨π', hπ', s', hs', he'⟩ := exists_signedMat f hτ.1
  apply Item2131One.matOf_injective f
  rw [map_mul, map_mul, he, he']
  refine mat_commute_four v hv π hπ s hs (he ▸ hσ.2) ?_ ?_ π' hπ' s' hs' (he' ▸ hτ.2) ?_ ?_
  · intro h
    apply hσ2
    rw [mul_eq_one_iff f, he]
    exact h
  · rw [← he, ← pow_four_eq_one_iff f]
    exact hσ4
  · intro h
    apply hτ2
    rw [mul_eq_one_iff f, he']
    exact h
  · rw [← he', ← pow_four_eq_one_iff f]
    exact hτ4

theorem isReflectionOn_of_not_commute (hA : IsMulCommutative A) (hv : v ≠ 0) {σ τ : MulAut A}
    (hσ : coordGL f σ ∈ monomial ∧ Item2131One.matOf f σ *ᵥ v = v)
    (hτ : coordGL f τ ∈ monomial ∧ Item2131One.matOf f τ *ᵥ v = v)
    (hσ2 : σ * σ = 1) (hτ2 : τ * τ = 1) (hst : σ * τ ≠ τ * σ) : IsReflectionOn σ := by
  obtain ⟨π, hπ, s, hs, he⟩ := exists_signedMat f hσ.1
  obtain ⟨π', hπ', s', hs', he'⟩ := exists_signedMat f hτ.1
  have hM2 : signedMat π s * signedMat π s = 1 := by
    rw [← he, ← mul_eq_one_iff f]
    exact hσ2
  have hN2 : signedMat π' s' * signedMat π' s' = 1 := by
    rw [← he', ← mul_eq_one_iff f]
    exact hτ2
  have hMN : signedMat π s * signedMat π' s' ≠ signedMat π' s' * signedMat π s := by
    intro h
    apply hst
    apply Item2131One.matOf_injective f
    rw [map_mul, map_mul, he, he', h]
  have hcard := mat_refl_of_not_commute v hv π hπ s hs (he ▸ hσ.2) hM2 π' hπ' s' hs'
    (he' ▸ hτ.2) hN2 hMN
  rw [isReflectionOn_iff hA f, isReflection_iff]
  have hval : ((coordGL f σ : GL (Fin 3) (ZMod 3)) : Mat3) = signedMat π s := he
  rw [hval]
  refine ⟨hM2, fun h1 => hMN ?_, hcard⟩
  rw [h1, one_mul, mul_one]

theorem card_commOf_of_orderOf_four (hA : IsMulCommutative A) (hv : v ≠ 0) {σ : MulAut A}
    (hσ : coordGL f σ ∈ monomial ∧ Item2131One.matOf f σ *ᵥ v = v)
    (hσ2 : σ * σ ≠ 1) (hσ4 : σ * σ * σ * σ = 1) :
    Nat.card (commOf σ) = 9 ∧ f (Multiplicative.ofAdd v) ∉ commOf σ := by
  obtain ⟨π, hπ, s, hs, he⟩ := exists_signedMat f hσ.1
  have h := mat_orderFour v hv π hπ s hs (he ▸ hσ.2)
    (fun h => hσ2 (by rw [mul_eq_one_iff f, he]; exact h))
    (by rw [← he, ← pow_four_eq_one_iff f]; exact hσ4)
  have hval : ((coordGL f σ : GL (Fin 3) (ZMod 3)) : Mat3) = signedMat π s := he
  refine ⟨?_, fun hmem => h.2 ?_⟩
  · rw [card_commOf_eq hA f σ, card_range_eq, hval]
    exact h.1
  · obtain ⟨a, ha⟩ := (mem_commOf_iff hA σ _).mp hmem
    rw [eq_coord f a, commHom_coord, he] at ha
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, coord_injective f ha⟩

theorem mem_zpowers_of_fixed (hv : v ≠ 0) {σ : MulAut A}
    (hσ : coordGL f σ ∈ monomial ∧ Item2131One.matOf f σ *ᵥ v = v)
    (hσ3 : σ * σ * σ = 1) (hσ1 : σ ≠ 1) {a : A} (ha : σ a = a) :
    a ∈ Subgroup.zpowers (f (Multiplicative.ofAdd v)) := by
  obtain ⟨π, hπ, s, hs, he⟩ := exists_signedMat f hσ.1
  set w := Multiplicative.toAdd (f.symm a) with hw
  have hfix : signedMat π s *ᵥ w = w := by
    rw [← he]
    apply coord_injective f
    rw [← apply_coord, ← eq_coord]
    exact ha
  have hM1 : signedMat π s ≠ 1 := by
    intro h
    apply hσ1
    apply Item2131One.matOf_injective f
    rw [he, h, map_one]
  rcases mat_fixed_orderThree v hv π hπ s hs (he ▸ hσ.2)
      (by rw [← he, ← pow_three_eq_one_iff f]; exact hσ3) hM1 w hfix with h | h | h
  · rw [eq_coord f a, ← hw, h, ofAdd_zero, map_one]
    exact Subgroup.one_mem _
  · rw [eq_coord f a, ← hw, h]
    exact Subgroup.mem_zpowers _
  · rw [eq_coord f a, ← hw, h, ofAdd_add, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)

theorem mem_sup_commOf (hv : v ≠ 0) {σ τ : MulAut A}
    (hσ : coordGL f σ ∈ monomial ∧ Item2131One.matOf f σ *ᵥ v = v)
    (hτ : coordGL f τ ∈ monomial ∧ Item2131One.matOf f τ *ᵥ v = v)
    (hσ2 : σ * σ = 1) (hτ2 : τ * τ = 1) (hst : σ * τ ≠ τ * σ)
    (h3 : σ * τ * (σ * τ) * (σ * τ) = 1) :
    f (Multiplicative.ofAdd v) ∈ commOf σ ⊔ commOf τ := by
  obtain ⟨π, hπ, s, hs, he⟩ := exists_signedMat f hσ.1
  obtain ⟨π', hπ', s', hs', he'⟩ := exists_signedMat f hτ.1
  have hMN : signedMat π s * signedMat π' s' ≠ signedMat π' s' * signedMat π s := by
    intro h
    apply hst
    apply Item2131One.matOf_injective f
    rw [map_mul, map_mul, he, he', h]
  have h3' : signedMat π s * signedMat π' s' * (signedMat π s * signedMat π' s') *
      (signedMat π s * signedMat π' s') = 1 := by
    rw [← he, ← he', ← map_mul, ← map_mul, ← map_mul, h3, map_one]
  obtain ⟨w₁, w₂, hw⟩ := mat_mem_sup_commOf v hv π hπ s hs (he ▸ hσ.2)
    (by rw [← he, ← mul_eq_one_iff f]; exact hσ2) π' hπ' s' hs' (he' ▸ hτ.2)
    (by rw [← he', ← mul_eq_one_iff f]; exact hτ2) hMN h3'
  rw [hw, ofAdd_add, map_mul, ← he, ← he', ← commHom_coord, ← commHom_coord]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (mem_commOf σ _))
    (Subgroup.mem_sup_right (mem_commOf τ _))

end CFSG.RankThree.PartTwo.Sec21.Item222Proof
