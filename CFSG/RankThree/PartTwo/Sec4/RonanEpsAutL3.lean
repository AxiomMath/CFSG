module

public import CFSG.RankThree.PartTwo.Sec4.RonanEpsCube

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanEps

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag Matrix

theorem eq_or_mul_eq_one_of_orderOf_eq_three {K : Type*} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) {φ ψ : K ≃+* K} (hφ : orderOf φ = 3)
    (hψ : orderOf ψ = 3) : ψ = φ ∨ ψ * φ = 1 := by
  obtain ⟨h3, hφ'⟩ := eq_frobenius_pow_of_orderOf_eq_three hp hf hK hφ
  obtain ⟨-, hψ'⟩ := eq_frobenius_pow_of_orderOf_eq_three hp hf hK hψ
  obtain ⟨g, rfl⟩ := h3
  have hg1 : 3 * g / 3 = g := by omega
  have hg2 : 2 * (3 * g) / 3 = 2 * g := by omega
  rw [hg1, hg2] at hφ' hψ'
  have hcard : ∀ x : K, x ^ p ^ (3 * g) = x := by
    intro x
    classical
    have := Fintype.ofFinite K
    have h := FiniteField.pow_card x
    rwa [← Nat.card_eq_fintype_card, hK] at h
  have hsum : ∀ x : K, (x ^ p ^ g) ^ p ^ (2 * g) = x := by
    intro x
    rw [← pow_mul, ← pow_add, show g + 2 * g = 3 * g by ring, hcard]
  have hsum' : ∀ x : K, (x ^ p ^ (2 * g)) ^ p ^ g = x := by
    intro x
    rw [← pow_mul, ← pow_add, show 2 * g + g = 3 * g by ring, hcard]
  rcases hφ' with hφ' | hφ' <;> rcases hψ' with hψ' | hψ'
  · exact Or.inl (RingEquiv.ext fun x => by rw [hφ', hψ'])
  · exact Or.inr (RingEquiv.ext fun x => by
      rw [RingAut.mul_apply, RingAut.one_apply, hφ', hψ', hsum])
  · exact Or.inr (RingEquiv.ext fun x => by
      rw [RingAut.mul_apply, RingAut.one_apply, hφ', hψ', hsum'])
  · exact Or.inl (RingEquiv.ext fun x => by rw [hφ', hψ'])

theorem card_le_three_mul_of_cosets {M : Type*} [Group M] {A D : Subgroup M} [Finite A]
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {α : M} (hα : α ∈ A)
    (hcov : ∀ β ∈ A, β ∈ D ∨ β * α⁻¹ ∈ D ∨ β * α ∈ D) :
    Nat.card A ≤ 3 * Nat.card (A ⊓ D : Subgroup M) := by
  set B : Subgroup A := D.subgroupOf A with hB
  have hcardB : Nat.card B = Nat.card (A ⊓ D : Subgroup M) := by
    rw [hB, ← Subgroup.inf_subgroupOf_left, inf_comm]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  set a : A := ⟨α, hα⟩ with ha
  have hsurj : Function.Surjective (fun i : Fin 3 =>
      ((![1, a, a⁻¹] : Fin 3 → A) i : A ⧸ B)) := by
    intro x
    obtain ⟨⟨β, hβ⟩, rfl⟩ := QuotientGroup.mk_surjective x
    rcases hcov β hβ with h | h | h
    · refine ⟨0, ?_⟩
      simp only [Matrix.cons_val_zero]
      rw [QuotientGroup.eq]
      change ((1 : A)⁻¹ * ⟨β, hβ⟩ : A) ∈ B
      rw [hB, Subgroup.mem_subgroupOf]
      simpa using h
    · refine ⟨1, ?_⟩
      simp only [Matrix.cons_val_one, Matrix.head_cons]
      rw [QuotientGroup.eq]
      rw [hB, Subgroup.mem_subgroupOf]
      change α⁻¹ * β ∈ D
      have : α⁻¹ * β = (β * α⁻¹) := by
        have hc := hcomm β hβ α⁻¹ (inv_mem hα)
        rw [hc]
      rw [this]
      exact h
    · refine ⟨2, ?_⟩
      simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      rw [QuotientGroup.eq]
      rw [hB, Subgroup.mem_subgroupOf]
      change (α⁻¹)⁻¹ * β ∈ D
      rw [inv_inv, show α * β = β * α from (hcomm β hβ α hα).symm]
      exact h
  have h3 : Nat.card (A ⧸ B) ≤ 3 := by
    have := Nat.card_le_card_of_surjective _ hsurj
    simpa using this
  rw [B.card_eq_card_quotient_mul_card_subgroup, hcardB]
  exact Nat.mul_le_mul_right _ h3

theorem autNoE27_projectiveSL_three_of_mod_two {F : Type} [Field F] [Finite F] {p f : ℕ}
    (hp : p.Prime) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f) (hq : p ^ f % 3 = 2) :
    AutNoE27 (projectiveSL 3 F) := by
  intro A hA
  set L := linearAutGroup 3 F with hL
  have hF' : Nat.card F % 3 = 2 := by rw [hF]; exact hq
  obtain ⟨φ₀⟩ := nonempty_projSL_mulEquiv 3 F
  have hcyc : ∀ Q : Sylow 3 (projectiveSL 3 F), IsCyclic Q :=
    isCyclic_sylow_three_of_mulEquiv_projSL hF' φ₀.symm
  have hZ := CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (k := F) (n := 3) le_rfl
  have hB : Nat.card (A ⊓ L : Subgroup _) ≤ 3 :=
    card_le_three_of_le_inn hcyc hZ (fun α hα => mem_range_conj_of_mem_linearAutGroup hF' hα.2)
      (fun α hα => hA.1.2 α hα.1)
  have hA3 : ∀ α ∈ A, α ^ 3 = 1 := hA.1.2
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hfc : ∀ (σ : F ≃+* F) (X : GL (Fin 3) F),
      fieldAut 3 F σ * conjAut 3 F X * (fieldAut 3 F σ)⁻¹ ∈ L := by
    intro σ X
    rw [fieldAut_mul_conjAut, mul_inv_cancel_right]
    exact conjAut_mem_linearAutGroup _
  by_cases hAL : A ≤ L
  · have : Nat.card A ≤ 3 := by
      rw [show A = A ⊓ L from (inf_eq_left.mpr hAL).symm]
      exact hB
    rw [hA.2] at this
    omega
  · obtain ⟨α, hαA, hαL⟩ := Set.not_subset.mp hAL
    obtain ⟨φ, hφ, H, rfl⟩ := linear_order_three_field_descent le_rfl α (hA3 _ hαA) hαL
    have hcov : ∀ β ∈ A, β ∈ L ∨ β * (conjAut 3 F H * fieldAut 3 F φ * (conjAut 3 F H)⁻¹)⁻¹ ∈ L ∨
        β * (conjAut 3 F H * fieldAut 3 F φ * (conjAut 3 F H)⁻¹) ∈ L := by
      intro β hβ
      by_cases hβL : β ∈ L
      · exact Or.inl hβL
      right
      obtain ⟨ψ, hψ, H', rfl⟩ := linear_order_three_field_descent le_rfl β (hA3 _ hβ) hβL
      rcases eq_or_mul_eq_one_of_orderOf_eq_three hp hf hF hφ hψ with rfl | hψφ
      · left
        have : conjAut 3 F H' * fieldAut 3 F ψ * (conjAut 3 F H')⁻¹ *
            (conjAut 3 F H * fieldAut 3 F ψ * (conjAut 3 F H)⁻¹)⁻¹ =
            conjAut 3 F H' * (fieldAut 3 F ψ * conjAut 3 F (H'⁻¹ * H) * (fieldAut 3 F ψ)⁻¹) *
              (conjAut 3 F H)⁻¹ := by
          rw [map_mul, map_inv]
          group
        rw [this]
        exact mul_mem (mul_mem (conjAut_mem_linearAutGroup _) (hfc _ _))
          (inv_mem (conjAut_mem_linearAutGroup _))
      · right
        have : conjAut 3 F H' * fieldAut 3 F ψ * (conjAut 3 F H')⁻¹ *
            (conjAut 3 F H * fieldAut 3 F φ * (conjAut 3 F H)⁻¹) =
            conjAut 3 F H' * (fieldAut 3 F ψ * conjAut 3 F (H'⁻¹ * H) * (fieldAut 3 F ψ)⁻¹) *
              (fieldAut 3 F ψ * fieldAut 3 F φ) * (conjAut 3 F H)⁻¹ := by
          rw [map_mul, map_inv]
          group
        have hone : fieldAut 3 F ψ * fieldAut 3 F φ = 1 := by rw [← map_mul, hψφ, map_one]
        rw [this, hone, mul_one]
        exact mul_mem (mul_mem (conjAut_mem_linearAutGroup _) (hfc _ _))
          (inv_mem (conjAut_mem_linearAutGroup _))
    have h9 := card_le_three_mul_of_cosets hcomm hαA hcov
    rw [hA.2] at h9
    omega

theorem autNoE27_unitaryPSU_three_of_mod_one {p f : ℕ} [Fact p.Prime]
    (h : UnitaryFieldData p f (GaloisField p (2 * f))) (hq : p ^ f % 3 = 1) (hq2 : 2 < p ^ f) :
    AutNoE27 (unitaryPSU h 3) := by
  intro A hA
  set L := (psuConj h).range with hL
  have hKcard : Nat.card (GaloisField p (2 * f)) = p ^ (2 * f) := h.card
  obtain ⟨φ₀⟩ := nonempty_unitaryPSU_mulEquiv_projSU h
  have hcyc : ∀ Q : Sylow 3 (unitaryPSU h 3), IsCyclic Q :=
    isCyclic_sylow_three_of_mulEquiv_projSU (by have := h.one_le; omega) hq φ₀
  have hZ := center_unitaryPSU_three_eq_bot h hq2
  have hB : Nat.card (A ⊓ L : Subgroup _) ≤ 3 :=
    card_le_three_of_le_inn hcyc hZ (fun α hα => mem_range_conj_of_mem_psuConj_range hq hα.2)
      (fun α hα => hA.1.2 α hα.1)
  have hA3 : ∀ α ∈ A, α ^ 3 = 1 := hA.1.2
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hfc : ∀ (σ : GaloisField p (2 * f) ≃+* GaloisField p (2 * f)) (X : unitaryIsom3 h),
      psuField h σ * psuConj h X * (psuField h σ)⁻¹ ∈ L := by
    intro σ X
    rw [psuField_mul_psuConj_mul_inv]
    exact ⟨_, rfl⟩
  have hf2 : 1 ≤ 2 * f := by have := h.one_le; omega
  by_cases hAL : A ≤ L
  · have : Nat.card A ≤ 3 := by
      rw [show A = A ⊓ L from (inf_eq_left.mpr hAL).symm]
      exact hB
    rw [hA.2] at this
    omega
  · obtain ⟨α, hαA, hαL⟩ := Set.not_subset.mp hAL
    obtain ⟨φ, hφ, H, rfl⟩ := unitary_order_three_field_descent hq2 α (hA3 _ hαA) hαL
    have hcov : ∀ β ∈ A, β ∈ L ∨ β * (psuConj h H * psuField h φ * (psuConj h H)⁻¹)⁻¹ ∈ L ∨
        β * (psuConj h H * psuField h φ * (psuConj h H)⁻¹) ∈ L := by
      intro β hβ
      by_cases hβL : β ∈ L
      · exact Or.inl hβL
      right
      obtain ⟨ψ, hψ, H', rfl⟩ := unitary_order_three_field_descent hq2 β (hA3 _ hβ) hβL
      rcases eq_or_mul_eq_one_of_orderOf_eq_three (Fact.out : p.Prime) hf2 hKcard hφ hψ with
        rfl | hψφ
      · left
        have : psuConj h H' * psuField h ψ * (psuConj h H')⁻¹ *
            (psuConj h H * psuField h ψ * (psuConj h H)⁻¹)⁻¹ =
            psuConj h H' * (psuField h ψ * psuConj h (H'⁻¹ * H) * (psuField h ψ)⁻¹) *
              (psuConj h H)⁻¹ := by
          rw [map_mul, map_inv]
          group
        rw [this]
        exact mul_mem (mul_mem ⟨_, rfl⟩ (hfc _ _)) (inv_mem ⟨_, rfl⟩)
      · right
        have : psuConj h H' * psuField h ψ * (psuConj h H')⁻¹ *
            (psuConj h H * psuField h φ * (psuConj h H)⁻¹) =
            psuConj h H' * (psuField h ψ * psuConj h (H'⁻¹ * H) * (psuField h ψ)⁻¹) *
              (psuField h ψ * psuField h φ) * (psuConj h H)⁻¹ := by
          rw [map_mul, map_inv]
          group
        have hone : psuField h ψ * psuField h φ = 1 := by rw [← map_mul, hψφ, map_one]
        rw [this, hone, mul_one]
        exact mul_mem (mul_mem ⟨_, rfl⟩ (hfc _ _)) (inv_mem ⟨_, rfl⟩)
    have h9 := card_le_three_mul_of_cosets hcomm hαA hcov
    rw [hA.2] at h9
    omega

end CFSG.RankThree.PartTwo.Sec4.RonanEps
