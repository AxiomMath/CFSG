module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TypeOne

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch1413

open CFSG.Open CFSG.ComponentClassification.CatFactsSp4 CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial SymplecticHigher SymplecticFlag Subgroup

variable {K : Type} [Field K]

private theorem a1413SpEndLift_two_ne_zero [Finite K] (hodd : Odd (Nat.card K)) :
    (2 : K) ≠ 0 := by
  let : Fintype K := Fintype.ofFinite K
  have hm : Fintype.card K % 2 = 1 :=
    Nat.odd_iff.mp (by simpa only [Nat.card_eq_fintype_card] using hodd)
  apply Ring.two_ne_zero
  intro hc
  have he := FiniteField.even_card_of_char_two hc
  omega

private theorem a1413SpEndLift_involution_type (h2 : (2 : K) ≠ 0)
    {a : StatedProj (StatedSp 2 K)} (haX : a ∈ X0 K) (ha2 : a * a = 1) :
    (∃ g h : Matrix.SpecialLinearGroup (Fin 2) K,
        g * g = 1 ∧ h * h = 1 ∧ a = proj 2 K (blkSL K (g, h))) ∨
      (∃ g h : Matrix.SpecialLinearGroup (Fin 2) K,
        g * g = negOneSL ∧ h * h = negOneSL ∧ a = proj 2 K (blkSL K (g, h))) := by
  obtain ⟨⟨g, h⟩, rfl⟩ := (mem_X0 h2).mp haX
  have hsq : proj 2 K (blkSL K (g * g, h * h)) = 1 := by
    rw [show (g * g, h * h) = (g, h) * (g, h) from rfl, map_mul, map_mul, ha2]
  have hmem : blkSL K (g * g, h * h) ∈ spScalars 2 K := by
    rw [← ker_proj, MonoidHom.mem_ker]
    exact hsq
  rw [mem_spScalars_iff, coe_blkSL] at hmem
  rcases hmem with h1 | h1
  · left
    have hb := blk_injective _ _ _ _ (h1.trans blk_one_one.symm)
    exact ⟨g, h, Subtype.ext hb.1, Subtype.ext hb.2, rfl⟩
  · right
    have hb := blk_injective _ _ _ _ (h1.trans blk_neg_one_neg_one.symm)
    exact ⟨g, h, Subtype.ext hb.1, Subtype.ext hb.2, rfl⟩

private theorem a1413SpEndLift_quaternion_lift (h2 : (2 : K) ≠ 0)
    {a : StatedProj (StatedSp 2 K)} (haX : a ∈ X0 K) (ha2 : a * a = 1)
    (ha1 : a ≠ 1) (hau : a ≠ u1 K) :
    ∃ g h : Matrix.SpecialLinearGroup (Fin 2) K,
      g * g = negOneSL ∧ h * h = negOneSL ∧ a = proj 2 K (blkSL K (g, h)) := by
  rcases a1413SpEndLift_involution_type h2 haX ha2 with ⟨g, h, hg, hh, haeq⟩ | hres
  · exfalso
    have hg' : (g : Matrix (Fin 2) (Fin 2) K) * g = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, hg, Matrix.SpecialLinearGroup.coe_one]
    have hh' : (h : Matrix (Fin 2) (Fin 2) K) * h = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, hh, Matrix.SpecialLinearGroup.coe_one]
    have ha : a = 1 ∨ a = u1 K := by
      rcases eq_one_or_neg_one_of_sq h2 g.2 hg' with hg1 | hg1 <;>
        rcases eq_one_or_neg_one_of_sq h2 h.2 hh' with hh1 | hh1
      · left
        rw [haeq, show g = 1 from Subtype.ext hg1, show h = 1 from Subtype.ext hh1,
          show ((1 : Matrix.SpecialLinearGroup (Fin 2) K),
            (1 : Matrix.SpecialLinearGroup (Fin 2) K)) = 1 from rfl, map_one, map_one]
      · right
        rw [haeq, show g = 1 from Subtype.ext hg1, show h = negOneSL from Subtype.ext hh1]
        exact u1_eq_proj_blkSL.symm
      · right
        rw [haeq, show g = negOneSL from Subtype.ext hg1, show h = 1 from Subtype.ext hh1]
        exact u1_eq_proj_blkSL'.symm
      · left
        rw [haeq, show g = negOneSL from Subtype.ext hg1,
          show h = negOneSL from Subtype.ext hh1]
        exact proj_blkSL_negOne_one
    rcases ha with h | h
    · exact ha1 h
    · exact hau h
  · exact hres

private theorem a1413SpEndLift_anticomm {g h : Matrix.SpecialLinearGroup (Fin 2) K}
    (hg : g * g = negOneSL) (hh : h * h = negOneSL)
    (hgh : (g * h) * (g * h) = negOneSL) :
    g * h = negOneSL * (h * g) := by
  have hneg : (negOneSL : Matrix.SpecialLinearGroup (Fin 2) K) * negOneSL = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_negOneSL]
    simp
  have hcen : ∀ x : Matrix.SpecialLinearGroup (Fin 2) K, negOneSL * x = x * negOneSL := by
    intro x
    apply Subtype.ext
    rw [coe_negOneSL_mul, Matrix.SpecialLinearGroup.coe_mul, coe_negOneSL, Matrix.mul_neg,
      Matrix.mul_one]
  have hginv : g⁻¹ = negOneSL * g := by
    have h1 : g * (negOneSL * g) = 1 := by
      rw [← mul_assoc, ← hcen g, mul_assoc, hg, hneg]
    exact inv_eq_of_mul_eq_one_right h1
  have hghg : g * h * g = h := by
    have h1 : (g * h) * (g * h) = h * h := by rw [hgh, hh]
    have h2 : g * h * g * h = h * h := by
      rwa [show g * h * g * h = (g * h) * (g * h) from by group]
    exact mul_right_cancel h2
  calc g * h = g * h * g * g⁻¹ := by group
    _ = h * g⁻¹ := by rw [hghg]
    _ = h * (negOneSL * g) := by rw [hginv]
    _ = negOneSL * (h * g) := by rw [← mul_assoc, ← hcen h, mul_assoc]

private theorem a1413SpEndLift_sq_mul_of_proj_eq
    {x₁ x₂ k₁ k₂ : Matrix.SpecialLinearGroup (Fin 2) K}
    (hk1 : k₁ * k₁ = negOneSL) (hk2 : k₂ * k₂ = negOneSL)
    (h : proj 2 K (blkSL K (x₁, x₂)) = proj 2 K (blkSL K (k₁, k₂))) :
    x₁ * x₁ = negOneSL ∧ x₂ * x₂ = negOneSL := by
  rcases eq_or_eq_neg_of_proj_eq h with hh | hh
  · rw [coe_blkSL, coe_blkSL] at hh
    have hb := blk_injective _ _ _ _ hh
    have hb1 : (↑k₁ : Matrix (Fin 2) (Fin 2) K) = ↑x₁ := by simpa using hb.1
    have hb2 : (↑k₂ : Matrix (Fin 2) (Fin 2) K) = ↑x₂ := by simpa using hb.2
    exact ⟨by rw [← hk1, ← Subtype.ext hb1], by rw [← hk2, ← Subtype.ext hb2]⟩
  · rw [coe_blkSL, coe_blkSL, blk_neg] at hh
    have hb := blk_injective _ _ _ _ hh
    constructor
    · apply Subtype.ext
      have hx : (↑x₁ : Matrix (Fin 2) (Fin 2) K) = -↑k₁ := by rw [hb.1, neg_neg]
      rw [Matrix.SpecialLinearGroup.coe_mul, hx, neg_mul_neg,
        ← Matrix.SpecialLinearGroup.coe_mul, hk1]
    · apply Subtype.ext
      have hx : (↑x₂ : Matrix (Fin 2) (Fin 2) K) = -↑k₂ := by rw [hb.2, neg_neg]
      rw [Matrix.SpecialLinearGroup.coe_mul, hx, neg_mul_neg,
        ← Matrix.SpecialLinearGroup.coe_mul, hk2]

private theorem a1413SpEndLift_mem_four {G : Type*} [Group G] {A : Subgroup G} [Finite G]
    (hA : IsElemAbelian 2 A) (h4 : Nat.card A = 4) {a b x : G}
    (ha : a ∈ A) (hb : b ∈ A) (hx : x ∈ A) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) :
    x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  classical
  have hsq : ∀ y ∈ A, y * y = 1 := fun y hy => by rw [← pow_two]; exact hA.2 y hy
  have hab1 : a * b ≠ 1 := fun h => hab (by
    have := hsq a ha
    calc a = a * (a * b) := by rw [h, mul_one]
      _ = b := by rw [← mul_assoc, this, one_mul])
  have haba : a * b ≠ a := fun h => hb1 (by simpa using h)
  have habb : a * b ≠ b := fun h => ha1 (by simpa using h)
  by_contra hne
  simp only [not_or] at hne
  obtain ⟨hx1, hxa, hxb, hxab⟩ := hne
  have hsub : (({1, a, b, a * b, x} : Finset G) : Set G) ⊆ A := by
    intro y hy
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact A.one_mem
    · exact ha
    · exact hb
    · exact A.mul_mem ha hb
    · exact hx
  have hcard : ({1, a, b, a * b, x} : Finset G).card = 5 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using Ne.symm hxab
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm habb, Ne.symm hxb⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hab, Ne.symm haba, Ne.symm hxa⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm ha1, Ne.symm hb1, Ne.symm hab1, Ne.symm hx1⟩
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, hcard, ← Nat.card_coe_set_eq] at hle
  change 5 ≤ Nat.card A at hle
  omega

theorem sp4_four_group_lifts {K : Type} [Field K] [Finite K] (hodd : Odd (Nat.card K))
    {A : Subgroup (StatedProj (StatedSp 2 K))} (hA : Nat.card A = 4) (hAe : IsElemAbelian 2 A)
    (hAX : A ≤ X0 K) (hu : u1 K ∉ A) :
    ∃ g₁ g₂ h₁ h₂ : Matrix.SpecialLinearGroup (Fin 2) K,
      g₁ * g₁ = negOneSL ∧ g₂ * g₂ = negOneSL ∧ h₁ * h₁ = negOneSL ∧ h₂ * h₂ = negOneSL ∧
      g₁ * h₁ = negOneSL * (h₁ * g₁) ∧ g₂ * h₂ = negOneSL * (h₂ * g₂) ∧
      A = Subgroup.closure {proj 2 K (blkSL K (g₁, g₂)), proj 2 K (blkSL K (h₁, h₂))} := by
  classical
  have h2 := a1413SpEndLift_two_ne_zero (K := K) hodd
  haveI : Fintype A := Fintype.ofFinite A
  obtain ⟨a, ha1⟩ : ∃ a : A, a ≠ 1 := by
    by_contra h
    rw [not_exists] at h
    have h' : ∀ x : A, x = 1 := fun x => not_not.mp (h x)
    have : Fintype.card A ≤ 1 := by
      rw [← Finset.card_univ]
      exact Finset.card_le_one.mpr (fun x _ y _ => by rw [h' x, h' y])
    have := hA
    rw [Nat.card_eq_fintype_card] at this
    omega
  obtain ⟨b, hb1, hba⟩ : ∃ b : A, b ≠ 1 ∧ b ≠ a := by
    by_contra h
    rw [not_exists] at h
    have h' : ∀ x : A, x = 1 ∨ x = a := by
      intro x
      by_cases hx : x = 1
      · exact Or.inl hx
      · exact Or.inr (by
          by_contra hxa
          exact h x ⟨hx, hxa⟩)
    have hsub : (Finset.univ : Finset A) ⊆ ({(1 : A), a} : Finset A) := by
      intro x _
      rcases h' x with hx | hx
      · simp [hx]
      · simp [hx]
    have hcard : Fintype.card A ≤ 2 := by
      rw [← Finset.card_univ]
      calc (Finset.univ : Finset A).card ≤ ({(1 : A), a} : Finset A).card :=
            Finset.card_le_card hsub
        _ ≤ 2 := Finset.card_le_two
    have := hA
    rw [Nat.card_eq_fintype_card] at this
    omega
  have haX : (a : StatedProj (StatedSp 2 K)) ∈ X0 K := hAX a.2
  have hbX : (b : StatedProj (StatedSp 2 K)) ∈ X0 K := hAX b.2
  have ha2 : (a : StatedProj (StatedSp 2 K)) * a = 1 := by
    have := hAe.2 a.1 a.2
    rwa [pow_two] at this
  have hb2 : (b : StatedProj (StatedSp 2 K)) * b = 1 := by
    have := hAe.2 b.1 b.2
    rwa [pow_two] at this
  have ha_ne_one : (a : StatedProj (StatedSp 2 K)) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hb_ne_one : (b : StatedProj (StatedSp 2 K)) ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hau : (a : StatedProj (StatedSp 2 K)) ≠ u1 K := fun h => hu (h ▸ a.2)
  have hbu : (b : StatedProj (StatedSp 2 K)) ≠ u1 K := fun h => hu (h ▸ b.2)
  obtain ⟨g₁, g₂, hg1, hg2, haeq⟩ :=
    a1413SpEndLift_quaternion_lift h2 haX ha2 ha_ne_one hau
  obtain ⟨h₁, h₂, hh1, hh2, hbeq⟩ :=
    a1413SpEndLift_quaternion_lift h2 hbX hb2 hb_ne_one hbu
  have hab_mem : (a : StatedProj (StatedSp 2 K)) * b ∈ A := A.mul_mem a.2 b.2
  have habX : (a : StatedProj (StatedSp 2 K)) * b ∈ X0 K := hAX hab_mem
  have hcomm : (b : StatedProj (StatedSp 2 K)) * a = a * b := by
    simpa using congrArg Subtype.val (hAe.1.is_comm.comm b a)
  have hab2 : ((a : StatedProj (StatedSp 2 K)) * b) * (a * b) = 1 := by
    have h1 : ((a : StatedProj (StatedSp 2 K)) * b) * (a * b) =
        ((a : StatedProj (StatedSp 2 K)) * a) * (b * b) := by
      rw [mul_assoc, ← mul_assoc (b : StatedProj (StatedSp 2 K)), hcomm, mul_assoc, ← mul_assoc]
    rw [h1, ha2, hb2, one_mul]
  have hab_ne_one : (a : StatedProj (StatedSp 2 K)) * b ≠ 1 := by
    intro h
    have hb_eq : (b : StatedProj (StatedSp 2 K)) = a := by
      have h1 : (a : StatedProj (StatedSp 2 K))⁻¹ * ((a : StatedProj (StatedSp 2 K)) * b) =
          (a : StatedProj (StatedSp 2 K))⁻¹ * 1 := by rw [h]
      rw [← mul_assoc, inv_mul_cancel, one_mul, mul_one] at h1
      rw [h1, inv_eq_of_mul_eq_one_right ha2]
    exact hba (Subtype.ext hb_eq)
  have habu : (a : StatedProj (StatedSp 2 K)) * b ≠ u1 K := fun h => hu (h ▸ hab_mem)
  obtain ⟨k₁, k₂, hk1, hk2, habeq⟩ :=
    a1413SpEndLift_quaternion_lift h2 habX hab2 hab_ne_one habu
  have hprod : proj 2 K (blkSL K (g₁ * h₁, g₂ * h₂)) = proj 2 K (blkSL K (k₁, k₂)) := by
    rw [show (g₁ * h₁, g₂ * h₂) = (g₁, g₂) * (h₁, h₂) from rfl, map_mul, map_mul,
      ← haeq, ← hbeq, ← habeq]
  obtain ⟨hgh1, hgh2⟩ := a1413SpEndLift_sq_mul_of_proj_eq hk1 hk2 hprod
  have hanti1 := a1413SpEndLift_anticomm hg1 hh1 hgh1
  have hanti2 := a1413SpEndLift_anticomm hg2 hh2 hgh2
  have hab : (a : StatedProj (StatedSp 2 K)) ≠ b := fun h => hba (Subtype.ext h.symm)
  have hAle : A ≤ Subgroup.closure ({(a : StatedProj (StatedSp 2 K)),
    (b : StatedProj (StatedSp 2 K))} : Set _) := by
    intro x hx
    rcases a1413SpEndLift_mem_four hAe hA a.2 b.2 hx ha_ne_one hb_ne_one hab with
      h | h | h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.subset_closure (by simp)
    · rw [h]; exact Subgroup.subset_closure (by simp)
    · rw [h]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
  have hclosure_le : Subgroup.closure ({(a : StatedProj (StatedSp 2 K)),
    (b : StatedProj (StatedSp 2 K))} : Set _) ≤ A := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact a.2
    · exact b.2
  have hAeq : A = Subgroup.closure ({(a : StatedProj (StatedSp 2 K)),
    (b : StatedProj (StatedSp 2 K))} : Set _) :=
    le_antisymm hAle hclosure_le
  refine ⟨g₁, g₂, h₁, h₂, hg1, hg2, hh1, hh2, hanti1, hanti2, ?_⟩
  rw [← haeq, ← hbeq]
  exact hAeq

end CFSG.LocalAnalysis.WeakClosure81.Asch1413

end
