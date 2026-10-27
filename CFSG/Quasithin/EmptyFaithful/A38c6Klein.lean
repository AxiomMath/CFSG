module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.Quasithin.A38c6

private lemma klein_card_of_index {Q : Type*} [Group Q] (hQ : Nat.card Q = 8) {A : Subgroup Q}
    (hA : A.index = 2) : Nat.card A = 4 := by
  have h := Subgroup.card_mul_index A
  rw [hA, hQ] at h
  omega

private lemma klein_card_inf_le {Q : Type*} [Group Q] [Finite Q] {A B : Subgroup Q}
    (hA : Nat.card A = 4) (hB : Nat.card B = 4) (hAB : A ≠ B) : Nat.card ↥(A ⊓ B) ≤ 2 := by
  have hd := Subgroup.card_dvd_of_le (inf_le_left : A ⊓ B ≤ A)
  rw [hA] at hd
  have hle : Nat.card ↥(A ⊓ B) ≤ 4 := Nat.le_of_dvd (by decide) hd
  by_contra hcon
  have h4 : Nat.card ↥(A ⊓ B) = 4 := by
    rcases (by omega : Nat.card ↥(A ⊓ B) = 3 ∨ Nat.card ↥(A ⊓ B) = 4) with h | h
    · rw [h] at hd
      omega
    · exact h
  apply hAB
  have h1 : A ⊓ B = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
  have h2 : A ⊓ B = B := Subgroup.eq_of_le_of_card_ge inf_le_right (by omega)
  rw [← h1, h2]

private lemma klein_sq_eq_one {Q : Type*} [Group Q] [Finite Q] (hQ : Nat.card Q = 8)
    {A B C : Subgroup Q} (hA : A.index = 2) (hB : B.index = 2) (hC : C.index = 2)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (sA : ∀ x ∈ A, x * x = 1) (sB : ∀ x ∈ B, x * x = 1) (sC : ∀ x ∈ C, x * x = 1) (z : Q) :
    z * z = 1 := by
  have cA := klein_card_of_index hQ hA
  have cB := klein_card_of_index hQ hB
  have cC := klein_card_of_index hQ hC
  have hinf := klein_card_inf_le cA cB hAB
  obtain ⟨c, hcC, hcA, hcB⟩ : ∃ c ∈ C, c ∉ A ∧ c ∉ B := by
    by_contra hcon
    push Not at hcon
    have hCA : ¬ C ≤ A := fun h => hAC (Subgroup.eq_of_le_of_card_ge h (by omega)).symm
    have hCB : ¬ C ≤ B := fun h => hBC (Subgroup.eq_of_le_of_card_ge h (by omega)).symm
    obtain ⟨x, hxC, hxA⟩ := Set.not_subset.1 hCA
    obtain ⟨y, hyC, hyB⟩ := Set.not_subset.1 hCB
    have hxB : x ∈ B := hcon x hxC hxA
    have hyA : y ∈ A := by
      by_contra h
      exact hyB (hcon y hyC h)
    by_cases h : x * y ∈ A
    · exact hxA (by simpa using A.mul_mem h (A.inv_mem hyA))
    · exact hyB (by simpa using B.mul_mem (B.inv_mem hxB) (hcon _ (C.mul_mem hxC hyC) h))
  have hAs : (A : Set Q).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact cA
  have hBs : (B : Set Q).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact cB
  have hABs : ((A : Set Q) ∩ B).ncard ≤ 2 := by
    rw [← Subgroup.coe_inf, ← Nat.card_coe_set_eq]
    exact hinf
  have hU := Set.ncard_union_add_ncard_inter (A : Set Q) (B : Set Q)
  have hV : (insert c ((A : Set Q) ∪ B)).ncard = ((A : Set Q) ∪ B).ncard + 1 :=
    Set.ncard_insert_of_notMem (by simp [hcA, hcB])
  by_contra hz
  have hzi : z⁻¹ * z⁻¹ ≠ 1 := by
    intro h
    apply hz
    rw [← mul_inv_rev, inv_eq_one] at h
    exact h
  have hne : z ≠ z⁻¹ := fun h => hz ((congrArg (z * ·) h).trans (mul_inv_cancel z))
  have hsub : insert c ((A : Set Q) ∪ B) ⊆ ({z, z⁻¹} : Set Q)ᶜ := by
    intro x hx hx'
    have hx1 : x * x = 1 := by
      simp only [Set.mem_insert_iff, Set.mem_union, SetLike.mem_coe] at hx
      rcases hx with h | h | h
      · rw [h]
        exact sC c hcC
      · exact sA x h
      · exact sB x h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx'
    rcases hx' with h | h
    · rw [h] at hx1
      exact hz hx1
    · rw [h] at hx1
      exact hzi hx1
  have h1 := Set.ncard_le_ncard hsub
  rw [Set.ncard_compl, Set.ncard_pair hne, hQ] at h1
  omega

private lemma klein_ker_le {G : Type*} [Group G] {S P M : Subgroup G}
    [(P.subgroupOf S).Normal] (hPM : P ≤ M) :
    (QuotientGroup.mk' (P.subgroupOf S)).ker ≤ M.subgroupOf S := by
  rw [QuotientGroup.ker_mk']
  intro x hx
  exact Subgroup.mem_subgroupOf.2 (hPM (Subgroup.mem_subgroupOf.1 hx))

private lemma klein_image_index {G : Type*} [Group G] {S P M : Subgroup G}
    [(P.subgroupOf S).Normal] (hPM : P ≤ M) (hi : M.relIndex S = 2) :
    ((M.subgroupOf S).map (QuotientGroup.mk' (P.subgroupOf S))).index = 2 := by
  rw [Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _) (klein_ker_le hPM)]
  exact hi

private lemma klein_image_sq {G : Type*} [Group G] {S P M : Subgroup G}
    [(P.subgroupOf S).Normal] (hs : ∀ x ∈ M, x * x ∈ P) :
    ∀ x ∈ (M.subgroupOf S).map (QuotientGroup.mk' (P.subgroupOf S)), x * x = 1 := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  rw [← map_mul]
  exact (QuotientGroup.eq_one_iff (y * y)).2
    (Subgroup.mem_subgroupOf.2 (hs _ (Subgroup.mem_subgroupOf.1 hy)))

private lemma klein_image_ne {G : Type*} [Group G] {S P M M' : Subgroup G}
    [(P.subgroupOf S).Normal] (hPM : P ≤ M) (hPM' : P ≤ M') (hM : M ≤ S) (hM' : M' ≤ S)
    (hne : M ≠ M') :
    (M.subgroupOf S).map (QuotientGroup.mk' (P.subgroupOf S)) ≠
      (M'.subgroupOf S).map (QuotientGroup.mk' (P.subgroupOf S)) := by
  intro h
  apply hne
  have h1 := Subgroup.map_injective_of_ker_le _ (klein_ker_le hPM) (klein_ker_le hPM') h
  rwa [Subgroup.subgroupOf_inj, inf_of_le_left hM, inf_of_le_left hM'] at h1

theorem three_klein {G : Type*} [Group G] [Finite G] {S P M₁ M₂ M₃ : Subgroup G}
    (hPS : P ≤ S) (hPn : (P.subgroupOf S).Normal) (hidx : P.relIndex S = 8)
    (hnab : ∃ g ∈ S, ∃ h ∈ S, g * h * g⁻¹ * h⁻¹ ∉ P)
    (h₁ : P ≤ M₁) (h₂ : P ≤ M₂) (h₃ : P ≤ M₃) (m₁ : M₁ ≤ S) (m₂ : M₂ ≤ S) (m₃ : M₃ ≤ S)
    (i₁ : M₁.relIndex S = 2) (i₂ : M₂.relIndex S = 2) (i₃ : M₃.relIndex S = 2)
    (s₁ : ∀ x ∈ M₁, x * x ∈ P) (s₂ : ∀ x ∈ M₂, x * x ∈ P) (s₃ : ∀ x ∈ M₃, x * x ∈ P)
    (d₁₂ : M₁ ≠ M₂) (d₁₃ : M₁ ≠ M₃) (d₂₃ : M₂ ≠ M₃) : False := by
  have _ := hPS
  obtain ⟨g, hg, h, hh, hgh⟩ := hnab
  have := hPn
  have hQ : Nat.card (↥S ⧸ P.subgroupOf S) = 8 := hidx
  have key := klein_sq_eq_one hQ
    (klein_image_index h₁ i₁) (klein_image_index h₂ i₂) (klein_image_index h₃ i₃)
    (klein_image_ne h₁ h₂ m₁ m₂ d₁₂) (klein_image_ne h₁ h₃ m₁ m₃ d₁₃)
    (klein_image_ne h₂ h₃ m₂ m₃ d₂₃)
    (klein_image_sq s₁) (klein_image_sq s₂) (klein_image_sq s₃)
  have hinv : ∀ x : ↥S ⧸ P.subgroupOf S, x⁻¹ = x := fun x =>
    (eq_inv_of_mul_eq_one_left (key x)).symm
  have hcomm : ∀ x y : ↥S ⧸ P.subgroupOf S, x * y = y * x := fun x y =>
    calc x * y = (x * y)⁻¹ := (hinv _).symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [hinv, hinv]
  apply hgh
  have hone : QuotientGroup.mk' (P.subgroupOf S)
      ((⟨g, hg⟩ : ↥S) * ⟨h, hh⟩ * (⟨g, hg⟩ : ↥S)⁻¹ * (⟨h, hh⟩ : ↥S)⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    exact hcomm _ _
  exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 hone)

end CFSG.Quasithin.A38c6
