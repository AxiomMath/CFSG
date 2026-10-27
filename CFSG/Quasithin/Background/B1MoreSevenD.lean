module

public import CFSG.Quasithin.Background.B1MoreSevenA

public section

namespace CFSG.Quasithin

open CFSG.Open

theorem card_le_card_image_mul {G β : Type*} [Group G] [Finite G] (A C : Subgroup G) (f : G → β)
    (hC : ∀ b ∈ A, ∀ b' ∈ A, f b = f b' → b⁻¹ * b' ∈ C) :
    ∃ s : Finset β, (∀ b ∈ A, f b ∈ s) ∧ (∀ x ∈ s, ∃ b ∈ A, f b = x) ∧
      Nat.card A ≤ s.card * Nat.card C := by
  classical
  have : Fintype ↥A := Fintype.ofFinite _
  have : Fintype ↥C := Fintype.ofFinite _
  refine ⟨Finset.univ.image (fun b : ↥A => f b), ?_, ?_, ?_⟩
  · intro b hb
    exact Finset.mem_image.2 ⟨⟨b, hb⟩, Finset.mem_univ _, rfl⟩
  · intro x hx
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hx
    exact ⟨b, b.2, rfl⟩
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    have := Finset.card_le_mul_card_image (Finset.univ : Finset ↥A) (Fintype.card ↥C)
      (f := fun b : ↥A => f b) ?_
    · simpa [mul_comm] using this
    · intro J hJ
      obtain ⟨b₀, -, rfl⟩ := Finset.mem_image.1 hJ
      rw [← Fintype.card_subtype]
      refine Fintype.card_le_of_injective
        (fun b : {x : ↥A // f x = f b₀} => (⟨(b₀ : G)⁻¹ * b.1, hC _ b₀.2 _ b.1.2 b.2.symm⟩ : ↥C)) ?_
      intro b b' h
      have h1 : (b₀ : G)⁻¹ * b.1 = (b₀ : G)⁻¹ * b'.1 := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext (mul_left_cancel h1))

theorem cover_of_card {V : Type*} [CommGroup V] [Finite V] (Z Wp Dp : Subgroup V)
    (𝒥 : Finset (Subgroup V)) (hZW : Z ≤ Wp) (hJZ : ∀ J ∈ 𝒥, Z ≤ J) (hJW : ∀ J ∈ 𝒥, J ≤ Wp)
    (hDZ : Z ≤ Dp) (hDW : Dp ≤ Wp) (hJJ : ∀ J ∈ 𝒥, ∀ J' ∈ 𝒥, J ≠ J' → J ⊓ J' = Z)
    (hDJ : ∀ J ∈ 𝒥, Dp ⊓ J = Z) (Q : ℕ) (hJ : ∀ J ∈ 𝒥, Nat.card J = Q) (hD : Nat.card Dp = Q)
    (hW : Nat.card Wp * Nat.card Z = Q * Q) (hs : Q ≤ 𝒥.card * Nat.card Z) :
    ∀ x ∈ Wp, x ∈ Dp ∨ ∃ J ∈ 𝒥, x ∈ J := by
  classical
  have : Fintype V := Fintype.ofFinite V
  set z := Nat.card Z with hz
  have hzpos : 0 < z := Nat.card_pos
  have hF : ∀ S : Subgroup V, Nat.card S = (Finset.univ.filter (· ∈ S)).card := by
    intro S
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  let T : Subgroup V → Finset V := fun S => Finset.univ.filter (fun x => x ∈ S ∧ x ∉ Z)
  have hTcard : ∀ S : Subgroup V, Z ≤ S → (T S).card = Nat.card S - z := by
    intro S hZS
    have hsub : Finset.univ.filter (· ∈ Z) ⊆ Finset.univ.filter (· ∈ S) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hZS hx
    have : T S = Finset.univ.filter (· ∈ S) \ Finset.univ.filter (· ∈ Z) := by
      ext x
      simp [T]
    rw [this, Finset.card_sdiff_of_subset hsub, ← hF, ← hF]
  have hQz : z ≤ Q := by
    by_cases h : 𝒥 = ∅
    ·
      rw [← hD]
      exact Subgroup.card_le_of_le hDZ
    · obtain ⟨J, hJm⟩ := Finset.nonempty_iff_ne_empty.2 h
      rw [← hJ J hJm]
      exact Subgroup.card_le_of_le (hJZ J hJm)
  have hWz : z ≤ Nat.card Wp := Subgroup.card_le_of_le hZW
  set U₁ : Finset V := 𝒥.biUnion T with hU₁
  have hdisj1 : (𝒥 : Set (Subgroup V)).PairwiseDisjoint T := by
    intro J hJm J' hJm' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hx'
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
    have : x ∈ J ⊓ J' := ⟨hx.1, hx'.1⟩
    rw [hJJ J hJm J' hJm' hne] at this
    exact hx.2 this
  have hcard1 : U₁.card = 𝒥.card * (Q - z) := by
    rw [hU₁, Finset.card_biUnion hdisj1]
    exact Finset.sum_const_nat fun J hJm => by rw [hTcard J (hJZ J hJm), hJ J hJm]
  have hdisj2 : Disjoint U₁ (T Dp) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨J, hJm, hxJ⟩ := Finset.mem_biUnion.1 hx
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hxJ hx'
    have : x ∈ Dp ⊓ J := ⟨hx'.1, hxJ.1⟩
    rw [hDJ J hJm] at this
    exact hxJ.2 this
  have hcard : (U₁ ∪ T Dp).card = 𝒥.card * (Q - z) + (Q - z) := by
    rw [Finset.card_union_of_disjoint hdisj2, hcard1, hTcard Dp hDZ, hD]
  have hsubset : U₁ ∪ T Dp ⊆ T Wp := by
    intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · obtain ⟨J, hJm, hxJ⟩ := Finset.mem_biUnion.1 hx
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hxJ ⊢
      exact ⟨hJW J hJm hxJ.1, hxJ.2⟩
    · simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact ⟨hDW hx.1, hx.2⟩
  have hTW : (T Wp).card = Nat.card Wp - z := hTcard Wp hZW
  have hle : (T Wp).card ≤ (U₁ ∪ T Dp).card := by
    rw [hcard, hTW]
    obtain ⟨q', hq'⟩ := Nat.exists_eq_add_of_le hQz
    obtain ⟨w', hw'⟩ := Nat.exists_eq_add_of_le hWz
    rw [hw'] at hW ⊢
    rw [hq'] at hW hs ⊢
    simp only [Nat.add_sub_cancel_left] at *
    refine Nat.le_of_mul_le_mul_right ?_ hzpos
    nlinarith
  have hEq : U₁ ∪ T Dp = T Wp := Finset.eq_of_subset_of_card_le hsubset hle
  intro x hx
  by_cases hxZ : x ∈ Z
  · exact Or.inl (hDZ hxZ)
  · have hxT : x ∈ T Wp := by simp [T, hx, hxZ]
    rw [← hEq] at hxT
    rcases Finset.mem_union.1 hxT with h | h
    · obtain ⟨J, hJm, hxJ⟩ := Finset.mem_biUnion.1 h
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hxJ
      exact Or.inr ⟨J, hJm, hxJ.1⟩
    · simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at h
      exact Or.inl h.1

end CFSG.Quasithin
