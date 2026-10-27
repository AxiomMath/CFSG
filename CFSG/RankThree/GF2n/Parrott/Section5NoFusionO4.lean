module

public import CFSG.RankThree.GF2n.Parrott.Section5Lemma54Orbits
import all CFSG.RankThree.GF2n.Parrott.Section5Lemma54Orbits
public import CFSG.RankThree.GF2n.Parrott.Section5Basic

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G] {z : G}

theorem exists_conj_mem_O6_or_mem_O4 (h : Tim79a.ParrottHyp z) {z₁ t y : G}
    {W S₀ : Subgroup G} (O : Fin 7 → Finset G)
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (hOW : ∀ i, ∀ a ∈ O i, a ∈ W ∧ a ≠ 1)
    (hcover : ∀ a ∈ W, a ≠ 1 → ∃ i, a ∈ O i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (O i) (O j))
    (hcard : ∀ i, (O i).card = lemma54Sizes i)
    (hJ : ∀ i : Fin 7, (i : ℕ) < 4 → ∀ a ∈ O i, a ∈ J z)
    (hnJ : ∀ i : Fin 7, 4 ≤ (i : ℕ) → ∀ a ∈ O i, a ∉ J z)
    (hO56 : ∀ a, a ∈ O 5 ∨ a ∈ O 6 →
      ∃ y ∈ H z ⊓ centralizer ({a} : Set G), y ∉ centralizer ({z₁} : Set G))
    (hO5z : ∀ a ∈ O 5, a * z ∈ O 6)
    (hz₁W : z₁ ∈ W) (htW : t ∈ W) (htJ : t ∉ J z)
    (hZS : ∀ e ∈ centerIn S₀, e = 1 ∨ e = z ∨ e = t * z₁ ∨ e = t * z₁ * z)
    (htz₁ : t * z₁ ∈ centerIn S₀)
    (hyH : y ∈ H z) (hyS : y ∈ S₀) (hy : y ∉ centralizer ({z₁} : Set G)) :
    (∃ u ∈ H z, ∃ a ∈ O 5, u * a * u⁻¹ ∈ O 6) ∨
      ((∀ e ∈ centerIn S₀, e = 1 ∨ e = z ∨ e ∈ O 5 ∨ e ∈ O 6) ∧ t ∈ O 4 ∧ t * z ∈ O 4) := by
  classical
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.1, pow_two] at this
  have hz₁sq : z₁ * z₁ = 1 := by
    have := pow_orderOf_eq_one z₁
    rwa [hord, pow_two] at this
  have hzz₁ : z * z₁ = z₁ * z :=
    (Subgroup.mem_centralizer_iff.mp (z_centralizes_H h) z₁ (J_le_H hz₁.1)).symm
  have hmulz_inj : Function.Injective (fun a : G => a * z) := by
    intro a b hab
    have hab' : a * z = b * z := hab
    have h' : a * z * z = b * z * z := by rw [hab']
    simpa [mul_assoc, hz2] using h'
  have hO5card : (O 5).card = 4 := by
    rw [hcard 5]
    rfl
  have hO6card : (O 6).card = 4 := by
    rw [hcard 6]
    rfl
  have hO4card : (O 4).card = 8 := by
    rw [hcard 4]
    rfl
  have himage5 : (O 5).image (fun a => a * z) = O 6 := by
    apply Finset.eq_of_subset_of_card_le
    · rw [Finset.image_subset_iff]
      intro a ha
      exact hO5z a ha
    · rw [Finset.card_image_of_injective _ hmulz_inj, hO5card, hO6card]
  have hO6z : ∀ b ∈ O 6, b * z ∈ O 5 := by
    intro b hb
    have hb' : b ∈ (O 5).image (fun a => a * z) := by rw [himage5]; exact hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb'
    simpa [mul_assoc, hz2] using ha
  have hO56z : ∀ a, a ∈ O 5 ∨ a ∈ O 6 → a * z ∈ O 5 ∨ a * z ∈ O 6 := by
    intro a ha
    rcases ha with h5 | h6
    · exact Or.inr (hO5z a h5)
    · exact Or.inl (hO6z a h6)
  by_cases hfus : ∃ u ∈ H z, ∃ a ∈ O 5, u * a * u⁻¹ ∈ O 6
  · exact Or.inl hfus
  · right
    push Not at hfus
    have hnf : ∀ u ∈ H z, ∀ a,
        (a ∈ O 5 ∧ u * a * u⁻¹ ∈ O 6) ∨ (a ∈ O 6 ∧ u * a * u⁻¹ ∈ O 5) → False := by
      intro u hu a ha
      rcases ha with ⟨h5, h6⟩ | ⟨h6, h5⟩
      · exact hfus u hu a h5 h6
      · have hu' : u⁻¹ ∈ H z := (H z).inv_mem hu
        have heq : u⁻¹ * (u * a * u⁻¹) * (u⁻¹)⁻¹ = a := by group
        have hmem : u⁻¹ * (u * a * u⁻¹) * (u⁻¹)⁻¹ ∈ O 6 := by
          rw [heq]
          exact h6
        exact hfus u⁻¹ hu' (u * a * u⁻¹) h5 hmem
    have hswap : ∀ u ∈ H z, ∀ b, b ∈ O 5 ∨ b ∈ O 6 → u * b * u⁻¹ ≠ b * z := by
      intro u hu b hb hconj
      rcases hb with h5 | h6
      · exact hnf u hu b (Or.inl ⟨h5, by rw [hconj]; exact hO5z b h5⟩)
      · exact hnf u hu b (Or.inr ⟨h6, by rw [hconj]; exact hO6z b h6⟩)
    have hmulz₁_inj : Function.Injective (fun a : G => a * z₁) := by
      intro a b hab
      have hab' : a * z₁ = b * z₁ := hab
      have h' : a * z₁ * z₁ = b * z₁ * z₁ := by rw [hab']
      simpa [mul_assoc, hz₁sq] using h'
    have hz₁O4 : ∀ a, a ∈ O 5 ∨ a ∈ O 6 → a * z₁ ∈ O 4 := by
      intro a ha
      have haW : a ∈ W := by
        rcases ha with h5 | h6
        · exact (hOW 5 a h5).1
        · exact (hOW 6 a h6).1
      have hanJ : a ∉ J z := by
        rcases ha with h5 | h6
        · exact hnJ 5 (by norm_num) a h5
        · exact hnJ 6 (by norm_num) a h6
      have haz₁W : a * z₁ ∈ W := W.mul_mem haW hz₁W
      have haz₁nJ : a * z₁ ∉ J z := by
        intro hmem
        apply hanJ
        have hm := (J z).mul_mem hmem hz₁.1
        rwa [mul_assoc, hz₁sq, mul_one] at hm
      have haz₁ne1 : a * z₁ ≠ 1 := by
        intro heq
        apply hanJ
        have haz : a = z₁ := by
          calc a = (a * z₁) * z₁ := by rw [mul_assoc, hz₁sq, mul_one]
            _ = 1 * z₁ := by rw [heq]
            _ = z₁ := one_mul z₁
        rw [haz]
        exact hz₁.1
      obtain ⟨i, hi⟩ := hcover (a * z₁) haz₁W haz₁ne1
      have hi4 : 4 ≤ (i : ℕ) := by
        by_contra hlt
        push Not at hlt
        exact haz₁nJ (hJ i hlt (a * z₁) hi)
      have hicases : i = 4 ∨ i = 5 ∨ i = 6 := by
        fin_cases i <;> simp at hi4 ⊢
      rcases hicases with rfl | rfl | rfl
      · exact hi
      · obtain ⟨y, hy, hyz₁⟩ := hO56 a ha
        have hyH : y ∈ H z := hy.1
        have hya : y * a = a * y := Subgroup.mem_centralizer_singleton_iff.mp hy.2
        have hyz₁' : y * z₁ * y⁻¹ = z * z₁ :=
          conj_z1_eq_of_not_mem_centralizer h hz₁ hz₁z hord hyH hyz₁
        have hconj : y * (a * z₁) * y⁻¹ = (a * z₁) * z := by
          calc y * (a * z₁) * y⁻¹ = (y * a) * (z₁ * y⁻¹) := by group
            _ = (a * y) * (z₁ * y⁻¹) := by rw [hya]
            _ = a * (y * z₁ * y⁻¹) := by group
            _ = a * (z * z₁) := by rw [hyz₁']
            _ = a * (z₁ * z) := by rw [hzz₁]
            _ = (a * z₁) * z := by group
        exact absurd hconj (hswap y hyH (a * z₁) (Or.inl hi))
      · obtain ⟨y, hy, hyz₁⟩ := hO56 a ha
        have hyH : y ∈ H z := hy.1
        have hya : y * a = a * y := Subgroup.mem_centralizer_singleton_iff.mp hy.2
        have hyz₁' : y * z₁ * y⁻¹ = z * z₁ :=
          conj_z1_eq_of_not_mem_centralizer h hz₁ hz₁z hord hyH hyz₁
        have hconj : y * (a * z₁) * y⁻¹ = (a * z₁) * z := by
          calc y * (a * z₁) * y⁻¹ = (y * a) * (z₁ * y⁻¹) := by group
            _ = (a * y) * (z₁ * y⁻¹) := by rw [hya]
            _ = a * (y * z₁ * y⁻¹) := by group
            _ = a * (z * z₁) := by rw [hyz₁']
            _ = a * (z₁ * z) := by rw [hzz₁]
            _ = (a * z₁) * z := by group
        exact absurd hconj (hswap y hyH (a * z₁) (Or.inr hi))
    have hO4z₁ : ∀ b ∈ O 4, b * z₁ ∈ O 5 ∨ b * z₁ ∈ O 6 := by
      have hunion_card : ((O 5) ∪ (O 6)).card = 8 := by
        rw [Finset.card_union_of_disjoint (hdisj 5 6 (by decide)), hO5card, hO6card]
      have himage : ((O 5) ∪ (O 6)).image (fun a => a * z₁) = O 4 := by
        apply Finset.eq_of_subset_of_card_le
        · rw [Finset.image_subset_iff]
          intro a ha
          exact hz₁O4 a (Finset.mem_union.mp ha)
        · rw [Finset.card_image_of_injective _ hmulz₁_inj, hunion_card, hO4card]
      intro b hb
      have hb' : b ∈ ((O 5) ∪ (O 6)).image (fun a => a * z₁) := by rw [himage]; exact hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb'
      rw [mul_assoc, hz₁sq, mul_one]
      exact Finset.mem_union.mp ha
    have htz₁56 : t * z₁ ∈ O 5 ∨ t * z₁ ∈ O 6 := by
      have htz₁W : t * z₁ ∈ W := W.mul_mem htW hz₁W
      have htz₁nJ : t * z₁ ∉ J z := by
        intro hmem
        apply htJ
        have hm := (J z).mul_mem hmem hz₁.1
        rwa [mul_assoc, hz₁sq, mul_one] at hm
      have htz₁ne1 : t * z₁ ≠ 1 := by
        intro heq
        apply htJ
        have ht : t = z₁ := by
          calc t = (t * z₁) * z₁ := by rw [mul_assoc, hz₁sq, mul_one]
            _ = 1 * z₁ := by rw [heq]
            _ = z₁ := one_mul z₁
        rw [ht]
        exact hz₁.1
      obtain ⟨i, hi⟩ := hcover (t * z₁) htz₁W htz₁ne1
      have hi4 : 4 ≤ (i : ℕ) := by
        by_contra hlt
        push Not at hlt
        exact htz₁nJ (hJ i hlt (t * z₁) hi)
      have hicases : i = 4 ∨ i = 5 ∨ i = 6 := by
        fin_cases i <;> simp at hi4 ⊢
      rcases hicases with rfl | rfl | rfl
      · have ht56 : t ∈ O 5 ∨ t ∈ O 6 := by
          have h := hO4z₁ (t * z₁) hi
          rwa [mul_assoc, hz₁sq, mul_one] at h
        have hcomm : y * (t * z₁) = (t * z₁) * y :=
          Subgroup.mem_centralizer_iff.mp htz₁.2 y hyS
        have hyz₁' : y * z₁ * y⁻¹ = z * z₁ :=
          conj_z1_eq_of_not_mem_centralizer h hz₁ hz₁z hord hyH hy
        have ht : (t * z₁) * z₁ = t := by rw [mul_assoc, hz₁sq, mul_one]
        have hconj : y * t * y⁻¹ = t * z := by
          calc y * t * y⁻¹ = y * ((t * z₁) * z₁) * y⁻¹ := by rw [ht]
            _ = (y * (t * z₁) * y⁻¹) * (y * z₁ * y⁻¹) := by group
            _ = (t * z₁) * (z * z₁) := by
                rw [hcomm, mul_inv_cancel_right, hyz₁']
            _ = t * (z₁ * z) * z₁ := by group
            _ = t * (z * z₁) * z₁ := by rw [hzz₁]
            _ = t * z * (z₁ * z₁) := by group
            _ = t * z := by rw [hz₁sq, mul_one]
        exact absurd hconj (hswap y hyH t ht56)
      · exact Or.inl hi
      · exact Or.inr hi
    have htO4 : t ∈ O 4 := by
      have h := hz₁O4 (t * z₁) htz₁56
      rwa [mul_assoc, hz₁sq, mul_one] at h
    have htzO4 : t * z ∈ O 4 := by
      have h := hz₁O4 ((t * z₁) * z) (hO56z (t * z₁) htz₁56)
      have heq : ((t * z₁) * z) * z₁ = t * z := by
        calc ((t * z₁) * z) * z₁ = (t * z₁) * (z * z₁) := by rw [mul_assoc]
          _ = (t * z₁) * (z₁ * z) := by rw [hzz₁]
          _ = t * (z₁ * (z₁ * z)) := by rw [mul_assoc]
          _ = t * ((z₁ * z₁) * z) := by rw [← mul_assoc z₁ z₁ z]
          _ = t * z := by rw [hz₁sq, one_mul]
      rwa [heq] at h
    refine ⟨?_, htO4, htzO4⟩
    intro e he
    rcases hZS e he with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr htz₁56)
    · exact Or.inr (Or.inr (hO56z (t * z₁) htz₁56))

end CFSG.RankThree.GF2n.Parrott
