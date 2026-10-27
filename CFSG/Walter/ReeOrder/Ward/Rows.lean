module

public import CFSG.Walter.ReeOrder.Ward.Eta
public import CFSG.Walter.ReeOrder.Ward.Columns

public section

open scoped BigOperators Classical

namespace CFSG.Walter.Ward

open CFSG.SmallDefect CFSG.BlockSectionOrthogonality.Helpers

namespace WardSetup

variable {G : Type} [Group G] [Fintype G] {L : Type} [Group L] [Fintype L] {q : ℕ} {e : ℤ}
  {IV : Bool} {S : WardSetup G L q e IV} (D : S.EtaData)

theorem sum_family_le {ι : Type} [Fintype ι] (η : ι → G → ℂ) (hinj : Function.Injective η)
    (hmem : ∀ i, η i ∈ BlocksIrr G) (f : (G → ℂ) → ℤ) (hf : ∀ χ, 0 ≤ f χ) :
    ∑ i, f (η i) ≤ ∑ χ ∈ (irreducibles_finite G).toFinset, f χ := by
  rw [← Finset.sum_image (fun i _ j _ h => hinj h)]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro χ hχ
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hχ
    rw [Set.Finite.mem_toFinset]
    exact hmem i
  · intro χ _ _
    exact hf χ

theorem sum_two_families_le {ι : Type} [Fintype ι] (η η' : ι → G → ℂ)
    (hinj : Function.Injective η) (hinj' : Function.Injective η')
    (hdisj : ∀ i k, η i ≠ η' k) (hmem : ∀ i, η i ∈ BlocksIrr G)
    (hmem' : ∀ i, η' i ∈ BlocksIrr G) (f : (G → ℂ) → ℤ) (hf : ∀ χ, 0 ≤ f χ) :
    ∑ i, f (η i) + ∑ i, f (η' i) ≤ ∑ χ ∈ (irreducibles_finite G).toFinset, f χ := by
  rw [← Finset.sum_image (fun i _ j _ h => hinj h), ← Finset.sum_image (fun i _ j _ h => hinj' h),
    ← Finset.sum_union]
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro χ hχ
      rcases Finset.mem_union.mp hχ with h | h <;> obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp h <;>
        rw [Set.Finite.mem_toFinset]
      · exact hmem i
      · exact hmem' i
    · intro χ _ _
      exact hf χ
  · rw [Finset.disjoint_left]
    intro χ h1 h2
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨k, -, hk⟩ := Finset.mem_image.mp h2
    exact hdisj i k hk.symm

theorem eq_zero_of_mul_sq_le {n c a : ℤ} (h : n * (a * a) ≤ c) (hc : c < n) (hn : 0 < n) :
    a = 0 := by
  by_contra ha
  have h1 : 1 ≤ a * a := by
    have := mul_self_pos.mpr ha
    omega
  nlinarith

namespace EtaData

theorem ma_η_const (i j : S.W.RFam) {θ : L → ℂ} (hθ : θ ∈ BlocksIrr L) (hR : θ ∉ S.W.RFam) :
    S.ma (D.η i) θ = S.ma (D.η j) θ := by
  have h := D.ma_η i j θ hθ
  have hi : θ ≠ i.1 := fun h => hR (h ▸ i.2)
  have hj : θ ≠ j.1 := fun h => hR (h ▸ j.2)
  simp only [hi, hj, ↓reduceIte, sub_self, mul_zero, sub_eq_zero] at h
  exact_mod_cast h

theorem mb_η'_const (i j : S.W.RFam) {θ : L → ℂ} (hθ : θ ∈ BlocksIrr L)
    (hR : θ ∉ S.W.RFam) : S.mb (D.η' i) θ = S.mb (D.η' j) θ := by
  have h := D.mb_η' i j θ hθ
  have hi : θ ≠ i.1 := fun h => hR (h ▸ i.2)
  have hj : θ ≠ j.1 := fun h => hR (h ▸ j.2)
  simp only [hi, hj, ↓reduceIte, sub_self, mul_zero, sub_eq_zero] at h
  exact_mod_cast h

theorem M_η_const (i j : S.W.RFam) {θ : L → ℂ} (hθ : θ ∈ BlocksIrr L) (hR : θ ∉ S.W.RFam) :
    S.M (D.η i) θ = S.M (D.η j) θ := by
  simp only [M, D.ma_η_const i j hθ hR, D.mb_η i j θ hθ]

theorem M_η'_const (i j : S.W.RFam) {θ : L → ℂ} (hθ : θ ∈ BlocksIrr L) (hR : θ ∉ S.W.RFam) :
    S.M (D.η' i) θ = S.M (D.η' j) θ := by
  simp only [M, D.ma_η' i j θ hθ, D.mb_η'_const i j hθ hR]

theorem Ar_η_const (i j : S.W.RFam) {θ : L → ℂ} (hθ : θ ∈ BlocksIrr L) (hR : θ ∉ S.W.RFam) :
    S.Ar (D.η i) θ = S.Ar (D.η j) θ := by
  simp only [Ar, D.ma_η_const i j hθ hR, D.mb_η i j θ hθ]

theorem Ar_η'_const (i j : S.W.RFam) {θ : L → ℂ} (hθ : θ ∈ BlocksIrr L) (hR : θ ∉ S.W.RFam) :
    S.Ar (D.η' i) θ = S.Ar (D.η' j) θ := by
  simp only [Ar, D.ma_η' i j θ hθ, D.mb_η'_const i j hθ hR]

theorem dR_η_diff (i k l : S.W.RFam) :
    S.dR (D.η i) k.1 - S.dR (D.η i) l.1 =
      D.ε * ((if i = k then 1 else 0) - (if i = l then 1 else 0)) := by
  have h1 := D.ma_other (D.η i) (D.mem i) k l
  have h2 := D.mb_other (D.η i) (D.mem i) k l
  simp only [D.inj.eq_iff, fun m => D.disj i m, ↓reduceIte, sub_self, mul_zero] at h1 h2
  simp only [dR, M]
  linear_combination h1 - h2

theorem dR_η_diff' (i j k : S.W.RFam) :
    S.dR (D.η i) k.1 - S.dR (D.η j) k.1 =
      D.ε * ((if i = k then 1 else 0) - (if j = k then 1 else 0)) := by
  have h1 := D.ma_η i j k.1 (S.W.R_mem k.2)
  have h2 := D.mb_η i j k.1 (S.W.R_mem k.2)
  simp only [dR, M, h2]
  have hik : (k.1 = i.1) ↔ (i = k) := by rw [eq_comm, Subtype.ext_iff]
  have hjk : (k.1 = j.1) ↔ (j = k) := by rw [eq_comm, Subtype.ext_iff]
  simp only [hik, hjk] at h1
  linear_combination h1

theorem dR_η'_diff (i k l : S.W.RFam) :
    S.dR (D.η' i) k.1 - S.dR (D.η' i) l.1 =
      -D.ε' * ((if i = k then 1 else 0) - (if i = l then 1 else 0)) := by
  have h1 := D.ma_other (D.η' i) (D.mem' i) k l
  have h2 := D.mb_other (D.η' i) (D.mem' i) k l
  simp only [D.inj'.eq_iff, fun m => (D.disj m i).symm, ↓reduceIte, sub_self, mul_zero] at h1 h2
  simp only [dR, M]
  linear_combination h1 - h2

theorem dR_η'_diff' (i j k : S.W.RFam) :
    S.dR (D.η' i) k.1 - S.dR (D.η' j) k.1 =
      -D.ε' * ((if i = k then 1 else 0) - (if j = k then 1 else 0)) := by
  have h1 := D.ma_η' i j k.1 (S.W.R_mem k.2)
  have h2 := D.mb_η' i j k.1 (S.W.R_mem k.2)
  simp only [dR, M, h1]
  have hik : (k.1 = i.1) ↔ (i = k) := by rw [eq_comm, Subtype.ext_iff]
  have hjk : (k.1 = j.1) ↔ (j = k) := by rw [eq_comm, Subtype.ext_iff]
  simp only [hik, hjk] at h2
  linear_combination -h2

theorem card_ge : 6 ≤ Fintype.card S.W.RFam := by
  rw [Fintype.card_coe]
  exact S.card_RFam_ge

theorem exists_third (i j : S.W.RFam) : ∃ m : S.W.RFam, m ≠ i ∧ m ≠ j := by
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset S.W.RFam) ⊆ {i, j} := by
    intro m _
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases hmi : m = i
    · exact Or.inl hmi
    · exact Or.inr (h m hmi)
  have := Finset.card_le_card hsub
  rw [Finset.card_univ] at this
  have h2 : ({i, j} : Finset S.W.RFam).card ≤ 2 := Finset.card_le_two
  have := card_ge (S := S)
  omega

theorem dR_η_offdiag (i k j l : S.W.RFam) (hik : i ≠ k) (hjl : j ≠ l) :
    S.dR (D.η i) k.1 = S.dR (D.η j) l.1 := by
  obtain ⟨m, hmi, hmj⟩ := exists_third i j
  have h1 := D.dR_η_diff i k m
  have h2 := D.dR_η_diff' i j m
  have h3 := D.dR_η_diff j m l
  simp only [hik, Ne.symm hmi, Ne.symm hmj, hjl, ↓reduceIte, sub_self, mul_zero] at h1 h2 h3
  linarith

theorem dR_η'_offdiag (i k j l : S.W.RFam) (hik : i ≠ k) (hjl : j ≠ l) :
    S.dR (D.η' i) k.1 = S.dR (D.η' j) l.1 := by
  obtain ⟨m, hmi, hmj⟩ := exists_third i j
  have h1 := D.dR_η'_diff i k m
  have h2 := D.dR_η'_diff' i j m
  have h3 := D.dR_η'_diff j m l
  simp only [hik, Ne.symm hmi, Ne.symm hmj, hjl, ↓reduceIte, sub_self, mul_zero] at h1 h2 h3
  linarith

theorem ε_sq : D.ε * D.ε = 1 := by rcases D.ε_eq with h | h <;> rw [h] <;> norm_num
theorem ε'_sq : D.ε' * D.ε' = 1 := by rcases D.ε'_eq with h | h <;> rw [h] <;> norm_num

theorem norm_R (k : S.W.RFam) :
    ∑ χ ∈ (irreducibles_finite G).toFinset, S.dR χ k.1 * S.dR χ k.1 = 2 := by
  rw [S.gram_R k.2 k.2, ite_eq_left rfl]

theorem dR_η (i k : S.W.RFam) : S.dR (D.η i) k.1 = if i = k then D.ε else 0 := by
  obtain ⟨k₀, hk₀⟩ := exists_third k k
  set c := S.dR (D.η k₀) k.1 with hc
  have hoff : ∀ j : S.W.RFam, j ≠ k → S.dR (D.η j) k.1 = c := fun j hj =>
    D.dR_η_offdiag j k k₀ k hj hk₀.1
  have hdiag : S.dR (D.η k) k.1 = c + D.ε := by
    have h := D.dR_η_diff k k k₀
    simp only [↓reduceIte, Ne.symm hk₀.1, sub_zero, mul_one] at h
    rw [D.dR_η_offdiag k k₀ k₀ k (Ne.symm hk₀.1) hk₀.1] at h
    linarith
  have hle := sum_family_le D.η D.inj D.mem (fun χ => S.dR χ k.1 * S.dR χ k.1)
    (fun χ => mul_self_nonneg _)
  rw [norm_R k] at hle
  have hsum : ∑ j, S.dR (D.η j) k.1 * S.dR (D.η j) k.1 =
      ((Finset.univ.erase k).card : ℤ) * (c * c) + (c + D.ε) * (c + D.ε) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k), hdiag]
    congr 1
    rw [Finset.sum_congr rfl fun j hj => by rw [hoff j (Finset.ne_of_mem_erase hj)],
      Finset.sum_const, nsmul_eq_mul]
  rw [hsum] at hle
  have hcard : ((Finset.univ.erase k).card : ℤ) ≥ 5 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    have := card_ge (S := S)
    omega
  have hc0 : c = 0 := by
    have h1 : ((Finset.univ.erase k).card : ℤ) * (c * c) ≤ 2 := by
      nlinarith [mul_self_nonneg (c + D.ε)]
    exact eq_zero_of_mul_sq_le h1 (by omega) (by omega)
  by_cases hik : i = k
  · rw [ite_eq_left hik, hik, hdiag, hc0, zero_add]
  · rw [ite_eq_right hik, hoff i hik, hc0]

theorem dR_η' (i k : S.W.RFam) : S.dR (D.η' i) k.1 = if i = k then -D.ε' else 0 := by
  obtain ⟨k₀, hk₀⟩ := exists_third k k
  set c := S.dR (D.η' k₀) k.1 with hc
  have hoff : ∀ j : S.W.RFam, j ≠ k → S.dR (D.η' j) k.1 = c := fun j hj =>
    D.dR_η'_offdiag j k k₀ k hj hk₀.1
  have hdiag : S.dR (D.η' k) k.1 = c - D.ε' := by
    have h := D.dR_η'_diff k k k₀
    simp only [↓reduceIte, Ne.symm hk₀.1, sub_zero, mul_one] at h
    rw [D.dR_η'_offdiag k k₀ k₀ k (Ne.symm hk₀.1) hk₀.1] at h
    linarith
  have hle := sum_family_le D.η' D.inj' D.mem' (fun χ => S.dR χ k.1 * S.dR χ k.1)
    (fun χ => mul_self_nonneg _)
  rw [norm_R k] at hle
  have hsum : ∑ j, S.dR (D.η' j) k.1 * S.dR (D.η' j) k.1 =
      ((Finset.univ.erase k).card : ℤ) * (c * c) + (c - D.ε') * (c - D.ε') := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k), hdiag]
    congr 1
    rw [Finset.sum_congr rfl fun j hj => by rw [hoff j (Finset.ne_of_mem_erase hj)],
      Finset.sum_const, nsmul_eq_mul]
  rw [hsum] at hle
  have hcard : ((Finset.univ.erase k).card : ℤ) ≥ 5 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    have := card_ge (S := S)
    omega
  have hc0 : c = 0 := by
    have h1 : ((Finset.univ.erase k).card : ℤ) * (c * c) ≤ 2 := by
      nlinarith [mul_self_nonneg (c - D.ε')]
    exact eq_zero_of_mul_sq_le h1 (by omega) (by omega)
  by_cases hik : i = k
  · rw [ite_eq_left hik, hik, hdiag, hc0, zero_sub]
  · rw [ite_eq_right hik, hoff i hik, hc0]

theorem dR_other {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) (hη : ∀ i, χ ≠ D.η i)
    (hη' : ∀ i, χ ≠ D.η' i) (k : S.W.RFam) : S.dR χ k.1 = 0 := by
  have hnorm := norm_R k
  have hmem : ∀ ψ ∈ BlocksIrr G, ψ ∈ (irreducibles_finite G).toFinset := fun ψ h => by
    rw [Set.Finite.mem_toFinset]; exact h
  have h1 : ({χ, D.η k, D.η' k} : Finset (G → ℂ)) ⊆ (irreducibles_finite G).toFinset := by
    intro ψ hψ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hψ
    rcases hψ with rfl | rfl | rfl
    · exact hmem _ hχ
    · exact hmem _ (D.mem k)
    · exact hmem _ (D.mem' k)
  have hle := Finset.sum_le_sum_of_subset_of_nonneg h1
    (f := fun ψ => S.dR ψ k.1 * S.dR ψ k.1) (fun ψ _ _ => mul_self_nonneg _)
  rw [Finset.sum_insert (by simp [hη k, hη' k]), Finset.sum_pair (D.disj k k), D.dR_η k k,
    D.dR_η' k k, ite_eq_left rfl, ite_eq_left rfl, hnorm] at hle
  have := D.ε_sq
  have := D.ε'_sq
  nlinarith [mul_self_nonneg (S.dR χ k.1)]

end EtaData

end WardSetup

end CFSG.Walter.Ward
