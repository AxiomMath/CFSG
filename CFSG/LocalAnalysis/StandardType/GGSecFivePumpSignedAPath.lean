module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDkRootsBasic

public section

namespace CFSG.StandardType

private theorem pair_trans {k : ℕ} {Φ : Set (Fin k → ℤ)} (hΦ : GGDSubsys k Φ) {ε : Fin k → ℤ}
    (hε : ∀ a, ε a = 1 ∨ ε a = -1) {a b c : Fin k} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (h1 : Pi.single a (ε a) - Pi.single b (ε b) ∈ Φ)
    (h2 : Pi.single b (ε b) - Pi.single c (ε c) ∈ Φ) :
    Pi.single a (ε a) - Pi.single c (ε c) ∈ Φ := by
  have hd : ggDDot (Pi.single b (ε b) - Pi.single c (ε c))
      (Pi.single a (ε a) - Pi.single b (ε b)) = -1 := by
    rw [ggDDot_eq_dotProduct, sub_dotProduct, single_dotProduct, single_dotProduct]
    simp only [Pi.sub_apply, Pi.single_apply, if_neg hab.symm, if_neg hac.symm, if_neg hbc.symm,
      ↓reduceIte]
    rcases hε b with h | h <;> rw [h] <;> ring
  have h := hΦ.2 _ h1 _ h2
  rw [ggDReflect, hd, neg_one_smul, sub_neg_eq_add] at h
  convert h using 1
  abel

private theorem step {k : ℕ} {Φ : Set (Fin k → ℤ)} (hΦ : GGDSubsys k Φ) {T : Finset (Fin k)}
    {ε : Fin k → ℤ} (hε : ∀ a, ε a = 1 ∨ ε a = -1)
    (hP : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → Pi.single a (ε a) - Pi.single b (ε b) ∈ Φ)
    {δ : Fin k → ℤ} (hδ : δ ∈ Φ) {y z : Fin k} (hy : y ∈ T) (hz : z ∉ T) (hδy : δ y ≠ 0)
    (hδz : δ z ≠ 0) :
    ∃ ε' : Fin k → ℤ, (∀ a ∈ T, ε' a = ε a) ∧ (∀ a, ε' a = 1 ∨ ε' a = -1) ∧ ggDDot ε' δ = 0 ∧
      ∀ a ∈ insert z T, ∀ b ∈ insert z T, a ≠ b →
        Pi.single a (ε' a) - Pi.single b (ε' b) ∈ Φ := by
  have hyz : y ≠ z := fun h => hz (h ▸ hy)
  have hR := hΦ.1 hδ
  have sy := ggDRootSet_sign hR hδy
  have sz := ggDRootSet_sign hR hδz
  set ε' := Function.update ε z (-(δ y * δ z * ε y))
  have hT : ∀ a ∈ T, ε' a = ε a := fun a ha => by
    have haz : a ≠ z := fun h => hz (h ▸ ha)
    exact Function.update_of_ne haz _ _
  have hz' : ε' z = -(δ y * δ z * ε y) := Function.update_self ..
  have h1 : ∀ a, ε' a = 1 ∨ ε' a = -1 := fun a => by
    by_cases ha : a = z
    · rw [ha, hz']
      rcases sy with h | h <;> rcases sz with h' | h' <;> rcases hε y with h'' | h'' <;>
        simp [h, h', h'']
    · rw [show ε' a = ε a from Function.update_of_ne ha _ _]
      exact hε a
  have hyz' : Pi.single y (ε' y) - Pi.single z (ε' z) ∈ Φ := by
    have hv : Pi.single y (ε' y) - Pi.single z (ε' z) = (δ y * ε y) • δ := by
      funext c
      rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hcy : c = y
      · rw [hcy, Pi.single_eq_same, Pi.single_eq_of_ne hyz, hT y hy]
        rcases sy with h | h <;> rw [h] <;> ring
      by_cases hcz : c = z
      · rw [hcz, Pi.single_eq_of_ne hyz.symm, Pi.single_eq_same, hz']
        ring
      rw [Pi.single_eq_of_ne hcy, Pi.single_eq_of_ne hcz, ggDRootSet_eq_zero hR hyz hδy hδz hcy hcz]
      ring
    rw [hv]
    rcases sy with h | h <;> rcases hε y with h' | h' <;> rw [h, h'] <;> norm_num
    · exact hδ
    · exact hΦ.neg_mem hδ
    · exact hΦ.neg_mem hδ
    · exact hδ
  have hd : ggDDot ε' δ = 0 := by
    rw [ggDDot_comm, ggDRootSet_dot_eq hR hyz hδy hδz, hT y hy, hz']
    rcases sz with h | h <;> rw [h] <;> ring
  have hPz : ∀ a ∈ T, Pi.single a (ε' a) - Pi.single z (ε' z) ∈ Φ := fun a ha => by
    by_cases hay : a = y
    · rw [hay]
      exact hyz'
    have h' := hP a ha y hy hay
    rw [← hT a ha, ← hT y hy] at h'
    exact pair_trans hΦ h1 hay hyz (fun h => hz (h ▸ ha)) h' hyz'
  refine ⟨ε', hT, h1, hd, fun a ha b hb hab => ?_⟩
  rcases Finset.mem_insert.1 ha with ha' | ha' <;> rcases Finset.mem_insert.1 hb with hb' | hb'
  · exact absurd (ha'.trans hb'.symm) hab
  · rw [ha']
    simpa only [neg_sub] using hΦ.neg_mem (hPz b hb')
  · rw [hb']
    exact hPz a ha'
  · rw [hT a ha', hT b hb']
    exact hP a ha' b hb' hab

theorem ggDk_signedA_of_path {k n : ℕ} {Φ : Set (Fin k → ℤ)} (hΦ : GGDSubsys k Φ)
    {θ : ℕ → Fin k → ℤ} (hθ : ∀ j < n, θ j ∈ Φ)
    (hadj : ∀ j, j + 1 < n → ∃ y z, θ j y ≠ 0 ∧ θ (j + 1) y ≠ 0 ∧ θ (j + 1) z ≠ 0 ∧ θ j z = 0)
    (hfar : ∀ i j, j < n → i + 1 < j → ∀ c, θ i c = 0 ∨ θ j c = 0) (hn : 0 < n) :
    ∃ (T : Finset (Fin k)) (ε : Fin k → ℤ), T.card = n + 1 ∧ (∀ a, ε a = 1 ∨ ε a = -1) ∧
      (∀ j < n, ggDDot ε (θ j) = 0) ∧
      ∀ a ∈ T, ∀ b ∈ T, a ≠ b → Pi.single a (ε a) - Pi.single b (ε b) ∈ Φ := by
  obtain ⟨y₀, -, -, hy₀, -⟩ := ggDRootSet_exists_pair (hΦ.1 (hθ 0 hn))
  suffices H : ∀ m ≤ n, ∃ (T : Finset (Fin k)) (ε : Fin k → ℤ), T.card = m + 1 ∧
      (∀ a, ε a = 1 ∨ ε a = -1) ∧ (∀ c, c ∈ T ↔ c = y₀ ∨ ∃ j < m, θ j c ≠ 0) ∧
      (∀ j < m, ggDDot ε (θ j) = 0) ∧
      ∀ a ∈ T, ∀ b ∈ T, a ≠ b → Pi.single a (ε a) - Pi.single b (ε b) ∈ Φ by
    obtain ⟨T, ε, h1, h2, -, h4, h5⟩ := H n le_rfl
    exact ⟨T, ε, h1, h2, h4, h5⟩
  intro m hm
  induction m with
  | zero =>
    refine ⟨{y₀}, fun _ => 1, rfl, fun _ => Or.inl rfl, fun c => by simp, fun j hj => ?_,
      fun a ha b hb hab => ?_⟩
    · exact absurd hj (Nat.not_lt_zero _)
    · exact absurd ((Finset.mem_singleton.1 ha).trans (Finset.mem_singleton.1 hb).symm) hab
  | succ m ih =>
    obtain ⟨T, ε, hc, hε, hT, hd, hP⟩ := ih (by omega)
    have hδ := hθ m (by omega)
    have hR := hΦ.1 hδ
    obtain ⟨y, z, hy, hz, hδy, hδz⟩ : ∃ y z, y ∈ T ∧ z ∉ T ∧ θ m y ≠ 0 ∧ θ m z ≠ 0 := by
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · obtain ⟨z, hz, hδz⟩ := ggDRootSet_exists_ne hR hy₀
        refine ⟨y₀, z, (hT y₀).2 (Or.inl rfl), fun h => ?_, hy₀, hδz⟩
        rcases (hT z).1 h with h | ⟨j, hj, -⟩
        · exact hz h
        · exact absurd hj (Nat.not_lt_zero _)
      obtain ⟨y, z, hγy, hδy, hδz, hγz⟩ := hadj (m - 1) (by omega)
      rw [Nat.sub_add_cancel hm0] at hδy hδz
      have hz0 : ∀ j < m, θ j z = 0 := fun j hj => by
        rcases Nat.lt_or_ge (j + 1) m with hj' | hj'
        · exact (hfar j m (by omega) hj' z).resolve_right hδz
        · obtain rfl : j = m - 1 := by omega
          exact hγz
      refine ⟨y, z, (hT y).2 (Or.inr ⟨m - 1, by omega, hγy⟩), fun h => ?_, hδy, hδz⟩
      rcases (hT z).1 h with h | ⟨j, hj, hj'⟩
      · exact hy₀ (h ▸ hz0 0 hm0)
      · exact hj' (hz0 j hj)
    obtain ⟨ε', hε'T, hε', hd', hP'⟩ := step hΦ hε hP hδ hy hz hδy hδz
    refine ⟨insert z T, ε', by rw [Finset.card_insert_of_notMem hz, hc], hε', fun c => ?_,
      fun j hj => ?_, hP'⟩
    · rw [Finset.mem_insert, hT]
      constructor
      · rintro (h | h | ⟨j, hj, h⟩)
        · exact Or.inr ⟨m, by omega, h ▸ hδz⟩
        · exact Or.inl h
        · exact Or.inr ⟨j, by omega, h⟩
      · rintro (h | ⟨j, hj, h⟩)
        · exact Or.inr (Or.inl h)
        rcases Nat.lt_or_ge j m with hjm | hjm
        · exact Or.inr (Or.inr ⟨j, hjm, h⟩)
        obtain rfl : j = m := by omega
        by_cases hcz : c = z
        · exact Or.inl hcz
        have hcy : c = y := by
          by_contra hcy
          exact h (ggDRootSet_eq_zero hR (ne_of_mem_of_not_mem hy hz) hδy hδz hcy hcz)
        exact Or.inr ((hT c).1 (hcy ▸ hy))
    · rcases Nat.lt_or_ge j m with hjm | hjm
      · rw [← hd j hjm]
        unfold ggDDot
        refine Finset.sum_congr rfl fun c _ => ?_
        by_cases h : θ j c = 0
        · rw [h, mul_zero, mul_zero]
        · rw [hε'T c ((hT c).2 (Or.inr ⟨j, hjm, h⟩))]
      · obtain rfl : j = m := by omega
        exact hd'

end CFSG.StandardType

end
