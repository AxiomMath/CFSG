module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r899Stab
import CFSG.LocalAnalysis.UniquenessCase.UC22R8100BFrat
import CFSG.LocalAnalysis.UniquenessCase.UC22P22d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.ABGLocalTools Subgroup

section Cycle

variable {G : Type} [Group G] [Finite G]

theorem uc22r899c4_exists_cycle {M L K₁ K₂ K₃ : Subgroup G} (hc3 : (conjSetOf M L).ncard = 3)
    (h₁ : K₁ ∈ conjSetOf M L) (h₂ : K₂ ∈ conjSetOf M L) (h₃ : K₃ ∈ conjSetOf M L)
    (h12 : K₁ ≠ K₂) (h13 : K₁ ≠ K₃) (h23 : K₂ ≠ K₃) :
    ∃ w ∈ M, K₁.map (MulAut.conj w).toMonoidHom = K₂ ∧
      K₂.map (MulAut.conj w).toMonoidHom = K₃ ∧ K₃.map (MulAut.conj w).toMonoidHom = K₁ := by
  have hS : ∀ K ∈ conjSetOf M L, K = K₁ ∨ K = K₂ ∨ K = K₃ := by
    have hsub : ({K₁, K₂, K₃} : Set (Subgroup G)) ⊆ conjSetOf M L := by
      intro K hK
      rcases hK with rfl | rfl | hK
      · exact h₁
      · exact h₂
      · rw [Set.mem_singleton_iff.1 hK]
        exact h₃
    have heq := Set.eq_of_subset_of_ncard_le hsub
      (by rw [hc3, Set.ncard_eq_three.2 ⟨K₁, K₂, K₃, h12, h13, h23, rfl⟩]) (Set.toFinite _)
    intro K hK
    rw [← heq] at hK
    exact hK
  have hmem : ∀ g ∈ M, ∀ K ∈ conjSetOf M L, K.map (MulAut.conj g).toMonoidHom = K₁ ∨
      K.map (MulAut.conj g).toMonoidHom = K₂ ∨ K.map (MulAut.conj g).toMonoidHom = K₃ :=
    fun g hg K hK => hS _ (uc22r899_map_conj_mem hg hK)
  have hinj : ∀ (g : G) {A B : Subgroup G}, A.map (MulAut.conj g).toMonoidHom =
      B.map (MulAut.conj g).toMonoidHom → A = B := fun g _ _ h =>
    Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective h
  have htr : ∀ {A B : Subgroup G}, A ∈ conjSetOf M L → B ∈ conjSetOf M L →
      ∃ g ∈ M, A.map (MulAut.conj g).toMonoidHom = B := by
    rintro A B ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    refine ⟨b * a⁻¹, M.mul_mem hb (M.inv_mem ha), ?_⟩
    rw [uc22p22d_map_conj_map_conj, inv_mul_cancel_right]
  obtain ⟨g, hg, hg1⟩ := htr h₁ h₂
  rcases hmem g hg K₂ h₂ with hg2 | hg2 | hg2
  ·
    have hg3 : K₃.map (MulAut.conj g).toMonoidHom = K₃ := by
      rcases hmem g hg K₃ h₃ with e | e | e
      · exact absurd (hinj g (e.trans hg2.symm)) h23.symm
      · exact absurd (hinj g (e.trans hg1.symm)) h13.symm
      · exact e
    obtain ⟨u, hu, hu2⟩ := htr h₂ h₃
    rcases hmem u hu K₃ h₃ with hu3 | hu3 | hu3
    ·
      have hu1 : K₁.map (MulAut.conj u).toMonoidHom = K₂ := by
        rcases hmem u hu K₁ h₁ with e | e | e
        · exact absurd (hinj u (e.trans hu3.symm)) h13
        · exact e
        · exact absurd (hinj u (e.trans hu2.symm)) h12
      exact ⟨u, hu, hu1, hu2, hu3⟩
    ·
      have hu1 : K₁.map (MulAut.conj u).toMonoidHom = K₁ := by
        rcases hmem u hu K₁ h₁ with e | e | e
        · exact e
        · exact absurd (hinj u (e.trans hu3.symm)) h13
        · exact absurd (hinj u (e.trans hu2.symm)) h12
      refine ⟨g * u, M.mul_mem hg hu, ?_, ?_, ?_⟩
      · rw [← uc22p22d_map_conj_map_conj K₁ u g, hu1, hg1]
      · rw [← uc22p22d_map_conj_map_conj K₂ u g, hu2, hg3]
      · rw [← uc22p22d_map_conj_map_conj K₃ u g, hu3, hg2]
    · exact absurd (hinj u (hu3.trans hu2.symm)) h23.symm
  · exact absurd (hinj g (hg2.trans hg1.symm)) h12.symm
  ·
    have hg3 : K₃.map (MulAut.conj g).toMonoidHom = K₁ := by
      rcases hmem g hg K₃ h₃ with e | e | e
      · exact e
      · exact absurd (hinj g (e.trans hg1.symm)) h13.symm
      · exact absurd (hinj g (e.trans hg2.symm)) h23.symm
    exact ⟨g, hg, hg1, hg2, hg3⟩

end Cycle

section Shift

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem uc22r899c4_shift_step {q : ℕ} [Fact q.Prime] {K S : Fin 3 → Subgroup Γ}
    (hS : ∀ i, IsSylowOf q (S i) (K i))
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, x * y = y * x) {w : Γ}
    (hwK : ∀ i, (K i).map (MulAut.conj w).toMonoidHom = K (i + 1)) (j : Fin 3) :
    ∃ w' : Γ, (∀ i, (K i).map (MulAut.conj w').toMonoidHom = K (i + 1)) ∧
      (S j).map (MulAut.conj w').toMonoidHom = S (j + 1) ∧
      ∀ i, i ≠ j →
        (S i).map (MulAut.conj w').toMonoidHom = (S i).map (MulAut.conj w).toMonoidHom := by
  have hSyl : IsSylowOf q ((S j).map (MulAut.conj w).toMonoidHom) (K (j + 1)) := by
    rw [← hwK j]
    exact isSylowOf_of_card (Subgroup.map_mono (hS j).le)
      (by rw [Subgroup.card_map_of_injective (MulAut.conj w).injective,
        Subgroup.card_map_of_injective (MulAut.conj w).injective, (hS j).card_eq])
  obtain ⟨k, hk, hkx⟩ := uc22r8100b_exists_conj hSyl (hS (j + 1))
  have hkc : ∀ m, m ≠ j + 1 → k ∈ centralizer (K m : Set Γ) := fun m hm =>
    Subgroup.mem_centralizer_iff.2 fun y hy => (hcomm (j + 1) m hm.symm k hk y hy).symm
  have hkN : ∀ m, k ∈ normalizer (K m : Set Γ) := by
    intro m
    by_cases hm : m = j + 1
    · subst hm
      exact Subgroup.le_normalizer hk
    · exact Subgroup.centralizer_le_normalizer _ (hkc m hm)
  refine ⟨k * w, fun i => ?_, ?_, fun i hij => ?_⟩
  · rw [← uc22p22d_map_conj_map_conj, hwK i]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.1 (hkN (i + 1))
  · rw [← uc22p22d_map_conj_map_conj]
    ext x
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, hkx]
  ·
    have hle : (S i).map (MulAut.conj w).toMonoidHom ≤ K (i + 1) := by
      rw [← hwK i]
      exact Subgroup.map_mono (hS i).le
    have hk' : k ∈ normalizer (((S i).map (MulAut.conj w).toMonoidHom : Subgroup Γ) : Set Γ) :=
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun y hy =>
        (Subgroup.mem_centralizer_iff.1 (hkc (i + 1) fun h => hij (add_right_cancel h)) y
          (hle hy)))
    rw [← uc22p22d_map_conj_map_conj]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.1 hk'

theorem uc22r899c4_exists_shift {q : ℕ} [Fact q.Prime] {K S : Fin 3 → Subgroup Γ}
    (hS : ∀ i, IsSylowOf q (S i) (K i))
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, x * y = y * x) {w : Γ}
    (hwK : ∀ i, (K i).map (MulAut.conj w).toMonoidHom = K (i + 1)) :
    ∃ w' : Γ, (∀ i, (K i).map (MulAut.conj w').toMonoidHom = K (i + 1)) ∧
      ∀ i, (S i).map (MulAut.conj w').toMonoidHom = S (i + 1) := by
  obtain ⟨w₁, hK₁, h₁0, -⟩ := uc22r899c4_shift_step hS hcomm hwK 0
  obtain ⟨w₂, hK₂, h₂1, h₂⟩ := uc22r899c4_shift_step hS hcomm hK₁ 1
  obtain ⟨w₃, hK₃, h₃2, h₃⟩ := uc22r899c4_shift_step hS hcomm hK₂ 2
  have e0 : (S 0).map (MulAut.conj w₃).toMonoidHom = S (0 + 1) := by
    rw [h₃ 0 (by decide), h₂ 0 (by decide)]
    exact h₁0
  have e1 : (S 1).map (MulAut.conj w₃).toMonoidHom = S (1 + 1) := by
    rw [h₃ 1 (by decide)]
    exact h₂1
  refine ⟨w₃, hK₃, fun i => ?_⟩
  fin_cases i
  exacts [e0, e1, h₃2]

end Shift

end CFSG.LocalAnalysis.UniquenessCase.UC22
