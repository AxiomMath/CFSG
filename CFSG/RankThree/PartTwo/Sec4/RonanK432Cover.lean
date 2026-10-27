module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Sylow

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

theorem sq_sq_eq_of_pow_three {G : Type} [Group G] {y : G} (h : y ^ 3 = 1) : (y ^ 2) ^ 2 = y := by
  rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, h, one_mul]

theorem listRow_of_cover {S : Type} [Group S] [Finite S] (R : Set S)
    (hR : ∀ c ∈ R, orderOf c = 3)
    (hcov : ∀ s : S, orderOf s = 3 →
      ∃ k c : S, c ∈ R ∧ ∃ e : ℕ, (e = 1 ∨ e = 2) ∧ k * c ^ e * k⁻¹ = s)
    (hw : ∀ c ∈ R, ∃ g : S, (g * c * g⁻¹) * c = c * (g * c * g⁻¹) ∧
      g * c * g⁻¹ ∉ Subgroup.zpowers c) : ListRow S := by
  refine listRow_of_class_exists (κ := R × Bool)
    (fun p => if p.2 then (p.1 : S) else (p.1 : S) ^ 2) ?_ ?_ ?_
  · intro s hs
    obtain ⟨k, c, hc, e, he, rfl⟩ := hcov s hs
    rcases he with rfl | rfl
    · exact ⟨(⟨c, hc⟩, true), k, by simp⟩
    · exact ⟨(⟨c, hc⟩, false), k, by simp⟩
  · rintro ⟨⟨c, hc⟩, b⟩
    have h3 : c ^ 3 = 1 := by rw [← hR c hc]; exact pow_orderOf_eq_one c
    cases b
    · simp only [Bool.false_eq_true, if_false]
      rw [← pow_mul, mul_comm, pow_mul, h3, one_pow]
    · simpa using h3
  · rintro ⟨⟨c, hc⟩, b⟩ _
    obtain ⟨g, hcomm, hnot⟩ := hw c hc
    have h3 : c ^ 3 = 1 := by rw [← hR c hc]; exact pow_orderOf_eq_one c
    have hy3 : (g * c * g⁻¹) ^ 3 = 1 := by
      rw [show (g * c * g⁻¹) ^ 3 = g * c ^ 3 * g⁻¹ by simp [conj_pow], h3]; group
    have hcinv : c⁻¹ ∈ Subgroup.zpowers c := inv_mem (Subgroup.mem_zpowers c)
    refine ⟨g, ?_⟩
    cases b
    · simp only [Bool.false_eq_true, if_false]
      have hy2 : g * c ^ 2 * g⁻¹ = (g * c * g⁻¹) ^ 2 := by simp [conj_pow]
      rw [hy2]
      have hc2 : c ^ 2 ∈ Subgroup.zpowers c := Subgroup.pow_mem _ (Subgroup.mem_zpowers c) 2
      have hnot2 : (g * c * g⁻¹) ^ 2 ∉ Subgroup.zpowers c := fun hmem => hnot (by
        rw [← sq_sq_eq_of_pow_three hy3]
        exact Subgroup.pow_mem _ hmem 2)
      refine ⟨(show Commute (g * c * g⁻¹) c from hcomm).pow_pow 2 2, fun h => hnot2 (by rw [h]; exact hc2),
        fun h => hnot2 (by rw [h]; exact inv_mem hc2), fun h => hnot2 (by rw [h]; exact one_mem _)⟩
    · simp only [if_true]
      exact ⟨hcomm, fun h => hnot (by rw [h]; exact Subgroup.mem_zpowers c),
        fun h => hnot (by rw [h]; exact hcinv), fun h => hnot (by rw [h]; exact one_mem _)⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
