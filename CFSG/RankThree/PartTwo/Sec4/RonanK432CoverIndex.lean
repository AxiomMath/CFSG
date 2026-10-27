module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Cover
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Count

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

theorem index_centralizer_eq_of_isConj {G : Type} [Group G] {a b : G} (h : IsConj a b) :
    (Subgroup.centralizer ({a} : Set G)).index = (Subgroup.centralizer ({b} : Set G)).index := by
  rw [Subgroup.index_centralizer_eq_ncard, Subgroup.index_centralizer_eq_ncard,
    isConj_iff_conjugatesOf_eq.mp h]

theorem centralizer_sq_eq_of_pow_three {S : Type} [Group S] {c : S} (h : c ^ 3 = 1) :
    Subgroup.centralizer ({c ^ 2} : Set S) = Subgroup.centralizer ({c} : Set S) := by
  ext x
  simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  constructor
  · intro hx
    have h2 : Commute ((c ^ 2) ^ 2) x := (show Commute (c ^ 2) x from hx).pow_left 2
    rw [sq_sq_eq_of_pow_three h] at h2
    exact h2
  · intro hx
    exact (show Commute c x from hx).pow_left 2

theorem not_weaklyClosed_of_class_witness {S : Type} [Group S] {r w h z : S} (hr3 : r ^ 3 = 1)
    (hzk : z = h * r * h⁻¹) (hc : (w * r * w⁻¹) * r = r * (w * r * w⁻¹))
    (hn1 : w * r * w⁻¹ ≠ r) (hn2 : w * r * w⁻¹ ≠ r⁻¹) (hn3 : w * r * w⁻¹ ≠ 1) :
    ¬ WeaklyClosed (Subgroup.zpowers z) := by
  subst hzk
  refine not_weaklyClosed_of_commute_conj (g := h * w * h⁻¹) ?_ ?_
  · calc h * w * h⁻¹ * (h * r * h⁻¹) * (h * w * h⁻¹)⁻¹ * (h * r * h⁻¹)
        = h * ((w * r * w⁻¹) * r) * h⁻¹ := by group
      _ = h * (r * (w * r * w⁻¹)) * h⁻¹ := by rw [hc]
      _ = (h * r * h⁻¹) * (h * w * h⁻¹ * (h * r * h⁻¹) * (h * w * h⁻¹)⁻¹) := by group
  · intro hmem
    have e1 : h * w * h⁻¹ * (h * r * h⁻¹) * (h * w * h⁻¹)⁻¹ =
        h * (w * r * w⁻¹) * h⁻¹ := by group
    rw [e1] at hmem
    rcases mem_zpowers_cases_of_pow_three (q := h * r * h⁻¹)
      (by rw [show (h * r * h⁻¹) ^ 3 = h * r ^ 3 * h⁻¹ by simp [conj_pow], hr3]; group)
      hmem with h' | h' | h'
    · apply hn3
      have := congrArg (fun t => h⁻¹ * t * h) h'
      simpa [mul_assoc] using this
    · apply hn1
      have := congrArg (fun t => h⁻¹ * t * h) h'
      simpa [mul_assoc] using this
    · apply hn2
      have := congrArg (fun t => h⁻¹ * t * h) h'
      simpa [mul_assoc] using this

theorem listRow_of_class_or_index {S : Type} [Group S] [Finite S] {κ : Type} (r : κ → S)
    (hcl : ∀ z : S, orderOf z = 3 → ∃ k : κ, ∃ h : S, z = h * r k * h⁻¹)
    (hr3 : ∀ k, r k ^ 3 = 1)
    (hw : ∀ k, r k ≠ 1 → 3 ∣ (Subgroup.centralizer ({r k} : Set S)).index ∨
      ∃ w : S, (w * r k * w⁻¹) * r k = r k * (w * r k * w⁻¹) ∧
        w * r k * w⁻¹ ≠ r k ∧ w * r k * w⁻¹ ≠ (r k)⁻¹ ∧ w * r k * w⁻¹ ≠ 1) : ListRow S := by
  refine listRow_of_forall_not_weaklyClosed fun z hz => ?_
  obtain ⟨k, h, hzk⟩ := hcl z hz
  have hne : r k ≠ 1 := by
    intro h1
    rw [h1] at hzk
    rw [hzk] at hz
    simp at hz
  rcases hw k hne with h3 | ⟨w, hc, hn1, hn2, hn3⟩
  · refine not_weaklyClosed_of_three_dvd_index hz ?_
    have hconj : IsConj (r k) z := isConj_iff.mpr ⟨h, hzk.symm⟩
    rw [← index_centralizer_eq_of_isConj hconj]
    exact h3
  · exact not_weaklyClosed_of_class_witness (hr3 k) hzk hc hn1 hn2 hn3

theorem listRow_of_cover_or_index {S : Type} [Group S] [Finite S] (R : Set S)
    (hR : ∀ c ∈ R, orderOf c = 3)
    (hcov : ∀ s : S, orderOf s = 3 →
      ∃ k c : S, c ∈ R ∧ ∃ e : ℕ, (e = 1 ∨ e = 2) ∧ k * c ^ e * k⁻¹ = s)
    (hw : ∀ c ∈ R, 3 ∣ (Subgroup.centralizer ({c} : Set S)).index ∨
      ∃ g : S, (g * c * g⁻¹) * c = c * (g * c * g⁻¹) ∧
        g * c * g⁻¹ ∉ Subgroup.zpowers c) : ListRow S := by
  refine listRow_of_class_or_index (κ := R × Bool)
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
    have h3 : c ^ 3 = 1 := by rw [← hR c hc]; exact pow_orderOf_eq_one c
    rcases hw c hc with hi | ⟨g, hcomm, hnot⟩
    · left
      cases b
      · simp only [Bool.false_eq_true, if_false]
        rw [centralizer_sq_eq_of_pow_three h3]
        exact hi
      · simpa using hi
    · right
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
        refine ⟨(show Commute (g * c * g⁻¹) c from hcomm).pow_pow 2 2,
          fun h => hnot2 (by rw [h]; exact hc2),
          fun h => hnot2 (by rw [h]; exact inv_mem hc2), fun h => hnot2 (by rw [h]; exact one_mem _)⟩
      · simp only [if_true]
        exact ⟨hcomm, fun h => hnot (by rw [h]; exact Subgroup.mem_zpowers c),
          fun h => hnot (by rw [h]; exact hcinv), fun h => hnot (by rw [h]; exact one_mem _)⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
