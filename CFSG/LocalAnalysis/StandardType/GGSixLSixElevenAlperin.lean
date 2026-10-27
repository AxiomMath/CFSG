module

public import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion

public section

namespace CFSG.StandardType

open CFSG.RankTwoShapes

variable {G : Type} [Group G]

theorem exists_good_step_of_conj [Finite G] {p : ℕ} [Fact p.Prime] (S : Sylow p G)
    (Good : G → Prop) {y g : G} (hy : y ∈ (S : Subgroup G)) (hg : g⁻¹ * y * g ∈ (S : Subgroup G))
    (hgood : Good (g⁻¹ * y * g)) (hbad : ¬ Good y) :
    ∃ Q : Subgroup G, Q ≤ (S : Subgroup G) ∧ ∃ z ∈ Q, ∃ n ∈ Subgroup.normalizer (Q : Set G),
      ¬ Good z ∧ Good (n⁻¹ * z * n) ∧ ∃ c : G, z = c⁻¹ * y * c := by
  have hP : Subgroup.zpowers y ≤ (S : Subgroup G) := Subgroup.zpowers_le.2 hy
  have hPg : (Subgroup.zpowers y).map (MulAut.conj g⁻¹).toMonoidHom ≤ (S : Subgroup G) := by
    rw [MonoidHom.map_zpowers]
    exact Subgroup.zpowers_le.2 (by simpa using hg)
  obtain ⟨c, hc, hcg⟩ := alperin_centric_radical_fusion S hP hPg
  have hcy : c⁻¹ * y * c = g⁻¹ * y * g := hcg y (Subgroup.mem_zpowers y)
  have key : ∀ c : G, AlperinDecomposition p (S : Subgroup G) (Subgroup.zpowers y) c →
      Good (c⁻¹ * y * c) →
      ∃ Q : Subgroup G, Q ≤ (S : Subgroup G) ∧ ∃ z ∈ Q, ∃ n ∈ Subgroup.normalizer (Q : Set G),
        ¬ Good z ∧ Good (n⁻¹ * z * n) ∧ ∃ c : G, z = c⁻¹ * y * c := by
    intro c hc
    induction hc with
    | one =>
      intro h
      exact absurd (by simpa using h) hbad
    | @step c n Q _ hQ hyQ hn ih =>
      intro h
      by_cases hc' : Good (c⁻¹ * y * c)
      · exact ih hc'
      · refine ⟨Q, hQ.1, c⁻¹ * y * c, ?_, n, hn, hc', ?_, c, rfl⟩
        · exact hyQ ⟨y, Subgroup.mem_zpowers y, by simp⟩
        · have heq : (c * n)⁻¹ * y * (c * n) = n⁻¹ * (c⁻¹ * y * c) * n := by group
          rwa [heq] at h
  exact key c hc (hcy ▸ hgood)

end CFSG.StandardType
