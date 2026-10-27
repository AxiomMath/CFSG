module

public import CFSG.OddTranspositions.SevenOne

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

open scoped Pointwise

variable {G : Type} [Group G] {D : Set G}

private theorem conj_mem_smul {α : Set G} (g : G) {a : G} (ha : a ∈ α) :
    g * a * g⁻¹ ∈ (ConjAct.toConjAct g) • α := by
  have h := Set.smul_mem_smul_set (a := ConjAct.toConjAct g) ha
  rwa [ConjAct.toConjAct_smul] at h

theorem Aalpha_nonempty (hS : Setup G D) {α : Set G} (hα : IsBlock D α) :
    (Aalpha D α).Nonempty := by
  classical
  by_contra hempty
  obtain ⟨hαD, ⟨a₀, ha₀⟩, hαne, -⟩ := hα
  have hcomm : ∀ g : ConjAct G, g • α ≠ α → ∀ a ∈ α, ∀ b ∈ g • α, Commute a b := by
    intro g hg a ha b hb
    have hp : g • α ∈ perp D α := by
      by_contra hp
      exact hempty ⟨g • α, ⟨g, rfl⟩, hp⟩
    rcases hp with hp | hp
    · exact hp.2.2.2 a ha b hb
    · exact absurd hp hg
  have hout : ∀ d ∈ D, d ∉ α → ∀ a ∈ α, Commute a d := by
    intro d hd hdα a ha
    obtain ⟨g, hg⟩ := isConj_iff.mp (hS.isConj (hαD ha₀) hd)
    have hdg : d ∈ (ConjAct.toConjAct g) • α := hg ▸ conj_mem_smul g ha₀
    exact hcomm _ (fun h => hdα (h ▸ hdg)) a ha d hdg
  have hnorm : (Subgroup.closure α).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hS.gen, Subgroup.closure_le]
    intro d hd
    by_cases hdα : d ∈ α
    · exact Subgroup.le_normalizer (Subgroup.subset_closure hdα)
    · have hle : Subgroup.closure α ≤ Subgroup.centralizer ({d} : Set G) := by
        rw [Subgroup.closure_le]
        intro a ha
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        exact (hout d hd hdα a ha).eq
      have hc : ∀ h ∈ Subgroup.closure α, d * h * d⁻¹ = h := fun h hh => by
        rw [← Subgroup.mem_centralizer_singleton_iff.mp (hle hh), mul_inv_cancel_right]
      rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        rw [hc h hh]
        exact hh
      · intro hh
        have h1 := hc _ hh
        have h2 : h = d * h * d⁻¹ := by
          calc h = d⁻¹ * (d * h * d⁻¹) * d := by group
            _ = d⁻¹ * (d * (d * h * d⁻¹) * d⁻¹) * d := by rw [h1]
            _ = d * h * d⁻¹ := by group
        rw [h2]
        exact hh
  obtain ⟨g, hg⟩ : ∃ g : G, (ConjAct.toConjAct g) • α ≠ α := by
    by_contra hno
    have h : ∀ g : G, (ConjAct.toConjAct g) • α = α := fun g => by
      by_contra hne
      exact hno ⟨g, hne⟩
    apply hαne
    refine Set.Subset.antisymm hαD fun d hd => ?_
    obtain ⟨g, hg⟩ := isConj_iff.mp (hS.isConj (hαD ha₀) hd)
    rw [← h g, ← hg]
    exact conj_mem_smul g ha₀
  have hαcomm : ∀ a ∈ α, ∀ c ∈ α, Commute a c := by
    intro a ha c hc
    have hb : g * a * g⁻¹ ∈ (ConjAct.toConjAct g) • α := conj_mem_smul g ha
    have hc' : g * c * g⁻¹ ∈ Subgroup.closure α :=
      hnorm.conj_mem c (Subgroup.subset_closure hc) g
    have hle : Subgroup.closure α ≤ Subgroup.centralizer ({g * a * g⁻¹} : Set G) := by
      rw [Subgroup.closure_le]
      intro x hx
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (hcomm _ hg x hx _ hb).eq
    exact ((Commute.conj_iff g).mp (Subgroup.mem_centralizer_singleton_iff.mp (hle hc'))).symm
  have hcen : ∀ x : G, Commute a₀ x := by
    intro x
    have hle : Subgroup.closure D ≤ Subgroup.centralizer ({a₀} : Set G) := by
      rw [Subgroup.closure_le]
      intro d hd
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      by_cases hdα : d ∈ α
      · exact (hαcomm a₀ ha₀ d hdα).eq.symm
      · exact (hout d hd hdα a₀ ha₀).eq.symm
    rw [hS.gen] at hle
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top x))).symm
  apply hαne
  refine Set.Subset.antisymm hαD fun d hd => ?_
  obtain ⟨x, hx⟩ := isConj_iff.mp (hS.isConj (hαD ha₀) hd)
  have hd' : d = a₀ := by
    rw [← hx, ← (hcen x).eq, mul_inv_cancel_right]
  rw [hd']
  exact ha₀

theorem no_firstKind_of_H' [Finite G] (hC : HypothesisC D)
    (hH : ∀ x w y : G, x ∈ DalphaStar D hC.alpha → w ∈ DalphaStar D hC.alpha →
      y ∈ DalphaStar D hC.alpha → IsTriangle D x w y →
      ¬ (Odd (orderOf (x * y * w)) ∧ 1 < orderOf (x * y * w))) :
    ∀ x w y : G, IsTriangle D x w y →
      ¬ (Odd (orderOf (x * y * w)) ∧ 1 < orderOf (x * y * w)) :=
  no_firstKind_of_H hC hH (Aalpha_nonempty hC.setup hC.isBlock_alpha)

end CFSG.OddTranspositions
