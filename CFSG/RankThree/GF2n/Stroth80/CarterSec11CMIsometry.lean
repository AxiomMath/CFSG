module

public import CFSG.RankThree.GF2n.Stroth80.GlobalModelData

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G]
  {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal]
  {K : Type} [Field K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem H0_le_M' : H0 M Z ≤ M := fun _ hx => hx.1

theorem exists_unique_action_isometry (hD : GlobalModelData M Q Z γ M₀) (h : ↥(H0 M Z)) :
    ∃! T : M₀.E ≃ₗ[K] M₀.E,
      (∀ x ∈ Q, M₀.π ((h : G) * x * (h : G)⁻¹) = T (M₀.π x)) ∧
      (∀ e, M₀.Qf (T e) = M₀.Qf e) ∧
      (∀ e f, M₀.B (T e) (T f) = M₀.B e f) := by
  obtain ⟨T, hTπ, hTQ, hTB⟩ := hD.linear_of_centralizes (H0_le_M' h.2) (fun z hz => by
    have hc := Subgroup.mem_centralizer_iff.mp h.2.2 z hz
    rw [← hc]; group)
  refine ⟨T, ⟨hTπ, hTQ, hTB⟩, ?_⟩
  rintro T' ⟨hT'π, -, -⟩
  refine LinearEquiv.ext fun e => ?_
  obtain ⟨x, hx, rfl⟩ := M₀.π_surj e
  rw [← hT'π x hx, ← hTπ x hx]

noncomputable def h0Isometry (hD : GlobalModelData M Q Z γ M₀) (h : ↥(H0 M Z)) :
    M₀.E ≃ₗ[K] M₀.E :=
  (exists_unique_action_isometry hD h).choose

theorem h0Isometry_π (hD : GlobalModelData M Q Z γ M₀) (h : ↥(H0 M Z)) :
    ∀ x ∈ Q, M₀.π ((h : G) * x * (h : G)⁻¹) = h0Isometry hD h (M₀.π x) :=
  ((exists_unique_action_isometry hD h).choose_spec).1.1

theorem h0Isometry_Qf (hD : GlobalModelData M Q Z γ M₀) (h : ↥(H0 M Z)) (e : M₀.E) :
    M₀.Qf (h0Isometry hD h e) = M₀.Qf e :=
  ((exists_unique_action_isometry hD h).choose_spec).1.2.1 e

theorem h0Isometry_B (hD : GlobalModelData M Q Z γ M₀) (h : ↥(H0 M Z)) (e f : M₀.E) :
    M₀.B (h0Isometry hD h e) (h0Isometry hD h f) = M₀.B e f :=
  ((exists_unique_action_isometry hD h).choose_spec).1.2.2 e f

theorem eq_h0Isometry_of_π (hD : GlobalModelData M Q Z γ M₀) (h : ↥(H0 M Z))
    {T : M₀.E ≃ₗ[K] M₀.E}
    (hT : ∀ x ∈ Q, M₀.π ((h : G) * x * (h : G)⁻¹) = T (M₀.π x)) :
    T = h0Isometry hD h := by
  refine LinearEquiv.ext fun e => ?_
  obtain ⟨x, hx, rfl⟩ := M₀.π_surj e
  rw [← hT x hx, ← h0Isometry_π hD h x hx]

theorem isometry_of_π (hD : GlobalModelData M Q Z γ M₀) (h : ↥(H0 M Z))
    {T : M₀.E ≃ₗ[K] M₀.E}
    (hT : ∀ x ∈ Q, M₀.π ((h : G) * x * (h : G)⁻¹) = T (M₀.π x)) :
    (∀ e, M₀.Qf (T e) = M₀.Qf e) ∧ (∀ e f, M₀.B (T e) (T f) = M₀.B e f) := by
  rw [eq_h0Isometry_of_π hD h hT]
  exact ⟨h0Isometry_Qf hD h, h0Isometry_B hD h⟩

end CFSG.RankThree.GF2n.Stroth80
