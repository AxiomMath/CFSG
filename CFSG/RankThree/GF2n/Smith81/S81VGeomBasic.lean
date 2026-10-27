module

public import CFSG.RankThree.GF2n.Smith81.S81VOrth

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module

variable {F : Type} [Field F] {σ : F ≃+* F}

structure ClosedPts (σ : F ≃+* F) (S : Set (Fin 6 → F)) : Prop where
  iso : ∀ x ∈ S, x ≠ 0 ∧ herm σ x x = 0
  smul : ∀ x ∈ S, ∀ c : F, c ≠ 0 → c • x ∈ S
  secant : ∀ x ∈ S, ∀ y ∈ S, herm σ x y ≠ 0 → ∀ z : Fin 6 → F, z ≠ 0 → herm σ z z = 0 →
    z ∈ Submodule.span F {x, y} → z ∈ S

theorem isTotIso_span_pair {x y : Fin 6 → F} (hσ : ∀ c, σ (σ c) = c) (hx : herm σ x x = 0)
    (hy : herm σ y y = 0) (hxy : herm σ x y = 0) : IsTotIso σ (Submodule.span F {x, y}) := by
  have hyx : herm σ y x = 0 := herm_eq_zero_comm σ hσ hxy
  intro u hu v hv
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hu
  obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hv
  simp [hx, hy, hxy, hyx]

theorem noTI_of_nonDeg_three (hσ : ∀ c, σ (σ c) = c) {U : Submodule F (Fin 6 → F)}
    (hU : NonDeg σ U) (h3 : finrank F U = 3) {L : Submodule F (Fin 6 → F)} (hL : L ≤ U)
    (h2 : finrank F L = 2) : ¬ IsTotIso σ L := by
  intro hti
  have hle : L ≤ U ⊓ orth σ L := by
    intro v hv
    refine Submodule.mem_inf.mpr ⟨hL hv, ?_⟩
    rw [mem_orth]
    intro w hw
    exact hti w hw v hv
  have hmono := Submodule.finrank_mono hle
  have hd := finrank_inf_orth hσ hU hL
  omega

theorem herm_ne_zero_of_noTI (hσ : ∀ c, σ (σ c) = c) {U : Submodule F (Fin 6 → F)}
    (hno : ∀ L ≤ U, finrank F L = 2 → ¬ IsTotIso σ L) {x y : Fin 6 → F} (hx : x ∈ U) (hy : y ∈ U)
    (hx0 : x ≠ 0) (hyx : y ∉ Submodule.span F {x}) (hxi : herm σ x x = 0)
    (hyi : herm σ y y = 0) : herm σ x y ≠ 0 := by
  intro hxy
  have hti : IsTotIso σ (Submodule.span F {x, y}) := isTotIso_span_pair hσ hxi hyi hxy
  have hle : Submodule.span F {x, y} ≤ U :=
    Submodule.span_le.mpr (Set.insert_subset_iff.mpr ⟨hx, Set.singleton_subset_iff.mpr hy⟩)
  have hli : LinearIndependent F ![x, y] :=
    (LinearIndependent.pair_iff' hx0).mpr fun a ha =>
      hyx (Submodule.mem_span_singleton.mpr ⟨a, ha⟩)
  have hfin : finrank F (Submodule.span F {x, y}) = 2 := by
    have h := finrank_span_eq_card hli
    rw [Matrix.range_cons_cons_empty x y ![], Fintype.card_fin] at h
    exact h
  exact hno _ hle hfin hti

end CFSG.RankThree.GF2n.Smith81.S81V
