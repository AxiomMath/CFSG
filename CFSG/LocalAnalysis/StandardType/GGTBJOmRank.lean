module

public import CFSG.LocalAnalysis.StandardType.GGTBJOmBlockZ

public section

open Module Multiplicative QuadraticMap

namespace CFSG.StandardType

namespace OrthTorus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p r : ℕ} {A : Subgroup (V ≃ₗ[K] V)}

private theorem finrank_iSup_pieces_le (Δ : TBJOmData Q p A r) :
    finrank K ↥(⨆ j, Δ.F.U j) ≤ 2 * r := by
  classical
  have key : ∀ s : Finset (Fin r), finrank K ↥(s.sup Δ.F.U) ≤ 2 * s.card := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sup_insert, Finset.card_insert_of_notMem ha]
      calc finrank K ↥(Δ.F.U a ⊔ s.sup Δ.F.U)
          ≤ finrank K ↥(Δ.F.U a) + finrank K ↥(s.sup Δ.F.U) :=
            Submodule.finrank_add_le_finrank_add_finrank _ _
        _ ≤ 2 + 2 * s.card := by rw [Δ.finrank_piece a]; omega
        _ = 2 * (s.card + 1) := by ring
  have h := key Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at h
  rwa [← Finset.sup_univ_eq_iSup]

theorem TBJOmData.finrank_le_two_mul_of_noFixed (Δ : TBJOmData Q p A r)
    (hnf : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0) : finrank K V ≤ 2 * r := by
  classical
  let W : Submodule K V := ⨆ j, Δ.F.U j
  let Φ : V →ₗ[K] Module.Dual K W :=
    (LinearMap.lcomp K K W.subtype).comp (QuadraticMap.polarBilin Q).flip
  have hΦ : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    apply hnf v
    intro a ha
    rw [← Δ.F.range] at ha
    obtain ⟨s, rfl⟩ := ha
    rw [Δ.F.fix]
    intro j _ u hu
    have h1 : ∀ w : W, QuadraticMap.polarBilin Q (w : V) v = 0 := fun w =>
      LinearMap.congr_fun hv w
    have hmem : u ∈ W := Submodule.mem_iSup_of_mem j hu
    have h2 := h1 ⟨u, hmem⟩
    simpa [QuadraticMap.polarBilin_apply_apply] using h2
  have h3 := LinearMap.finrank_le_finrank_of_injective hΦ
  rw [Subspace.dual_finrank_eq] at h3
  exact h3.trans (finrank_iSup_pieces_le Δ)

end OrthTorus

end CFSG.StandardType

end
