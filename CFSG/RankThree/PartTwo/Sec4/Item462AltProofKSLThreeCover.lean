module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

open CFSG.RankThree.PartTwo.Sec4

@[expose] def CoverLift (X : Type) [Group X] (π : Bool) (p f : ℕ) (K : Type) [Field K] : Prop :=
  ∃ φ : slPi π 3 (p ^ f) K →* X, Function.Surjective φ ∧
    (Subgroup.center X).comap φ = Subgroup.center (slPi π 3 (p ^ f) K) ∧
    ∀ β : MulAut X, β ^ 3 = 1 → ∃ β' : MulAut (slPi π 3 (p ^ f) K), β' ^ 3 = 1 ∧
      ∀ s, φ (β' s) = β (φ s)

theorem coverLift_of_mulEquiv_sl {X : Type} [Group X] {π : Bool} {p f : ℕ} {K : Type} [Field K]
    (e : X ≃* slPi π 3 (p ^ f) K) : CoverLift X π p f K := by
  refine ⟨e.symm.toMonoidHom, e.symm.surjective, ?_, fun β hβ => ?_⟩
  · ext s
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, Subgroup.mem_center_iff]
    constructor
    · intro h t
      obtain ⟨u, rfl⟩ := e.surjective t
      apply e.symm.injective
      rw [map_mul, map_mul, MulEquiv.symm_apply_apply]
      exact h u
    · intro h g
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact h (e g)
  · refine ⟨MulAut.congr e β, by rw [← map_pow, hβ, map_one], fun s => ?_⟩
    simp [MulAut.congr_apply]

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

end
