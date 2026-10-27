module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitOmBlkFrame
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitOmInv

public section

namespace CFSG.StandardType

namespace WitOmBlk

open QuadraticMap Module OrdPNsOm CFSG.RankThree.OrthogonalInvolutions

variable {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

theorem even_finrank_of_nondeg [FiniteDimensional K V] (hQ : Q.polarBilin.Nondegenerate) :
    Even (finrank K V) :=
  LinearMap.BilinForm.IsAlt.even_finrank (B := polarBilin Q) (fun a => by
    rw [polarBilin_apply_apply, polar_self_charTwo]) hQ

omit [CharP K 2] in
theorem polar_commSpace_fixSpace (hQ : Q.polarBilin.Nondegenerate) {v : V ≃ₗ[K] V}
    (hO : v ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hvv : v * v = 1) {r c : V}
    (hr : r ∈ commSpace v) (hc : c ∈ fixSpace v) : polar Q r c = 0 := by
  rw [fixSpace_eq_orthogonal_commSpace hQ hO hvv, LinearMap.BilinForm.mem_orthogonal_iff] at hc
  exact hc r hr

theorem exists_compl_fix [FiniteDimensional K V] (hQ : Q.polarBilin.Nondegenerate)
    {v : V ≃ₗ[K] V} (hO : v ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hvv : v * v = 1) :
    ∃ W₀ : Submodule K V, W₀ ≤ fixSpace v ∧ SUTB.NondegOn (polarBilin Q) W₀ ∧
      finrank K W₀ + 2 * finrank K (commSpace v) = finrank K V := by
  have hRC : commSpace v ≤ fixSpace v := commSpace_le_fixSpace hvv
  obtain ⟨R', hR'⟩ := (commSpace v).exists_isCompl
  have hsup : commSpace v ⊔ R' ⊓ fixSpace v = fixSpace v := by
    rw [← sup_inf_assoc_of_le _ hRC, hR'.sup_eq_top, top_inf_eq]
  have hinf : commSpace v ⊓ (R' ⊓ fixSpace v) = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    have h1 : x ∈ commSpace v ⊓ R' := ⟨hx.1, hx.2.1⟩
    rw [hR'.inf_eq_bot] at h1
    exact h1
  have hdimC := finrank_commSpace_add_finrank_fixSpace v
  have hdimW : finrank K (commSpace v) + finrank K ↥(R' ⊓ fixSpace v) =
      finrank K (fixSpace v) := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (commSpace v) (R' ⊓ fixSpace v)
    rw [hsup, hinf, finrank_bot, add_zero] at h1
    omega
  refine ⟨R' ⊓ fixSpace v, inf_le_right, fun w hw hw' => ?_, by omega⟩
  have hwC : w ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) (fixSpace v) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro c hc
    rw [← hsup] at hc
    obtain ⟨r, hr, w', hw'', rfl⟩ := Submodule.mem_sup.mp hc
    change polarBilin Q (r + w') w = 0
    rw [map_add, LinearMap.add_apply, hw' w' hw'', add_zero, polarBilin_apply_apply]
    exact polar_commSpace_fixSpace hQ hO hvv hr hw.2
  have hwR : w ∈ commSpace v := by
    rwa [fixSpace_eq_orthogonal_commSpace hQ hO hvv,
      LinearMap.BilinForm.orthogonal_orthogonal hQ (QuadraticMap.isSymm_polarBilin Q).isRefl] at hwC
  have h1 : w ∈ commSpace v ⊓ (R' ⊓ fixSpace v) := ⟨hwR, hw⟩
  rw [hinf] at h1
  exact h1

theorem exists_frame_fix [Finite K] [FiniteDimensional K V] [Finite V] {c₀ : K}
    (hc₀ : c₀ ∉ (wp K).range) (hQ : Q.polarBilin.Nondegenerate) {v : V ≃ₗ[K] V}
    (hO : v ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hvv : v * v = 1) {m : ℕ} (τ₀ : Bool)
    (h : 2 * m + 4 + 2 * finrank K (commSpace v) ≤ finrank K V ∨
      (2 * m + 2 + 2 * finrank K (commSpace v) = finrank K V ∧ ∃ x₀, Q (v x₀ - x₀) ≠ 0)) :
    ∃ (e f : Fin m → V) (a b : V), IsFrame Q c₀ τ₀ e f a b ∧
      ∀ x, fvec e f a b x ∈ fixSpace v := by
  obtain ⟨W₀, hW₀C, hW₀nd, hdim⟩ := exists_compl_fix hQ hO hvv
  obtain ⟨k, hk⟩ := even_finrank_of_nondeg hQ
  rcases h with h | ⟨h, x₀, hx₀⟩
  · obtain ⟨m', hm'⟩ : ∃ m', finrank K W₀ = 2 * m' + 2 := ⟨finrank K W₀ / 2 - 1, by omega⟩
    obtain ⟨τ, e, f, a, b, hmem, hF, -⟩ := exists_frame hc₀ m' W₀ hW₀nd hm'
    exact exists_frame_of_type (by omega) hF τ₀ fun x => hW₀C (hmem x)
  · obtain ⟨τ, e, f, a, b, hmem, hF, -⟩ := exists_frame hc₀ m W₀ hW₀nd (by omega)
    have hrR : v x₀ - x₀ ∈ commSpace v := sub_mem_commSpace v x₀
    have hrC : v x₀ - x₀ ∈ fixSpace v := commSpace_le_fixSpace hvv hrR
    have hp : ∀ x, polar Q (v x₀ - x₀) (fvec e f a b x) = 0 := fun x =>
      polar_commSpace_fixSpace hQ hO hvv hrR (hW₀C (hmem x))
    obtain ⟨a', b', hF', ha', hb'⟩ := exists_frame_of_type_add hF hx₀ (fun i => hp (.inl i))
      (fun i => hp (.inr (.inl i))) (hp (.inr (.inr 0))) (hp (.inr (.inr 1))) τ₀
      (hW₀C (hmem (.inr (.inr 0)))) (hW₀C (hmem (.inr (.inr 1)))) hrC
    refine ⟨e, f, a', b', hF', ?_⟩
    rintro (i | i | j)
    · exact hW₀C (hmem (.inl i))
    · exact hW₀C (hmem (.inr (.inl i)))
    · fin_cases j
      · exact ha'
      · exact hb'

end WitOmBlk

end CFSG.StandardType
