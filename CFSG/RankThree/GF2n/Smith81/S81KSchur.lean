module

public import CFSG.RankThree.GF2n.Smith81.S81BGeom
public import CFSG.RankThree.GF2n.Stroth80.Sec12CaseVIEquiv

public section

namespace CFSG.RankThree.GF2n.Smith81.KSchur

open CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom

section Schur

variable {K : Type} [Field K] {E : Type} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

theorem riesz (β : E →ₗ[K] E →ₗ[K] K) (hβ : ∀ w : E, (∀ u : E, β u w = 0) → w = 0)
    (B : E →ₗ[K] E →ₗ[K] K) : ∃ T : E →ₗ[K] E, ∀ u v : E, B u v = β u (T v) := by
  have hinj : Function.Injective β.flip := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    apply hβ
    intro u
    have h := LinearMap.congr_fun hw u
    rw [LinearMap.flip_apply, LinearMap.zero_apply] at h
    exact h
  have hdim : Module.finrank K E = Module.finrank K (Module.Dual K E) :=
    Subspace.dual_finrank_eq.symm
  have hsurj : Function.Surjective β.flip :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  let Φ : E ≃ₗ[K] Module.Dual K E := LinearEquiv.ofBijective β.flip ⟨hinj, hsurj⟩
  refine ⟨Φ.symm.toLinearMap ∘ₗ B.flip, fun u v => ?_⟩
  have h1 : β.flip (Φ.symm (B.flip v)) = B.flip v := Φ.apply_symm_apply _
  have h2 := LinearMap.congr_fun h1 u
  rw [LinearMap.flip_apply, LinearMap.flip_apply] at h2
  exact h2.symm

theorem commutes_of_invariant (Γ : Subgroup (E ≃ₗ[K] E)) (β B : E →ₗ[K] E →ₗ[K] K)
    (hβ : ∀ w : E, (∀ u : E, β u w = 0) → w = 0)
    (hβΓ : ∀ g ∈ Γ, ∀ u v, β (g u) (g v) = β u v)
    (hBΓ : ∀ g ∈ Γ, ∀ u v, B (g u) (g v) = B u v)
    (T : E →ₗ[K] E) (hT : ∀ u v, B u v = β u (T v)) :
    ∀ g ∈ Γ, ∀ v, T (g v) = g (T v) := by
  intro g hg v
  apply sub_eq_zero.mp
  apply hβ
  intro u
  obtain ⟨u', rfl⟩ : ∃ u', u = g u' := ⟨g.symm u, by simp⟩
  rw [map_sub, ← hT, hBΓ g hg, hT, hβΓ g hg, sub_self]

theorem scalar_of_fixed_line (Γ U₀ : Subgroup (E ≃ₗ[K] E)) (p : E) (hp : p ≠ 0)
    (hU : U₀ ≤ Γ) (hfix : ∀ u ∈ U₀, u p = p)
    (hFix : ∀ v : E, (∀ u ∈ U₀, u v = v) → v ∈ Submodule.span K {p})
    (hirr : ∀ S : AddSubgroup E, (∀ g ∈ Γ, ∀ s ∈ S, g s ∈ S) → S = ⊥ ∨ S = ⊤)
    (T : E →ₗ[K] E) (hT : ∀ g ∈ Γ, ∀ v, T (g v) = g (T v)) : ∃ c : K, ∀ v, T v = c • v := by
  have hTp : T p ∈ Submodule.span K {p} := by
    apply hFix
    intro u hu
    rw [← hT u (hU hu), hfix u hu]
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hTp
  refine ⟨c, ?_⟩
  let O : Submodule K E := Submodule.span K (Set.range fun g : Γ => (g : E ≃ₗ[K] E) p)
  have hO : O.toAddSubgroup = ⊤ := by
    rcases hirr O.toAddSubgroup (fun g hg s hs => by
        change s ∈ O at hs
        change g s ∈ O
        induction hs using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨h, rfl⟩ := hx
          exact Submodule.subset_span ⟨⟨g * h, mul_mem hg h.2⟩, rfl⟩
        | zero => simp
        | add x y _ _ hx hy => rw [map_add]; exact O.add_mem hx hy
        | smul a x _ hx => rw [map_smul]; exact O.smul_mem a hx) with h | h
    · exfalso
      have : p ∈ O.toAddSubgroup := Submodule.subset_span ⟨⟨1, one_mem Γ⟩, rfl⟩
      rw [h] at this
      exact hp (by simpa using this)
    · exact h
  intro v
  have hv : v ∈ O := by
    have : v ∈ O.toAddSubgroup := by rw [hO]; trivial
    exact this
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    rw [hT g g.2, ← hc, map_smul]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul a x _ hx => rw [map_smul, hx, smul_comm]

end Schur

section FormGeneric

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
  {E : Type} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

theorem form_of_uniform (hc : Ctx M Q Z B)
    (hD : GlobalModelData M Q Z γ M₀)
    (β : E →ₗ[K] E →ₗ[K] K) (hβ : ∀ w : E, (∀ u : E, β u w = 0) → w = 0)
    {Γ U₀ : Subgroup (E ≃ₗ[K] E)} {p₀ : E} (hp₀ : p₀ ≠ 0)
    (hβΓ : ∀ g ∈ Γ, ∀ u v, β (g u) (g v) = β u v) (hU : U₀ ≤ Γ) (hfix : ∀ u ∈ U₀, u p₀ = p₀)
    (hFix : ∀ v : E, (∀ u ∈ U₀, u v = v) → v ∈ Submodule.span K {p₀})
    (hirr : ∀ S : AddSubgroup E, (∀ g ∈ Γ, ∀ s ∈ S, g s ∈ S) → S = ⊥ ∨ S = ⊤)
    {ψ : M₀.E ≃ₗ[K] E} {φ : Lgen M (LB M Q B) →* (E ≃ₗ[K] E)}
    (d : EUniData M Q Z B M₀ ψ φ Γ p₀ U₀) :
    ∃ lam : K, lam ≠ 0 ∧ ∀ e f : M₀.E, M₀.B e f = lam * β (ψ e) (ψ f) := by
  let B' : E →ₗ[K] E →ₗ[K] K :=
    M₀.B.compl₁₂ (ψ.symm : E →ₗ[K] M₀.E) (ψ.symm : E →ₗ[K] M₀.E)
  have hB' : ∀ u v, B' u v = M₀.B (ψ.symm u) (ψ.symm v) := fun u v => rfl
  have hinv : ∀ g ∈ Γ, ∀ u v, B' (g u) (g v) = B' u v := by
    intro g hg u v
    rw [← d.range] at hg
    obtain ⟨s, rfl⟩ := hg
    have hsH : (s : G) ∈ H0 M Z := Lgen_le_H0 hc s.2
    obtain ⟨hsM, hsC⟩ := Subgroup.mem_inf.mp hsH
    have hcz : ∀ z ∈ Z, (s : G) * z * (s : G)⁻¹ = z := fun z hz => by
      have h1 := Subgroup.mem_centralizer_iff.mp hsC z hz
      rw [mul_inv_eq_iff_eq_mul]
      exact h1.symm
    obtain ⟨T₀, hT₀, -, hB⟩ := hD.linear_of_centralizes hsM hcz
    have hψT : ∀ e, ψ (T₀ e) = φ s (ψ e) := by
      intro e
      obtain ⟨x, hx, rfl⟩ := M₀.π_surj e
      rw [← hT₀ x hx, d.equivariant s x hx]
    have hsymm : ∀ w, ψ.symm (φ s w) = T₀ (ψ.symm w) := by
      intro w
      apply ψ.injective
      rw [hψT, ψ.apply_symm_apply, ψ.apply_symm_apply]
    rw [hB', hB', hsymm, hsymm, hB]
  obtain ⟨T, hT⟩ := riesz β hβ B'
  have hcomm := commutes_of_invariant Γ β B' hβ hβΓ hinv T hT
  obtain ⟨c, hc⟩ := scalar_of_fixed_line Γ U₀ p₀ hp₀ hU hfix hFix hirr T hcomm
  refine ⟨c, ?_, fun e f => ?_⟩
  · intro h0
    have hzero : ∀ e f, M₀.B e f = 0 := fun e f => by
      have h1 := hT (ψ e) (ψ f)
      rw [hB', hc, h0] at h1
      simpa using h1
    have hne : ψ.symm p₀ ≠ 0 := by
      intro h
      exact hp₀ (by simpa using congrArg ψ h)
    exact hne (M₀.nondeg _ fun f => hzero _ f)
  · have h1 := hT (ψ e) (ψ f)
    rw [hB', hc, map_smul, smul_eq_mul] at h1
    simpa using h1

end FormGeneric

end CFSG.RankThree.GF2n.Smith81.KSchur
