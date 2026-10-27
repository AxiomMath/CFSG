module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResRank1
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitClassFunctionInner

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial Polynomial
open scoped MatrixGroups


theorem excres_inner_on_rankOne_of_odd {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] (K' : Subfield L) [Finite K'] (β : Fin τ.rank → ℤ)
    (z : ModGL τ L) {P : Type} [Group P] [Finite P] (ι : P →* ModGL τ L)
    (hι : Function.Injective ι)
    (hθ : ∀ g : SL2 K', excresTheta τ K' β z g ∈ ι.range)
    {J : Subgroup P} (hJ : ∀ p : P, p ∈ J ↔ ι p ∈ (excresTheta τ K' β z).range)
    {y : P} (hyo : Odd (orderOf y))
    (hstab : ∀ p : P, y * p * y⁻¹ ∈ J ↔ p ∈ J) :
    ∃ w ∈ J, ∀ j ∈ J, y * j * y⁻¹ = w * j * w⁻¹ := by
  classical
  set θ := excresTheta τ K' β z with hθdef
  let e : P ≃* ι.range := MonoidHom.ofInjective hι
  let ρ : SL2 K' →* P := e.symm.toMonoidHom.comp (θ.codRestrict ι.range hθ)
  have hιρ : ∀ g, ι (ρ g) = θ g := by
    intro g
    have : e (ρ g) = ⟨θ g, hθ g⟩ := by
      change e (e.symm ⟨θ g, hθ g⟩) = _
      exact e.apply_symm_apply _
    exact congrArg Subtype.val this
  have hrange : ρ.range = J := by
    ext p
    constructor
    · rintro ⟨g, rfl⟩
      rw [hJ, hιρ]
      exact ⟨g, rfl⟩
    · intro hp
      obtain ⟨g, hg⟩ := (hJ p).1 hp
      exact ⟨g, hι (by rw [hιρ]; exact hg)⟩
  have hker : ∀ g : SL2 K', ρ g = 1 → ∃ l : K'ˣ, l ^ 2 = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) K') = (l : K') • (1 : Matrix (Fin 2) (Fin 2) K') := by
    intro g hg
    have h1 : θ g = 1 := by rw [← hιρ, hg, map_one]
    have h2 : g = 1 := excresTheta_injective τ K' β z (by rw [h1, map_one])
    exact ⟨1, by simp, by rw [h2]; simp⟩
  have hχ : ∀ g h : P, LinearMap.trace L (RootModule τ L)
      (ι (h * g * h⁻¹) : Module.End L (RootModule τ L)) =
      LinearMap.trace L (RootModule τ L) (ι g : Module.End L (RootModule τ L)) := by
    intro g h
    rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, LinearMap.trace_conj]
  obtain ⟨c, c₀, hcc⟩ : ∃ (c : ℕ) (c₀ : L), ∀ t : K'ˣ,
      LinearMap.trace L (RootModule τ L) (θ (sl2Diag K' t) : Module.End L (RootModule τ L)) =
        K'.subtype (((t : K') + (t : K')⁻¹) ^ 2 + (c : K') * ((t : K') + (t : K')⁻¹)) + c₀ := by
    rcases hτ with rfl | rfl | rfl
    · refine ⟨20, 34, fun t => ?_⟩
      rw [hθdef, excres_trace_theta (Or.inl rfl)]
      simp [eRootTracePoly, sl2Diag, Matrix.trace_fin_two, map_ofNat]
      rfl
    · refine ⟨32, 65, fun t => ?_⟩
      rw [hθdef, excres_trace_theta (Or.inr (Or.inl rfl))]
      simp [eRootTracePoly, sl2Diag, Matrix.trace_fin_two, map_ofNat]
      rfl
    · refine ⟨56, 132, fun t => ?_⟩
      rw [hθdef, excres_trace_theta (Or.inr (Or.inr rfl))]
      simp [eRootTracePoly, sl2Diag, Matrix.trace_fin_two, map_ofNat]
      rfl
  have hχd : ∀ t : K'ˣ, LinearMap.trace L (RootModule τ L)
      (ι (ρ (sl2Diag K' t)) : Module.End L (RootModule τ L)) =
      K'.subtype (((t : K') + (t : K')⁻¹) ^ 2 +
        (c : K') * ((t : K') + (t : K')⁻¹)) + c₀ := by
    intro t
    rw [hιρ]
    exact hcc t
  obtain ⟨w, hw, hwj⟩ := excres_normalizer_inner_of_odd (ρ := ρ) hker K'.subtype c c₀
    (fun g => LinearMap.trace L (RootModule τ L) (ι g : Module.End L (RootModule τ L)))
    hχ hχd hyo (by
      rw [hrange]
      ext p
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact (hstab q).2 hq
      · intro hp
        refine ⟨y⁻¹ * p * y, (hstab _).1 ?_, ?_⟩
        · simpa [mul_assoc] using hp
        · simp [MulAut.conj_apply, mul_assoc])
  rw [hrange] at hw hwj
  exact ⟨w, hw, hwj⟩

end CFSG.HardMathSupport.Dickson.Sec6.I1431
