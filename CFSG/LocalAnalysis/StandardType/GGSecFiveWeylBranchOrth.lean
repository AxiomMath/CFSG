module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinPrimed
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylBranchInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBarData

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggSecFive_weyl_of_witORTH
    (hOrth : GGSecFiveOrthExclInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {U : Submodule (ZMod p) V} {Abar : Subgroup (↥U ≃ₗ[ZMod p] ↥U)}
    {ρ : ↥(ggAInf p B Bs x L D J) ≃* ↥Abar}
    (hD : GGSecFiveBarData p B Bs x L D J ι U Abar ρ)
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg' p B Bs x L D J 𝒦) (hsplit : GGSplitLie p L)
    (hC : ∀ b : ↥Bs, (∀ φ ∈ ggAInf p B Bs x L D J, φ b = b) → b = 1)
    (hO : ZS.WitORTH p Abar) : GGWeylReflectionGroup p (ggAInf p B Bs x L D J) := by
  obtain ⟨hp3, hdimU, Q, hQ, hAbar⟩ := hO
  have hneg : (LinearEquiv.neg (ZMod p) : ↥U ≃ₗ[ZMod p] ↥U) ∈ Abar :=
    (hAbar _).mpr fun v => by simp
  have hU : U = ⊤ := hD.2.2.2.2.2.2 hneg
  let eU : ↥U ≃ₗ[ZMod p] V := LinearEquiv.ofTop U hU
  have heU : ∀ u : ↥U, eU u = (u : V) := fun u => LinearEquiv.ofTop_apply U u
  let f : V →ₗ[ZMod p] ↥U := eU.symm.toLinearMap
  let Q' : QuadraticForm (ZMod p) V := Q.comp f
  have hQ'_apply : ∀ w : V, Q' w = Q (eU.symm w) := fun w => rfl
  have hQ'eU : ∀ u : ↥U, Q' (eU u) = Q u := by
    intro u
    rw [hQ'_apply, LinearEquiv.symm_apply_apply]
  have hpolar :
      QuadraticMap.polarBilin Q' = LinearMap.BilinForm.congr eU (QuadraticMap.polarBilin Q) := by
    dsimp only [Q', f]
    rw [QuadraticMap.polarBilin_comp]
    ext x y
    rw [LinearMap.compl₁₂_apply, LinearMap.BilinForm.congr_apply]
    rfl
  have hQ' : (QuadraticMap.polarBilin Q').Nondegenerate := by
    rw [hpolar]
    exact (LinearMap.BilinForm.nondegenerate_congr_iff eU).mpr hQ
  have hdimV : Module.finrank (ZMod p) V = 4 ∨ Module.finrank (ZMod p) V = 5 := by
    rw [← eU.finrank_eq]
    exact hdimU
  have himage : ∀ g : V ≃ₗ[ZMod p] V,
      (∃ a ∈ ggAInf p B Bs x L D J, ggLin (p := p) ι a = g) ↔ ∀ v, Q' (g v) = Q' v := by
    intro g
    constructor
    · rintro ⟨a, ha, rfl⟩
      let a' : ↥(ggAInf p B Bs x L D J) := ⟨a, ha⟩
      intro v
      obtain ⟨u, rfl⟩ := eU.bijective.2 v
      have hgg : ggLin (p := p) ι a (eU u)
          = eU (((ρ a' : ↥Abar) : ↥U ≃ₗ[ZMod p] ↥U) u) := by
        rw [heU u, heU (((ρ a' : ↥Abar) : ↥U ≃ₗ[ZMod p] ↥U) u)]
        exact (hD.2.2.2.1 a' u).symm
      rw [hgg, hQ'eU, hQ'eU]
      exact (hAbar ((ρ a' : ↥Abar) : ↥U ≃ₗ[ZMod p] ↥U)).mp (ρ a').2 u
    · intro hg
      let σ : ↥U ≃ₗ[ZMod p] ↥U := eU.trans (g.trans eU.symm)
      have hσ_apply : ∀ u : ↥U, eU (σ u) = g (eU u) := by
        intro u
        dsimp only [σ]
        rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
      have hσ : ZS.IsIsom p Q σ := by
        intro u
        rw [← hQ'eU (σ u), hσ_apply u, hg (eU u), hQ'eU u]
      have hσA : σ ∈ Abar := (hAbar σ).mpr hσ
      obtain ⟨a, ha⟩ := ρ.surjective ⟨σ, hσA⟩
      refine ⟨(a : MulAut ↥Bs), a.2, ?_⟩
      ext v
      obtain ⟨u, rfl⟩ := eU.bijective.2 v
      have hgg : ggLin (p := p) ι (a : MulAut ↥Bs) (eU u)
          = eU (((ρ a : ↥Abar) : ↥U ≃ₗ[ZMod p] ↥U) u) := by
        rw [heU u, heU (((ρ a : ↥Abar) : ↥U ≃ₗ[ZMod p] ↥U) u)]
        exact (hD.2.2.2.1 a u).symm
      have hcoe : ((ρ a : ↥Abar) : ↥U ≃ₗ[ZMod p] ↥U) = σ :=
        congrArg (fun x : ↥Abar => (x : ↥U ≃ₗ[ZMod p] ↥U)) ha
      rw [hgg, hcoe, hσ_apply u]
  exact hOrth G p B Bs x L D J 𝒦 hcfg hsplit hC hp3 V Q' hQ' ι hdimV himage

end CFSG.StandardType

end
