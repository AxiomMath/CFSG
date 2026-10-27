module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinPrimed
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylBranchInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGSecFiveBarData
    {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    (U : Submodule (ZMod p) V) (Abar : Subgroup (↥U ≃ₗ[ZMod p] ↥U))
    (ρ : ↥(ggAInf p B Bs x L D J) ≃* ↥Abar) : Prop :=
  3 ≤ Module.finrank (ZMod p) U ∧ ZS.ReflGen p Abar ∧ ZS.AbsIrred p Abar ∧
    (∀ (a : ↥(ggAInf p B Bs x L D J)) (u : ↥U),
      (((ρ a : ↥Abar) : ↥U ≃ₗ[ZMod p] ↥U) u : V) = ggLin (p := p) ι a u) ∧
    (∀ a ∈ ggAInf p B Bs x L D J, ∀ v : V, ggLin (p := p) ι a v - v ∈ U) ∧
    (∀ a : ↥(ggAInf p B Bs x L D J), GGIsReflection p (a : MulAut ↥Bs) ↔
      ZS.IsRefl p ((ρ a : ↥Abar) : ↥U ≃ₗ[ZMod p] ↥U)) ∧
    ((LinearEquiv.neg (ZMod p) : ↥U ≃ₗ[ZMod p] ↥U) ∈ Abar → U = ⊤)

theorem ggSecFive_weyl_of_linWeyl
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {U : Submodule (ZMod p) V} {Abar : Subgroup (↥U ≃ₗ[ZMod p] ↥U)}
    {ρ : ↥(ggAInf p B Bs x L D J) ≃* ↥Abar}
    (hD : GGSecFiveBarData p B Bs x L D J ι U Abar ρ)
    (hW : ZS.LinWeyl p Abar) : GGWeylReflectionGroup p (ggAInf p B Bs x L D J) := by
  obtain ⟨ι', M, hM, f, hf⟩ := hW
  refine ⟨ι', M, hM, f.trans ρ.symm, fun i => ?_⟩
  rw [hD.2.2.2.2.2.1]
  have hx : ρ ((f.trans ρ.symm) (M.simple i)) = f (M.simple i) := by
    simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rw [hx]
  exact hf i

theorem ggSecFive_not_witNEG3
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {U : Submodule (ZMod p) V} {Abar : Subgroup (↥U ≃ₗ[ZMod p] ↥U)}
    {ρ : ↥(ggAInf p B Bs x L D J) ≃* ↥Abar}
    (hD : GGSecFiveBarData p B Bs x L D J ι U Abar ρ)
    (h4 : 4 ≤ Module.finrank (ZMod p) V) : ¬ ZS.WitNEG3 p Abar := by
  rintro ⟨h3, hneg⟩
  have htop : U = ⊤ := hD.2.2.2.2.2.2 hneg
  have hfr : Module.finrank (ZMod p) U = Module.finrank (ZMod p) V := by
    rw [htop, finrank_top]
  omega

end CFSG.StandardType

end
