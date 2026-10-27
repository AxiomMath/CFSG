module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutDefs
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinberg

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

namespace OrdPGraph

section Model

variable {U C : Type*} [Group U] [Group C]

@[expose] def ModelDiagField (Δ : UniversalRootDatum U) (π : U →* C) (β : MulAut C) : Prop :=
  ∃ g : C, ∀ γ ∈ Δ.roots, ∀ z ∈ Δ.rootGroup γ, ∃ z' ∈ Δ.rootGroup γ, g⁻¹ * β (π z) * g = π z'

theorem normalizerMonoidHom_inv_apply {G : Type*} [Group G] {H : Subgroup G} {c : G}
    (hc : c ∈ Subgroup.normalizer (H : Set G)) (x : H) :
    ((H.normalizerMonoidHom ⟨c⁻¹, inv_mem hc⟩ x : H) : G) = c⁻¹ * x * c := by
  simp

theorem ggPsiDiagField_of_model {G : Type*} [Group G] {Δ : UniversalRootDatum U}
    {ψ : U →* G} {π : U →* C} (hπ : Function.Surjective π) (hker : π.ker = ψ.ker) {p : ℕ}
    {c : G} (hc : c ∈ Subgroup.normalizer (ψ.range : Set G)) (hcp : c ^ p = 1)
    (hM : ∀ β : MulAut C, β ^ p = 1 → ModelDiagField Δ π β) : GGPsiDiagField Δ ψ c := by
  set Θ : C ≃* ψ.range := AutSt.modelEquiv ψ π hπ hker with hΘdef
  have hΘ : ∀ y, ((Θ (π y) : ψ.range) : G) = ψ y := AutSt.modelEquiv_apply ψ π hπ hker
  set a : MulAut ψ.range := ψ.range.normalizerMonoidHom ⟨c⁻¹, inv_mem hc⟩ with hadef
  have ha : ∀ x : ψ.range, ((a x : ψ.range) : G) = c⁻¹ * x * c :=
    normalizerMonoidHom_inv_apply hc
  have hap : a ^ p = 1 := by
    rw [hadef, ← map_pow]
    have e : (⟨c⁻¹, inv_mem hc⟩ : Subgroup.normalizer (ψ.range : Set G)) ^ p = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, inv_pow, hcp, inv_one]; rfl)
    rw [e, map_one]
  set β : MulAut C := MulAut.congr Θ.symm a with hβdef
  have hβ : ∀ x : C, Θ (β x) = a (Θ x) := fun x => by
    rw [hβdef, MulAut.congr_apply]
    simp
  have hβp : β ^ p = 1 := by
    rw [hβdef, ← map_pow, hap, map_one]
  obtain ⟨g, hg⟩ := hM β hβp
  refine ⟨Θ g, (Θ g).2, fun γ hγ z hz => ?_⟩
  obtain ⟨z', hz', e⟩ := hg γ hγ z hz
  refine ⟨z', hz', ?_⟩
  have e' := congrArg (fun x => ((Θ x : ψ.range) : G)) e
  simp only [map_mul, map_inv, hβ, Subgroup.coe_mul, Subgroup.coe_inv, ha, hΘ] at e'
  rw [← e']
  group

end Model

end OrdPGraph

section Inputs

@[expose] def GGOrdPGraphModelAt (t : StatedLieTag) : Prop :=
  ∀ n f : ℕ, StatedLieAdmissible t n 2 f → 2 ≤ (ggU t n f).D.rank →
    ∃ (C : Type) (_ : Group C) (π : (ggU t n f).K →* C), Function.Surjective π ∧
      π.ker = Subgroup.center (ggU t n f).K ∧
      ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ (t = .POmegaPlus ∧ n = 4 ∧ p = 3) →
        ∀ β : MulAut C, β ^ p = 1 → OrdPGraph.ModelDiagField (ggU t n f).D π β

theorem ggOrdPGraphAt_of_model {t : StatedLieTag} (h : GGOrdPGraphModelAt t) :
    GGOrdPGraphAt t := by
  intro G _ _ n f ψ G₀ hpres hC p hp hp2 y hyM hyp hDF
  by_contra hne
  apply hDF
  obtain ⟨⟨hadm, hrank⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
  obtain ⟨C, _, π, hπ, hπker, hM⟩ := h n f hadm hrank
  have hC' : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact hC
  have hψ := AutSt.ker_eq_center hker hC'
  rw [← hrange] at hyM
  exact OrdPGraph.ggPsiDiagField_of_model hπ (hπker.trans hψ.symm) hyM hyp (hM p hp hp2 hne)

end Inputs

end CFSG.StandardType
