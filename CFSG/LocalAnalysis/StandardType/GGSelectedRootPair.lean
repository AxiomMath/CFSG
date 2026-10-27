module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinSelected
public import CFSG.LocalAnalysis.StandardType.GGSelectedModelOfChevalley
public import CFSG.LocalAnalysis.StandardType.GGRankOneModel
public import CFSG.LocalAnalysis.StandardType.GGSecFivePresOfPsiFacts
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits
open CFSG.Open (StatedLieTag StatedLieAdmissible)

section Weyl

variable {U : Type*} [Group U] {D : UniversalRootDatum U} {ν : GGWeyl D →* U}

theorem map_rootGroup_conj_weylLift (hν : GGWeylLift D ν) (w : GGWeyl D) {γ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) :
    (D.rootGroup γ).map (MulAut.conj (ν w)).toMonoidHom =
      D.rootGroup (weylAction D.isFiniteType w γ) := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact hν.conj_mem w γ hγ y hy
  · intro z hz
    have h := hν.conj_mem w⁻¹ _
      (CFSG.LieType.RootSystem.weylAction_mem_roots D.isFiniteType w hγ) z hz
    rw [← weylAction_mul_apply, inv_mul_cancel, map_one, Module.End.one_apply, map_inv] at h
    have h' : (ν w)⁻¹ * z * ν w ∈ D.rootGroup γ := by simpa only [inv_inv] using h
    refine Subgroup.mem_map.mpr ⟨(ν w)⁻¹ * z * ν w, h', ?_⟩
    change ν w * ((ν w)⁻¹ * z * ν w) * (ν w)⁻¹ = z
    group

end Weyl

section Packages

variable {G : Type} [Group G]

theorem presentedSelectedSL2At_ggRootSub {t : StatedLieTag} {n f : ℕ}
    (ψ : (ggU t n f).K →* G) (hW : GGHasWeylLift (ggU t n f).D)
    (hM : GGRankOneModel (ggU t n f).D (GaloisField 2 f))
    (hdiv : (ggU t n f).D.divisible = ∅) {β : Fin (ggU t n f).D.rank → ℤ}
    (hβ : β ∈ (ggU t n f).D.roots) (k : (ggU t n f).K) :
    PresentedSelectedSL2At ψ
      (ggRootSub (ggU t n f).D ψ β k ⊔ ggRootSub (ggU t n f).D ψ (-β) k) := by
  obtain ⟨ν, hν⟩ := hW
  rcases hβ with ⟨w, i, rfl⟩ | ⟨-, i, hi, -⟩
  swap
  · rw [hdiv] at hi
    exact absurd hi (Set.notMem_empty i)
  have hi : (Pi.single i 1 : Fin (ggU t n f).D.rank → ℤ) ∈ (ggU t n f).D.roots :=
    Or.inl ⟨1, i, by simp⟩
  have hi' : (-Pi.single i 1 : Fin (ggU t n f).D.rank → ℤ) ∈ (ggU t n f).D.roots :=
    CFSG.LieType.Steinberg.OfCartan.neg_mem_roots _ hi
  obtain ⟨model, hmodel⟩ := SelectedRoot.exists_model_of_rankOneModel hM i
  refine ⟨GaloisField 2 f, inferInstance, inferInstance, inferInstance, Pi.single i 1, model,
    k * ν w, ?_⟩
  have hconj : (MulAut.conj (k * ν w)).toMonoidHom =
      (MulAut.conj k).toMonoidHom.comp (MulAut.conj (ν w)).toMonoidHom := by
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  rw [MonoidHom.range_comp, hmodel, ← Subgroup.map_map]
  change ((((ggU t n f).D.rootGroup (Pi.single i 1) ⊔
      (ggU t n f).D.rootGroup (-Pi.single i 1)).map (MulAut.conj (k * ν w)).toMonoidHom).map ψ) = _
  rw [hconj, ← Subgroup.map_map, Subgroup.map_sup, map_rootGroup_conj_weylLift hν w hi,
    map_rootGroup_conj_weylLift hν w hi', map_neg, Subgroup.map_sup, Subgroup.map_sup]
  rfl

theorem memberSelectedSL2At_map_ggRootLevi {X : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    (lam : (ggU t n f).K →* G) (hadm : StatedLieAdmissible t n 2 f)
    (hrk : 2 ≤ (ggU t n f).D.rank) (hker : lam.ker ≤ Subgroup.center (ggU t n f).K)
    (hrange : lam.range = X) {k : Type} [Field k] [Finite k] [CharP k 2]
    {δ : Fin (ggU t n f).D.rank → ℤ} (model : SelectedRoot.SelectedSL2Model (ggU t n f).D k δ)
    (hmodel : model.phi.range = ggRootLevi (ggU t n f).D δ) :
    MemberSelectedSL2At X ((ggRootLevi (ggU t n f).D δ).map lam) :=
  ⟨t, n, f, lam, hadm, hrk, hker, hrange, k, inferInstance, inferInstance, inferInstance, δ, model,
    by rw [MonoidHom.range_comp, hmodel]⟩

theorem exists_selected_of_rootPair {X : Subgroup G} {t t' : StatedLieTag} {n f n' f' : ℕ}
    (ψ : (ggU t n f).K →* G) (hW : GGHasWeylLift (ggU t n f).D)
    (hM : GGRankOneModel (ggU t n f).D (GaloisField 2 f))
    (hdiv : (ggU t n f).D.divisible = ∅)
    (α : (ggU t' n' f').K →* G) (hadm : StatedLieAdmissible t' n' 2 f')
    (hrk : 2 ≤ (ggU t' n' f').D.rank) (hker : α.ker ≤ Subgroup.center (ggU t' n' f').K)
    (hrange : α.range = X) {k : Type} [Field k] [Finite k] [CharP k 2]
    {δ : Fin (ggU t' n' f').D.rank → ℤ} (model : SelectedRoot.SelectedSL2Model (ggU t' n' f').D k δ)
    (hmodel : model.phi.range = ggRootLevi (ggU t' n' f').D δ)
    {β : Fin (ggU t n f).D.rank → ℤ} (hβ : β ∈ (ggU t n f).D.roots) (u : (ggU t n f).K)
    (h₁ : ((ggU t' n' f').D.rootGroup δ).map α = ggRootSub (ggU t n f).D ψ β u)
    (h₂ : ((ggU t' n' f').D.rootGroup (-δ)).map α = ggRootSub (ggU t n f).D ψ (-β) u) :
    ∃ S : Subgroup G, MemberSelectedSL2At X S ∧ PresentedSelectedSL2At ψ S := by
  refine ⟨_, memberSelectedSL2At_map_ggRootLevi α hadm hrk hker hrange model hmodel, ?_⟩
  have hS : (ggRootLevi (ggU t' n' f').D δ).map α =
      ggRootSub (ggU t n f).D ψ β u ⊔ ggRootSub (ggU t n f).D ψ (-β) u := by
    rw [← h₁, ← h₂]
    exact Subgroup.map_sup _ _ _
  rw [hS]
  exact presentedSelectedSL2At_ggRootSub ψ hW hM hdiv hβ u

end Packages

end CFSG.StandardType

end
