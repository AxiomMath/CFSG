module

public import CFSG.LocalAnalysis.StandardType.GGMaxRankJReflection
import CFSG.LocalAnalysis.StandardType.GGF4AutWeyl

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma pjt_mulAut_congr_symm_trans_apply {M N P : Type} [Group M] [Group N] [Group P]
    (e₁ : M ≃* N) (e₂ : M ≃* P) (ψ : MulAut M) :
    MulAut.congr (e₁.symm.trans e₂) (MulAut.congr e₁ ψ) = MulAut.congr e₂ ψ := by
  ext x
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_trans_apply,
    MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]

theorem ggMaxRank_automizerTransport {G G' : Type} [Group G] [Finite G] [Group G'] [Finite G']
    {X J A : Subgroup G} (hJ : J ≤ X) (hA : A ≤ X) (θ : ↥X ≃* G') :
    ∃ (eA : ↥A ≃* ↥((A.subgroupOf X).map θ.toMonoidHom))
      (e : ↥(ggAutomizer J A) ≃*
        ↥(ggAutomizer ((J.subgroupOf X).map θ.toMonoidHom) ((A.subgroupOf X).map θ.toMonoidHom))),
      ∀ φ : ↥(ggAutomizer J A),
        (e φ : MulAut ↥((A.subgroupOf X).map θ.toMonoidHom)) = MulAut.congr eA (φ : MulAut ↥A) := by
  let f : ↥X →* G := X.subtype
  let g : ↥X →* G' := θ.toMonoidHom
  let J₁ : Subgroup ↥X := J.subgroupOf X
  let A₁ : Subgroup ↥X := A.subgroupOf X
  have hf : Function.Injective f := fun _ _ h => Subtype.ext h
  have hg : Function.Injective g := θ.injective
  have hA₁ : A₁.map f = A := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hA hx⟩, hx, rfl⟩
  have hJ₁ : J₁.map f = J := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hJ hx⟩, hx, rfl⟩
  let e₁ : ↥A₁ ≃* ↥A := (A₁.equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hA₁)
  let e₂ : ↥A₁ ≃* ↥(A₁.map g) := (A₁.equivMapOfInjective g hg).trans (MulEquiv.subgroupCongr rfl)
  have h1 : ggAutomizer J A = (ggAutomizer J₁ A₁).map (MulAut.congr e₁).toMonoidHom := by
    have h := F4AutWeyl.ggAutomizer_map_eq (f := f) hf J₁ A₁ hA₁
    simpa [e₁, hJ₁] using h
  have h2 : ggAutomizer (J₁.map g) (A₁.map g) =
      (ggAutomizer J₁ A₁).map (MulAut.congr e₂).toMonoidHom := by
    have h := F4AutWeyl.ggAutomizer_map_eq (f := g) hg J₁ A₁ (rfl : A₁.map g = A₁.map g)
    simpa [e₂] using h
  let eA : ↥A ≃* ↥(A₁.map g) := e₁.symm.trans e₂
  let σ₁ : MulAut ↥A₁ →* MulAut ↥A := (MulAut.congr e₁).toMonoidHom
  let σ₂ : MulAut ↥A₁ →* MulAut ↥(A₁.map g) := (MulAut.congr e₂).toMonoidHom
  let σ : MulAut ↥A →* MulAut ↥(A₁.map g) := (MulAut.congr eA).toMonoidHom
  have hσ : ∀ ψ : MulAut ↥A₁, σ (σ₁ ψ) = σ₂ ψ := fun ψ =>
    pjt_mulAut_congr_symm_trans_apply e₁ e₂ ψ
  have hmap : (ggAutomizer J₁ A₁).map σ₂ = ((ggAutomizer J₁ A₁).map σ₁).map σ := by
    ext φ
    simp only [Subgroup.mem_map]
    constructor
    · rintro ⟨ψ, hψ, hφ⟩
      exact ⟨σ₁ ψ, ⟨ψ, hψ, rfl⟩, by rw [hσ ψ, hφ]⟩
    · rintro ⟨η, ⟨ψ, hψ, rfl⟩, hφ⟩
      exact ⟨ψ, hψ, by rw [← hσ ψ, hφ]⟩
  have h2' : (ggAutomizer J A).map σ = ggAutomizer (J₁.map g) (A₁.map g) := by
    rw [h1, h2]
    exact hmap.symm
  refine ⟨eA, ((ggAutomizer J A).equivMapOfInjective σ (MulAut.congr eA).injective).trans
    (MulEquiv.subgroupCongr h2'), ?_⟩
  intro φ
  rfl

end CFSG.StandardType

end
