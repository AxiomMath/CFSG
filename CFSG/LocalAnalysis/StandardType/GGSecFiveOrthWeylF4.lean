module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthF4Model
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthCount
public import CFSG.Monster.B.Geometry.F4Weyl
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBarBridge
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
public import CFSG.Monster.B.Geometry.CoxeterWords

public section

namespace CFSG.StandardType.OrthF3

open TauCeti

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

private theorem ct_oj_card_coxeterF4 :
    Nat.card (CoxeterMatrix.F₄).Group = 1152 := by
  have hC : GGIntCartan CoxeterMatrix.F₄ (CFSG.Blueprint.Chevalley.Tag.cartan .F4) := by
    refine ⟨by decide, fun i j hij => ?_⟩
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide
  have hM : CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) = CoxeterMatrix.F₄ :=
    coxeterMatrix_eq_of_ggIntCartan (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) hC
  have h : Nat.card (CFSG.LieType.Chevalley.WeylGroup .F4) = 1152 :=
    CFSG.Monster.B.Geometry.card_f4WeylGroup
  change Nat.card ((CFSG.LieType.RootSystem.coxeterMatrix
    (CFSG.LieType.Chevalley.isFiniteType_cartan .F4)).Group) = 1152 at h
  rw [hM] at h
  exact h

private theorem ct_oj_orthReflOfNorm_map {V₁ V₂ : Type} [AddCommGroup V₁] [Module (ZMod 3) V₁]
    [AddCommGroup V₂] [Module (ZMod 3) V₂] {Q₁ : QuadraticForm (ZMod 3) V₁}
    {Q₂ : QuadraticForm (ZMod 3) V₂} {c : ZMod 3} {g : V₁ ≃ₗ[ZMod 3] V₁}
    (hgmem : g ∈ QuadraticMap.orthogonalGroup Q₁) (e : Q₁.IsometryEquiv Q₂)
    (h : OrthReflOfNorm Q₁ c g) :
    OrthReflOfNorm Q₂ c
      ((QuadraticMap.orthogonalGroupCongr e ⟨g, hgmem⟩ : QuadraticMap.orthogonalGroup Q₂) :
        V₂ ≃ₗ[ZMod 3] V₂) := by
  obtain ⟨v, hv, hQv, hg⟩ := h
  let gO : QuadraticMap.orthogonalGroup Q₁ := ⟨g, hgmem⟩
  have hQe : Q₂ (e v) = Q₁ v := e.map_app v
  have hInv : Invertible (Q₂ (e v)) := Invertible.copy hv (Q₂ (e v)) hQe
  have hQc : Q₂ (e v) = c := hQe.trans hQv
  refine ⟨e v, hInv, hQc, ?_⟩
  have hgO : (QuadraticMap.reflectionOrthogonal Q₁ v : QuadraticMap.orthogonalGroup Q₁) = gO :=
    Subtype.ext hg
  change ((QuadraticMap.reflectionOrthogonal Q₂ (e v) : QuadraticMap.orthogonalGroup Q₂) :
      V₂ ≃ₗ[ZMod 3] V₂) =
    ((QuadraticMap.orthogonalGroupCongr e gO : QuadraticMap.orthogonalGroup Q₂) :
      V₂ ≃ₗ[ZMod 3] V₂)
  rw [← hgO, QuadraticMap.orthogonalGroupCongr_reflectionOrthogonal e v]

private noncomputable def ct_oj_orthEquiv {G : Type} [Group G] {Bs : Subgroup G} {p : ℕ}
    [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (Q : QuadraticForm (ZMod p) V)
    (ι : Additive ↥Bs ≃+ V) (A : Subgroup (MulAut ↥Bs))
    (hA : ∀ g : V ≃ₗ[ZMod p] V,
      (∃ a ∈ A, ggLin (p := p) ι a = g) ↔ ∀ v, Q (g v) = Q v) :
    ↥A ≃* QuadraticMap.orthogonalGroup Q := by
  classical
  let f : ↥A →* (V ≃ₗ[ZMod p] V) := (ggLin (p := p) ι).comp A.subtype
  have hf : ∀ a : ↥A, f a ∈ QuadraticMap.orthogonalGroup Q := fun a =>
    QuadraticMap.mem_orthogonalGroup_iff.mpr
      ((hA (f a)).mp ⟨(a : MulAut ↥Bs), a.2, rfl⟩)
  let F : ↥A →* QuadraticMap.orthogonalGroup Q := f.codRestrict _ hf
  refine MulEquiv.ofBijective F ⟨?_, ?_⟩
  · intro a b h
    apply Subtype.ext
    apply ggLin_injective (p := p) ι
    exact congrArg (fun z : QuadraticMap.orthogonalGroup Q => (z : V ≃ₗ[ZMod p] V)) h
  · intro g
    obtain ⟨a, ha, hga⟩ := (hA (g : V ≃ₗ[ZMod p] V)).mpr
      (QuadraticMap.mem_orthogonalGroup_iff.mp g.2)
    exact ⟨⟨a, ha⟩, Subtype.ext hga⟩

private theorem ct_oj_orthEquiv_apply_coe {G : Type} [Group G] {Bs : Subgroup G} {p : ℕ}
    [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (Q : QuadraticForm (ZMod p) V)
    (ι : Additive ↥Bs ≃+ V) (A : Subgroup (MulAut ↥Bs))
    (hA : ∀ g : V ≃ₗ[ZMod p] V,
      (∃ a ∈ A, ggLin (p := p) ι a = g) ↔ ∀ v, Q (g v) = Q v) (a : ↥A) :
    ((ct_oj_orthEquiv Q ι A hA a : QuadraticMap.orthogonalGroup Q) :
        V ≃ₗ[ZMod p] V) = ggLin (p := p) ι (a : MulAut ↥Bs) := rfl

theorem ggWeylReflectionGroup_of_orth_plus {G : Type} [Group G] {Bs : Subgroup G} {p : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (Q : QuadraticForm (ZMod p) V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) [Fact p.Prime] (hp3 : p = 3)
    (hd : Module.finrank (ZMod p) V = 4)
    (hplus : ∃ W : Submodule (ZMod p) V, Module.finrank (ZMod p) W = 2 ∧ ∀ w ∈ W, Q w = 0)
    (ι : Additive ↥Bs ≃+ V) (A : Subgroup (MulAut ↥Bs))
    (hA : ∀ g : V ≃ₗ[ZMod p] V, (∃ a ∈ A, ggLin (p := p) ι a = g) ↔ ∀ v, Q (g v) = Q v) :
    GGWeylReflectionGroup p A := by
  subst hp3
  classical
  have hdim : 0 < Module.finrank (ZMod 3) V := by rw [hd]; norm_num
  have : FiniteDimensional (ZMod 3) V := FiniteDimensional.of_finrank_pos hdim
  have : Fintype (Module.Basis.ofVectorSpaceIndex (ZMod 3) V) := inferInstance
  have : Fintype V := Fintype.ofEquiv _
    (Module.Basis.ofVectorSpace (ZMod 3) V).equivFun.toEquiv.symm
  obtain ⟨e, he⟩ := f4Model_isometric Q hQ hd hplus
  let eIso : Q.IsometryEquiv f4ModelForm := { e with map_app' := he }
  obtain ⟨Φ, hΦsurj, hΦrefl⟩ := f4Model_hom
  let conjInv : QuadraticMap.orthogonalGroup f4ModelForm ≃*
      QuadraticMap.orthogonalGroup Q := QuadraticMap.orthogonalGroupCongr eIso.symm
  let Φ' : (CoxeterMatrix.F₄).Group →* QuadraticMap.orthogonalGroup Q :=
    conjInv.toMonoidHom.comp Φ
  have hΦ'surj : Function.Surjective Φ' := by
    intro y
    obtain ⟨x, hx⟩ := hΦsurj (conjInv.symm y)
    exact ⟨x, by
      change conjInv (Φ x) = y
      rw [hx, MulEquiv.apply_symm_apply]⟩
  have hcardC : Nat.card (CoxeterMatrix.F₄).Group = 1152 := ct_oj_card_coxeterF4
  have hcardO : Nat.card (QuadraticMap.orthogonalGroup Q) = 1152 :=
    card_orthogonalGroup_four_plus Q hQ hd hplus
  have : Finite (CoxeterMatrix.F₄).Group :=
    Nat.finite_of_card_ne_zero (by rw [hcardC]; norm_num)
  have hbij : Function.Bijective Φ' :=
    hΦ'surj.bijective_of_nat_card_le (by rw [hcardC, hcardO])
  let eC : (CoxeterMatrix.F₄).Group ≃* QuadraticMap.orthogonalGroup Q :=
    MulEquiv.ofBijective Φ' hbij
  let eA : ↥A ≃* QuadraticMap.orthogonalGroup Q := ct_oj_orthEquiv Q ι A hA
  let f : (CoxeterMatrix.F₄).Group ≃* ↥A := eC.trans eA.symm
  refine ⟨Fin 4, CoxeterMatrix.F₄, ?_, f, ?_⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨Equiv.refl (Fin 4), by ext j k; rfl⟩))))
  · intro i
    let s : (CoxeterMatrix.F₄).Group := (CoxeterMatrix.F₄).simple i
    obtain ⟨c, hc, horth⟩ := hΦrefl i
    have horthQ : OrthReflOfNorm Q c (conjInv (Φ s) : V ≃ₗ[ZMod 3] V) := by
      simpa [conjInv] using ct_oj_orthReflOfNorm_map
        (e := eIso.symm) (h := horth)
        (hgmem := (Φ s : QuadraticMap.orthogonalGroup f4ModelForm).2)
    have hggLin : ggLin (p := 3) ι ((f s : ↥A) : MulAut ↥Bs) =
        (conjInv (Φ s) : V ≃ₗ[ZMod 3] V) := by
      have happ : eA (f s) = eC s := by
        change eA (eA.symm (eC s)) = eC s
        rw [MulEquiv.apply_symm_apply]
      rw [← ct_oj_orthEquiv_apply_coe Q ι A hA (f s)]
      rw [happ]
      rfl
    have hmem : ggLin (p := 3) ι ((f s : ↥A) : MulAut ↥Bs) ∈
        QuadraticMap.orthogonalGroup Q := by
      rw [hggLin]
      exact (conjInv (Φ s)).2
    have hG : GGLinRefl (ggLin (p := 3) ι ((f s : ↥A) : MulAut ↥Bs)) := by
      unfold GGLinRefl
      exact (linRefl_iff_orthRefl hQ hmem).mpr ⟨c, hc, by rwa [hggLin]⟩
    exact (ggIsReflection_iff_ggLinRefl (p := 3) (by norm_num) ι
      ((f s : ↥A) : MulAut ↥Bs)).mpr hG

end CFSG.StandardType.OrthF3

end
