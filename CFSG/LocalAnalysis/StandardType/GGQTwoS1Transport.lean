module

public import CFSG.LocalAnalysis.StandardType.GGQTwoReflOrth
public import CFSG.LocalAnalysis.StandardType.GGQTwoInvForm
public import CFSG.LocalAnalysis.StandardType.GGQTwoTransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

private lemma ggQ2xS1_eq_one_or_neg_one (a : ZMod 3) (ha : a ≠ 0) : a = 1 ∨ a = -1 :=
  (by decide : ∀ a : ZMod 3, a ≠ 0 → a = 1 ∨ a = -1) a ha

private lemma ggQ2xS1_simplePair_mem (D : GGQ2Lin 3) (k : D.ι) :
    (D.root k, D.coroot k) ∈ D.rootPairs :=
  ⟨k, 1, D.weyl.one_mem, rfl, by
    change D.root k = (D.root k).comp (LinearMap.id : D.V →ₗ[ZMod 3] D.V)
    rw [LinearMap.comp_id]⟩

private lemma ggQ2xS1_cast_ne_zero (D : GGQ2Lin 3) (hsym : ∀ i j, D.cartan i j = D.cartan j i)
    {i j : D.ι} (hij : i ≠ j) (h : D.cartan i j ≠ 0) : (D.cartan i j : ZMod 3) ≠ 0 := by
  rcases D.isCartan.2 i j hij with ⟨-, h1, -⟩ | ⟨-, h1, -⟩ | ⟨-, h1, h2, h3⟩ |
    ⟨-, h1, h2, h3⟩
  · exact absurd h1 h
  · rw [h1]; decide
  · exfalso
    have hs : D.cartan i j = D.cartan j i := hsym i j
    rw [← hs] at h1
    have hc : ((D.cartan i j : ZMod 4)) * (D.cartan i j : ZMod 4) = 2 := by
      have hh := congrArg (fun z : ℤ => (z : ZMod 4)) h1
      push_cast at hh
      exact hh
    exact (by decide : ∀ a : ZMod 4, a * a ≠ 2) _ hc
  · exfalso
    have hs : D.cartan i j = D.cartan j i := hsym i j
    rw [← hs] at h1
    have hc : ((D.cartan i j : ZMod 4)) * (D.cartan i j : ZMod 4) = 3 := by
      have hh := congrArg (fun z : ℤ => (z : ZMod 4)) h1
      push_cast at hh
      exact hh
    exact (by decide : ∀ a : ZMod 4, a * a ≠ 3) _ hc

private lemma ggQ2xS1_reflTransGen_eq {α : Type*} {r : α → α → Prop} {f : α → ZMod 3}
    (hstep : ∀ a b, r a b → f a = f b) {a b : α} (h : Relation.ReflTransGen r a b) :
    f a = f b := by
  induction h with
  | refl => rfl
  | tail hab hbc ih => exact ih.trans (hstep _ _ hbc)

private theorem ggQ2xS1_form_eq (D : GGQ2Lin 3) (hbas : D.Basis)
    (h4 : 4 ≤ Fintype.card D.ι)
    (hsym : ∀ i j, D.cartan i j = D.cartan j i)
    {V' : Type} [AddCommGroup V'] [Module (ZMod 3) V'] (τ : D.V ≃ₗ[ZMod 3] V')
    (B' : LinearMap.BilinForm (ZMod 3) V')
    (hB' : ∀ i j, B' (τ (D.coroot i)) (τ (D.coroot j)) = (D.cartan i j : ZMod 3))
    (β : LinearMap.BilinForm (ZMod 3) D.V) (hβ : β.IsSymm)
    (d : ↥D.rootPairs → ZMod 3) (hd : ∀ γ, d γ ≠ 0)
    (hβh : ∀ γ v, β γ.1.2 v = d γ * γ.1.1 v) :
    ∃ lam : ZMod 3, lam ≠ 0 ∧ ∀ u v, β u v = lam * B' (τ u) (τ v) := by
  classical
  haveI : Nonempty D.ι := Fintype.card_pos_iff.mp (by omega)
  let pair : D.ι → ↥D.rootPairs := fun i =>
    ⟨(D.root i, D.coroot i), ggQ2xS1_simplePair_mem D i⟩
  let di : D.ι → ZMod 3 := fun i => d (pair i)
  have hdi_ne : ∀ i, di i ≠ 0 := fun i => hd (pair i)
  have hβhi : ∀ i v, β (D.coroot i) v = di i * D.root i v := fun i v => hβh (pair i) v
  have hsymm : ∀ i j, di i * (D.cartan i j : ZMod 3) = di j * (D.cartan j i : ZMod 3) := by
    intro i j
    have h1 : β (D.coroot i) (D.coroot j) = di i * (D.cartan i j : ZMod 3) := by
      rw [hβhi i (D.coroot j), D.pairing]
    have h2 : β (D.coroot i) (D.coroot j) = β (D.coroot j) (D.coroot i) := hβ.eq _ _
    have h3 : β (D.coroot j) (D.coroot i) = di j * (D.cartan j i : ZMod 3) := by
      rw [hβhi j (D.coroot i), D.pairing]
    rw [← h1, h2, h3]
  have hstep : ∀ i j, i ≠ j → D.cartan i j ≠ 0 → di i = di j := by
    intro i j hij hcij
    have h := hsymm i j
    rw [← hsym i j] at h
    exact mul_right_cancel₀ (ggQ2xS1_cast_ne_zero D hsym hij hcij) h
  have hconn : (TauCeti.diagramGraph D.cartan).Connected :=
    connected_diagramGraph_of_ggIsWeylMatrix D.isWeyl D.isCartan
  let i₀ : D.ι := Classical.arbitrary D.ι
  have hconst : ∀ i, di i = di i₀ := by
    intro i
    have hreach : Relation.ReflTransGen (TauCeti.diagramGraph D.cartan).Adj i₀ i :=
      (SimpleGraph.reachable_iff_reflTransGen i₀ i).mp (hconn.preconnected i₀ i)
    exact (ggQ2xS1_reflTransGen_eq (r := (TauCeti.diagramGraph D.cartan).Adj) (f := di)
      (fun a b hab => by
        obtain ⟨hne, hcij, -⟩ := (TauCeti.diagramGraph_adj).mp hab
        exact hstep a b hne hcij) hreach).symm
  let lam : ZMod 3 := di i₀
  let b : Basis D.ι (ZMod 3) D.V := basisOfLinearIndependentOfCardEqFinrank hbas.1 hbas.2
  have hb : ⇑b = D.coroot := coe_basisOfLinearIndependentOfCardEqFinrank hbas.1 hbas.2
  let β₂ : LinearMap.BilinForm (ZMod 3) D.V :=
    LinearMap.BilinForm.comp B' (τ : D.V →ₗ[ZMod 3] V') (τ : D.V →ₗ[ZMod 3] V')
  have hβ₂ : ∀ u v, β₂ u v = B' (τ u) (τ v) :=
    fun u v => LinearMap.BilinForm.comp_apply B' _ _ u v
  have hkey : ∀ i j, β (D.coroot i) (D.coroot j) =
      lam * B' (τ (D.coroot i)) (τ (D.coroot j)) := by
    intro i j
    rw [hβhi i (D.coroot j), D.pairing i j, hB' i j, hconst i]
  have hβeq : β = lam • β₂ := by
    apply LinearMap.BilinForm.ext_basis b
    intro i j
    rw [congrFun hb i, congrFun hb j]
    simp only [LinearMap.smul_apply, smul_eq_mul, hβ₂, hkey i j]
  refine ⟨lam, hdi_ne i₀, fun u v => ?_⟩
  rw [hβeq]
  simp only [LinearMap.smul_apply, smul_eq_mul, hβ₂]

theorem ggQ2_S1_transport (D : GGQ2Lin 3) (hbas : D.Basis) (h4 : 4 ≤ Fintype.card D.ι)
    (hsym : ∀ i j, D.cartan i j = D.cartan j i) {V' : Type} [AddCommGroup V']
    [Module (ZMod 3) V'] (τ : D.V ≃ₗ[ZMod 3] V') (B' : LinearMap.BilinForm (ZMod 3) V')
    (hB' : ∀ i j, B' (τ (D.coroot i)) (τ (D.coroot j)) = (D.cartan i j : ZMod 3))
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    {c : V'} {φ : Module.Dual (ZMod 3) V'} (h : φ c = 2)
    (ht : Module.reflection h ∈ A.map (ggLinConj τ).toMonoidHom) :
    ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧ ∀ v, φ v = ε * B' c v := by
  classical
  obtain ⟨β, d, hβ, hd, hβh⟩ := ggQ2_exists_invariantForm (p := 3) rfl D hbas h4
  obtain ⟨lam, hlam_ne, hlam⟩ := ggQ2xS1_form_eq D hbas h4 hsym τ B' hB' β hβ d hd hβh
  obtain ⟨g, hgA, hg_eq⟩ := Subgroup.mem_map.mp ht
  let h' : Module.Dual (ZMod 3) D.V := φ.comp (τ : D.V →ₗ[ZMod 3] V')
  have hh' : h' (τ.symm c) = 2 := by
    change φ (τ (τ.symm c)) = 2
    rw [LinearEquiv.apply_symm_apply]
    exact h
  have hg_refl : g = Module.reflection hh' := by
    ext w
    apply τ.injective
    have h1 : τ (g w) = (Module.reflection h) (τ w) := by
      have hh := DFunLike.congr_fun hg_eq (τ w)
      change ggLinConj τ g (τ w) = (Module.reflection h) (τ w) at hh
      rwa [ggLinConj_apply, LinearEquiv.symm_apply_apply] at hh
    rw [h1, Module.reflection_apply (τ w) h, Module.reflection_apply w hh',
      map_sub, map_smul, LinearEquiv.apply_symm_apply]
    rfl
  have hgA' : Module.reflection hh' ∈ A := by rw [← hg_refl]; exact hgA
  obtain ⟨ε'', hε'', hφ''⟩ :=
    ggQ2_refl_orthogonal (p := 3) rfl D hbas h4 β hβ d hd hβh A hW hTF
      (c := τ.symm c) (φ := h') hh' hgA'
  refine ⟨ε'' * lam, ?_, ?_⟩
  · rcases hε'' with h1 | h1 <;>
      rcases ggQ2xS1_eq_one_or_neg_one lam hlam_ne with h2 | h2 <;>
        rw [h1, h2] <;> decide
  · intro v
    have h1 := hφ'' (τ.symm v)
    have h2 : h' (τ.symm v) = φ v := by
      change φ (τ (τ.symm v)) = φ v
      rw [LinearEquiv.apply_symm_apply]
    rw [h2, hlam (τ.symm c) (τ.symm v)] at h1
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h1
    rw [h1, mul_assoc]

end CFSG.StandardType

end
