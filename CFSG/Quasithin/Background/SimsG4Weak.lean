module

public import CFSG.Quasithin.Background.SimsG4Sp
import CFSG.Quasithin.Background.SimsG4Core
import CFSG.Quasithin.Vol2.GoldschmidtSp4C2WireBase

public section

namespace CFSG.Quasithin.SimsG4

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp glMat)
open CFSG.Quasithin.Ch3E213M (natAct natLin spBil subfieldSp IsIrreducibleSp4)

theorem weak_form
    {F : Type} [Field F] [Finite F] [CharP F 2] (n : ℕ) (hn : Nat.card F = 2 ^ n)
    {V : Type} [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V)
    (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hdim : Module.finrank F V = 4)
    (G₀ : Subgroup (V ≃ₗ[F] V)) (hSp : G₀ ≤ spGroup B) (hirr : IsIrredOnV G₀)
    (hD : (transvSet G₀).Nonempty) :
    (∃ (b : Module.Basis (Fin 4) F V) (F₀ : Subfield F), IsSympBasis B b ∧
        ∀ g : V ≃ₗ[F] V, g ∈ G₀ ↔ g ∈ spGroup B ∧ g ∈ subfieldSpOf b F₀) ∨
      (∃ Q : QuadraticForm F V, (∀ x y, QuadraticMap.polar Q x y = B x y) ∧
        ∀ g ∈ G₀, ∀ x, Q (g x) = Q x) ∨
      (∃ V₁ V₂ : Submodule F V, Module.finrank F V₁ = 2 ∧
        V₂ = LinearMap.BilinForm.orthogonal B V₁ ∧ V₁ ⊓ V₂ = ⊥ ∧
        ∀ g ∈ G₀, (V₁.map (g : V →ₗ[F] V) = V₁ ∧ V₂.map (g : V →ₗ[F] V) = V₂) ∨
          (V₁.map (g : V →ₗ[F] V) = V₂ ∧ V₂.map (g : V →ₗ[F] V) = V₁)) := by
  obtain ⟨b, hb⟩ := exists_isSympBasis B halt hnd hdim
  let f : antiSp F →* (V ≃ₗ[F] V) := (spGroup B).subtype.comp (spCoord B b hb).symm.toMonoidHom
  have hf : ∀ x : spGroup B, f (spCoord B b hb x) = x := fun x => by simp [f]
  let G₁ : Subgroup (antiSp F) := G₀.comap f
  have hmem : ∀ g (hg : g ∈ G₀), spCoord B b hb ⟨g, hSp hg⟩ ∈ G₁ := fun g hg => by
    change f _ ∈ G₀
    rw [hf]
    exact hg
  have hact : ∀ g (hg : g ∈ G₀) x,
      CFSG.Quasithin.Ch3E213M.natAct (spCoord B b hb ⟨g, hSp hg⟩) (b.equivFun x) = b.equivFun (g x) :=
    fun g hg x => natAct_spCoord B b hb ⟨g, hSp hg⟩ x
  have hirr₁ : IsIrreducibleSp4 G₁ := by
    intro W hW
    have hinv : ∀ g ∈ G₀, ∀ w ∈ W.comap (b.equivFun : V →ₗ[F] (Fin 4 → F)),
        g w ∈ W.comap (b.equivFun : V →ₗ[F] (Fin 4 → F)) := by
      intro g hg w hw
      rw [Submodule.mem_comap, LinearEquiv.coe_coe] at hw ⊢
      rw [← hact g hg]
      exact hW _ (hmem g hg) _ hw
    have hpull : ∀ x, b.equivFun.symm x ∈ W.comap (b.equivFun : V →ₗ[F] (Fin 4 → F)) ↔ x ∈ W :=
      fun x => by rw [Submodule.mem_comap, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rcases hirr _ hinv with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      rw [← hpull, h, Submodule.mem_bot] at hx
      rw [Submodule.mem_bot, ← b.equivFun.apply_symm_apply x, hx, map_zero]
    · right
      rw [eq_top_iff]
      intro x _
      rw [← hpull, h]
      exact Submodule.mem_top
  have hD₁ : (Ch3E213M.transvSet G₁).Nonempty := by
    obtain ⟨d, hdG, hdT⟩ := hD
    refine ⟨spCoord B b hb ⟨d, hSp hdG⟩, hmem d hdG, fun h1 => ?_, ?_⟩
    · apply transv_ne_one d hdT
      have h2 := congrArg f h1
      rwa [hf, map_one] at h2
    · have hkey : Matrix.toLin' (glMat (spCoord B b hb ⟨d, hSp hdG⟩ : GL (Fin 4) F) - 1) ∘ₗ
            (b.equivFun : V →ₗ[F] (Fin 4 → F)) =
          (b.equivFun : V →ₗ[F] (Fin 4 → F)) ∘ₗ ((d : V →ₗ[F] V) - LinearMap.id) := by
        refine LinearMap.ext fun x => ?_
        rw [LinearMap.comp_apply, LinearMap.comp_apply, Ch3E213M.G41.toLin'_sub_one_apply]
        simp only [LinearEquiv.coe_coe, hact d hdG, LinearMap.sub_apply, LinearMap.id_apply,
          map_sub]
      have hrank : Module.finrank F (LinearMap.range (Matrix.toLin'
          (glMat (spCoord B b hb ⟨d, hSp hdG⟩ : GL (Fin 4) F) - 1))) = 1 := by
        rw [← LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range b.equivFun), hkey,
          LinearMap.range_comp, LinearEquiv.finrank_map_eq]
        exact hdT.1
      exact hrank
  rcases Ch3E213M.Sp4C2.factSp4TransvW_holds F n hn G₁ hirr₁ hD₁ with hS | hO | hDec
  ·
    left
    obtain ⟨F₀, h, hGh⟩ := hS
    obtain ⟨γ, hγ⟩ : ∃ γ : spGroup B, γ = (spCoord B b hb).symm h := ⟨_, rfl⟩
    have hh : h = spCoord B b hb γ := by rw [hγ, MulEquiv.apply_symm_apply]
    have hmat : ∀ (g : V ≃ₗ[F] V) (hg : g ∈ spGroup B),
        LinearMap.toMatrix (b.map (γ : V ≃ₗ[F] V)) (b.map (γ : V ≃ₗ[F] V)) (g : V →ₗ[F] V) =
          glMat ((h⁻¹ * spCoord B b hb ⟨g, hg⟩ * h : antiSp F) : GL (Fin 4) F) := by
      intro g hg
      rw [hh, ← map_inv, ← map_mul, ← map_mul, glMat_spCoord]
      ext i j
      rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, Module.Basis.map_repr,
        Module.Basis.map_apply]
      rfl
    refine ⟨b.map (γ : V ≃ₗ[F] V), F₀, fun i j => ?_, fun g => ⟨fun hg => ?_, fun hg => ?_⟩⟩
    · rw [Module.Basis.map_apply, Module.Basis.map_apply]
      exact (γ.2 (b i) (b j)).trans (hb i j)
    · refine ⟨hSp hg, fun i j => ?_⟩
      have h1 : spCoord B b hb ⟨g, hSp hg⟩ ∈
          (subfieldSp F₀).map (MulAut.conj h).toMonoidHom := hGh ▸ hmem g hg
      obtain ⟨s, hs, hs'⟩ := Subgroup.mem_map.mp h1
      have h2 : h⁻¹ * spCoord B b hb ⟨g, hSp hg⟩ * h = s := by
        rw [← hs', MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [hmat g (hSp hg), h2]
      exact hs i j
    · obtain ⟨hgSp, hgF⟩ := hg
      have hs : h⁻¹ * spCoord B b hb ⟨g, hgSp⟩ * h ∈ subfieldSp F₀ := fun i j => by
        rw [← hmat g hgSp]
        exact hgF i j
      have h1 : spCoord B b hb ⟨g, hgSp⟩ ∈ G₁ := by
        rw [hGh]
        refine Subgroup.mem_map.mpr ⟨_, hs, ?_⟩
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      have h2 : f (spCoord B b hb ⟨g, hgSp⟩) ∈ G₀ := h1
      rwa [hf] at h2
  ·
    right
    left
    obtain ⟨Q', hpolar, hinv⟩ := hO
    refine ⟨Q'.comp (b.equivFun : V →ₗ[F] (Fin 4 → F)), fun x y => ?_, fun g hg x => ?_⟩
    · have hcomp : QuadraticMap.polar (Q'.comp (b.equivFun : V →ₗ[F] (Fin 4 → F))) x y =
          QuadraticMap.polar Q' (b.equivFun x) (b.equivFun y) := by
        simp only [QuadraticMap.polar, QuadraticMap.comp_apply, LinearEquiv.coe_coe, map_add]
      rw [hcomp, hpolar, spBil_equivFun B b hb]
    · simp only [QuadraticMap.comp_apply, LinearEquiv.coe_coe]
      rw [← hact g hg, hinv _ (hmem g hg)]
  ·
    right
    right
    obtain ⟨W₁, W₂, h1, h2, h3, h4⟩ := hDec
    subst h2
    refine ⟨W₁.map (b.equivFun.symm : (Fin 4 → F) →ₗ[F] V),
      (LinearMap.BilinForm.orthogonal spBil W₁).map (b.equivFun.symm : (Fin 4 → F) →ₗ[F] V),
      ?_, ?_, ?_, fun g hg => ?_⟩
    · rw [LinearEquiv.finrank_map_eq]
      exact h1
    · ext y
      rw [Submodule.mem_map_equiv, LinearEquiv.symm_symm,
        LinearMap.BilinForm.mem_orthogonal_iff, LinearMap.BilinForm.mem_orthogonal_iff]
      constructor
      · intro H n hn
        rw [Submodule.mem_map_equiv, LinearEquiv.symm_symm] at hn
        rw [← spBil_equivFun B b hb]
        exact H _ hn
      · intro H n hn
        have hn' : b.equivFun.symm n ∈ W₁.map (b.equivFun.symm : (Fin 4 → F) →ₗ[F] V) := by
          rw [Submodule.mem_map_equiv, LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply]
          exact hn
        have := H _ hn'
        rwa [← spBil_equivFun B b hb, LinearEquiv.apply_symm_apply] at this
    · rw [← Submodule.map_inf (b.equivFun.symm : (Fin 4 → F) →ₗ[F] V) b.equivFun.symm.injective,
        h3, Submodule.map_bot]
    · have hcomm : ∀ W : Submodule F (Fin 4 → F),
          (W.map (b.equivFun.symm : (Fin 4 → F) →ₗ[F] V)).map (g : V →ₗ[F] V) =
            (W.map (natLin (spCoord B b hb ⟨g, hSp hg⟩))).map
              (b.equivFun.symm : (Fin 4 → F) →ₗ[F] V) := by
        intro W
        rw [← Submodule.map_comp, ← Submodule.map_comp]
        congr 1
        refine LinearMap.ext fun x => ?_
        rw [LinearMap.comp_apply, LinearMap.comp_apply, Ch3E213M.G41.natLin_apply']
        apply b.equivFun.injective
        rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, ← hact g hg,
          LinearEquiv.apply_symm_apply]
      rw [hcomm W₁, hcomm]
      rcases h4 _ (hmem g hg) with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact Or.inl ⟨by rw [e1], by rw [e2]⟩
      · exact Or.inr ⟨by rw [e1], by rw [e2]⟩

end CFSG.Quasithin.SimsG4
