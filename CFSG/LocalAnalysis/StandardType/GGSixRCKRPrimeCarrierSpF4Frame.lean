module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCarrierSpF4Torus
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleSplit
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.C3AlgebraicPart2
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.B3AlgebraicPart3
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RationalC3Part2
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RationalB3Part1
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.SelectedLiteralPart2

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.ComponentClassification.CatLeafProof CFSG.SeitzReduction.F4Pilot


variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] [Algebra (ZMod 2) L]
  [Algebra.IsAlgebraic (ZMod 2) L]

theorem exists_spFrame_of_adjoint {n : ℕ} {S : Set (Fin Tag.F4.rank → ℤ)}
    (ι : ↥(StatedSp n L) →* ↥(adjointGroup Tag.F4 L)) (hinj : Function.Injective ι)
    (hrange : MonoidHom.range ((adjointGroup Tag.F4 L).subtype.comp ι)
      = rootSpan Tag.F4 L S)
    (hnat : ∀ (σ : L ≃+* L) (X : ↥(StatedSp n L)),
      frobGL (τ := Tag.F4) σ (((adjointGroup Tag.F4 L).subtype.comp ι) X)
        = ((adjointGroup Tag.F4 L).subtype.comp ι) (statedSpMap (σ : L →+* L) n X))
    (htor : ∀ t ∈ torusGroup Tag.F4 L, ∃ t₁ ∈ rootSpan Tag.F4 L S,
      ∀ g ∈ rootSpan Tag.F4 L S, t * g * t⁻¹ = t₁ * g * t₁⁻¹) :
    ∃ ι₀ : ↥(StatedSp n L) →* ModGL Tag.F4 L, Function.Injective ι₀ ∧
      ι₀.range = rootSpan Tag.F4 L S ∧
      (∀ (σ : L ≃+* L) (X : ↥(StatedSp n L)),
        frobGL (τ := Tag.F4) σ (ι₀ X) = ι₀ (statedSpMap (σ : L →+* L) n X)) ∧
      ∀ t ∈ torusGroup Tag.F4 L, ∃ W : ↥(StatedSp n L), ∀ X,
        t * ι₀ X * t⁻¹ = ι₀ (W * X * W⁻¹) := by
  let ι₀ : ↥(StatedSp n L) →* ModGL Tag.F4 L := (adjointGroup Tag.F4 L).subtype.comp ι
  have hinj₀ : Function.Injective ι₀ :=
    (adjointGroup Tag.F4 L).subtype_injective.comp hinj
  have htor' : ∀ t ∈ torusGroup Tag.F4 L, ∃ W : ↥(StatedSp n L), ∀ X,
      t * ι₀ X * t⁻¹ = ι₀ (W * X * W⁻¹) := by
    intro t ht
    obtain ⟨t₁, ht₁, hconj⟩ := htor t ht
    have ht₁' : t₁ ∈ ι₀.range := by rw [hrange]; exact ht₁
    obtain ⟨W, hW⟩ := ht₁'
    refine ⟨W, fun X => ?_⟩
    have hX : ι₀ X ∈ rootSpan Tag.F4 L S := by
      rw [← hrange]
      exact MonoidHom.mem_range.mpr ⟨X, rfl⟩
    rw [hconj (ι₀ X) hX, ← hW, ← map_mul, ← map_inv, ← map_mul]
  exact ⟨ι₀, hinj₀, hrange, hnat, htor'⟩

private theorem exists_baseFrame_c3 {J : Set (Fin Tag.F4.rank)} (hJ : J = f4LeviC3) :
    ∃ ι₀ : ↥(StatedSp 3 L) →* ModGL Tag.F4 L, Function.Injective ι₀ ∧
      ι₀.range = rootSpan Tag.F4 L (parabolicRoots Tag.F4 J) ∧
      (∀ (σ : L ≃+* L) (X : ↥(StatedSp 3 L)),
        frobGL (τ := Tag.F4) σ (ι₀ X) = ι₀ (statedSpMap (σ : L →+* L) 3 X)) ∧
      ∀ t ∈ torusGroup Tag.F4 L, ∃ W : ↥(StatedSp 3 L), ∀ X,
        t * ι₀ X * t⁻¹ = ι₀ (W * X * W⁻¹) := by
  have hrange : MonoidHom.range ((adjointGroup Tag.F4 L).subtype.comp
      (CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOmega L))
      = rootSpan Tag.F4 L (parabolicRoots Tag.F4 J) := by
    rw [hJ, CFSG.StandardType.F4ExplicitPos.SelectedLiteral.parabolicRoots_f4LeviC3_eq_c3RootSet]
    exact CFSG.StandardType.F4ExplicitPos.C3Algebraic.range_eq_rootSpan_alg
      (CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOmega L)
      (fun γ c => CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOmega_x L γ c)
  have hnat : ∀ (σ : L ≃+* L) (X : ↥(StatedSp 3 L)),
      frobGL (τ := Tag.F4) σ (((adjointGroup Tag.F4 L).subtype.comp
        (CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOmega L)) X)
        = ((adjointGroup Tag.F4 L).subtype.comp
            (CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOmega L))
          (statedSpMap (σ : L →+* L) 3 X) := by
    intro σ X
    change frobGL (τ := Tag.F4) σ
        (((CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOmega L X :
          ↥(adjointGroup Tag.F4 L)) : ModGL Tag.F4 L)) =
      (((CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOmega L
          (statedSpMap (σ : L →+* L) 3 X) : ↥(adjointGroup Tag.F4 L)) : ModGL Tag.F4 L))
    rw [CFSG.StandardType.F4ExplicitPos.RankThreeModels.frobGL_eq_bcGL (Ω := L) σ]
    exact congrArg (fun z : ↥(adjointGroup Tag.F4 L) => (z : ModGL Tag.F4 L))
      (CFSG.StandardType.F4ExplicitPos.RationalC3.iOmega_natural_apply
        (Ω := L) (σ : L →+* L) X)
  exact exists_spFrame_of_adjoint _ (CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOmega_injective L)
    hrange hnat (fun t ht => exists_mem_rootSpan_conj_eq_f4Levi (Or.inr hJ) ht)

private theorem exists_baseFrame_b3 {J : Set (Fin Tag.F4.rank)} (hJ : J = f4LeviB3) :
    ∃ ι₀ : ↥(StatedSp 3 L) →* ModGL Tag.F4 L, Function.Injective ι₀ ∧
      ι₀.range = rootSpan Tag.F4 L (parabolicRoots Tag.F4 J) ∧
      (∀ (σ : L ≃+* L) (X : ↥(StatedSp 3 L)),
        frobGL (τ := Tag.F4) σ (ι₀ X) = ι₀ (statedSpMap (σ : L →+* L) 3 X)) ∧
      ∀ t ∈ torusGroup Tag.F4 L, ∃ W : ↥(StatedSp 3 L), ∀ X,
        t * ι₀ X * t⁻¹ = ι₀ (W * X * W⁻¹) := by
  have hrange : MonoidHom.range ((adjointGroup Tag.F4 L).subtype.comp
      (CFSG.StandardType.F4ExplicitPos.B3Algebraic.iBΩ L))
      = rootSpan Tag.F4 L (parabolicRoots Tag.F4 J) := by
    rw [hJ, CFSG.StandardType.F4ExplicitPos.SelectedLiteral.parabolicRoots_f4LeviB3_eq_b3LeviRoots]
    exact CFSG.StandardType.F4ExplicitPos.B3Algebraic.iBΩ_map_range L
  have hnat : ∀ (σ : L ≃+* L) (X : ↥(StatedSp 3 L)),
      frobGL (τ := Tag.F4) σ (((adjointGroup Tag.F4 L).subtype.comp
        (CFSG.StandardType.F4ExplicitPos.B3Algebraic.iBΩ L)) X)
        = ((adjointGroup Tag.F4 L).subtype.comp
            (CFSG.StandardType.F4ExplicitPos.B3Algebraic.iBΩ L))
          (statedSpMap (σ : L →+* L) 3 X) := by
    intro σ X
    change frobGL (τ := Tag.F4) σ
        (((CFSG.StandardType.F4ExplicitPos.B3Algebraic.iBΩ L X :
          ↥(adjointGroup Tag.F4 L)) : ModGL Tag.F4 L)) =
      (((CFSG.StandardType.F4ExplicitPos.B3Algebraic.iBΩ L
          (statedSpMap (σ : L →+* L) 3 X) : ↥(adjointGroup Tag.F4 L)) : ModGL Tag.F4 L))
    rw [CFSG.StandardType.F4ExplicitPos.RankThreeModels.frobGL_eq_bcGL (Ω := L) σ]
    exact congrArg (fun z : ↥(adjointGroup Tag.F4 L) => (z : ModGL Tag.F4 L))
      (CFSG.StandardType.F4ExplicitPos.B3Naturality.iBΩ_natural_apply
        (Ω := L) (σ : L →+* L) X)
  exact exists_spFrame_of_adjoint _ (CFSG.StandardType.F4ExplicitPos.B3Algebraic.iBΩ_injective L)
    hrange hnat (fun t ht => exists_mem_rootSpan_conj_eq_f4Levi (Or.inl hJ) ht)

theorem exists_spFrame_conj (v : WeylGroup Tag.F4) {n : ℕ}
    {S : Set (Fin Tag.F4.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot Tag.F4 α)
    (ι₀ : ↥(StatedSp n L) →* ModGL Tag.F4 L) (hinj : Function.Injective ι₀)
    (hrange : ι₀.range = rootSpan Tag.F4 L S)
    (hnat : ∀ (σ : L ≃+* L) (X : ↥(StatedSp n L)),
      frobGL (τ := Tag.F4) σ (ι₀ X) = ι₀ (statedSpMap (σ : L →+* L) n X))
    (htor : ∀ t ∈ torusGroup Tag.F4 L, ∃ W : ↥(StatedSp n L), ∀ X,
      t * ι₀ X * t⁻¹ = ι₀ (W * X * W⁻¹)) :
    ∃ ψ : ↥(StatedSp n L) →* ModGL Tag.F4 L, Function.Injective ψ ∧
      ψ.range = rootSpan Tag.F4 L ((fun α => v • α) '' S) ∧
      (∀ (σ : L ≃+* L) (X : ↥(StatedSp n L)),
        frobGL (τ := Tag.F4) σ (ψ X) = ψ (statedSpMap (σ : L →+* L) n X)) ∧
      ∀ t ∈ torusGroup Tag.F4 L, ∃ W : ↥(StatedSp n L), ∀ X,
        t * ψ X * t⁻¹ = ψ (W * X * W⁻¹) := by
  let n' : ModGL Tag.F4 L := canonicalRep (coxeterSystem Tag.F4) L v
  let ψ : ↥(StatedSp n L) →* ModGL Tag.F4 L := (MulAut.conj n').toMonoidHom.comp ι₀
  have hψinj : Function.Injective ψ := (MulAut.conj n').injective.comp hinj
  have hψrange : ψ.range =
      rootSpan Tag.F4 L ((fun α => v • α) '' S) := by
    rw [show ψ = (MulAut.conj n').toMonoidHom.comp ι₀ from rfl, MonoidHom.range_comp, hrange]
    exact (canonical_weyl_root_transport Tag.F4 L).1 v S hS
  have hψnat : ∀ (σ : L ≃+* L) (X : ↥(StatedSp n L)),
      frobGL (τ := Tag.F4) σ (ψ X) = ψ (statedSpMap (σ : L →+* L) n X) := by
    intro σ X
    have hn : frobGL (τ := Tag.F4) σ n' = n' :=
      CFSG.LieType.Chevalley.entrywise_canonicalRep (τ := Tag.F4) (K := L) σ v
    change frobGL (τ := Tag.F4) σ (n' * ι₀ X * n'⁻¹) =
      n' * ι₀ (statedSpMap (σ : L →+* L) n X) * n'⁻¹
    rw [map_mul, map_mul, map_inv, hn, hnat σ X]
  have hψtor : ∀ t ∈ torusGroup Tag.F4 L, ∃ W : ↥(StatedSp n L), ∀ X,
      t * ψ X * t⁻¹ = ψ (W * X * W⁻¹) := by
    intro t ht
    have hnN : n' ∈ Subgroup.normalizer (torusGroup Tag.F4 L : Set (ModGL Tag.F4 L)) :=
      (canonical_weyl_root_transport Tag.F4 L).2.2 v
    have ht' : n'⁻¹ * t * n' ∈ torusGroup Tag.F4 L := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hnN) t).1 ht
      rwa [inv_inv] at this
    obtain ⟨W, hW⟩ := htor (n'⁻¹ * t * n') ht'
    refine ⟨W, fun X => ?_⟩
    change t * (n' * ι₀ X * n'⁻¹) * t⁻¹ = n' * ι₀ (W * X * W⁻¹) * n'⁻¹
    calc
      t * (n' * ι₀ X * n'⁻¹) * t⁻¹
          = n' * ((n'⁻¹ * t * n') * ι₀ X * (n'⁻¹ * t * n')⁻¹) * n'⁻¹ := by group
        _ = n' * ι₀ (W * X * W⁻¹) * n'⁻¹ := by rw [hW X]
  exact ⟨ψ, hψinj, hψrange, hψnat, hψtor⟩

theorem exists_sp3Frame (v : WeylGroup Tag.F4) {J : Set (Fin Tag.F4.rank)}
    (hJ : J = f4LeviB3 ∨ J = f4LeviC3) :
    ∃ ψ : ↥(StatedSp 3 L) →* ModGL Tag.F4 L, Function.Injective ψ ∧
      ψ.range = rootSpan Tag.F4 L ((fun α => v • α) '' parabolicRoots Tag.F4 J) ∧
      (∀ (σ : L ≃+* L) (X : ↥(StatedSp 3 L)),
        frobGL σ (ψ X) = ψ (statedSpMap (σ : L →+* L) 3 X)) ∧
      ∀ t ∈ torusGroup Tag.F4 L, ∃ W : ↥(StatedSp 3 L), ∀ X, t * ψ X * t⁻¹ = ψ (W * X * W⁻¹) := by
  rcases hJ with hJ | hJ
  · obtain ⟨ι₀, hinj, hrange, hnat, htor⟩ := exists_baseFrame_b3 (L := L) hJ
    exact exists_spFrame_conj v (fun α hα => hα.1) ι₀ hinj hrange hnat htor
  · obtain ⟨ι₀, hinj, hrange, hnat, htor⟩ := exists_baseFrame_c3 (L := L) hJ
    exact exists_spFrame_conj v (fun α hα => hα.1) ι₀ hinj hrange hnat htor

end CFSG.StandardType.RCKRP

end
