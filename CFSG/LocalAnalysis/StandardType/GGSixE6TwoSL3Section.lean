module

public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveF4
public import Certificates.Certificate3007
public import Certificates.Certificate10005
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Basic
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoSL3Nat
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoSL3Cover
public import CFSG.Certificates.CosetTableShort
public import CFSG.LieType.Multipliers.ProductKernel

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.StandardType.GGHalf Matrix

section Section

private theorem irreducible_comp_surjective {X G : Type} [Group X] [Group G] {W : Type}
    [AddCommGroup W] [Module (ZMod 2) W] (σ : Representation (ZMod 2) X W) (π : G →* X)
    (hπ : Function.Surjective π) (hirr : σ.IsIrreducible) :
    Representation.IsIrreducible (σ.comp π) := by
  rw [CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff] at hirr ⊢
  exact ⟨hirr.1, fun U hU => hirr.2 U fun x v hv => by
    obtain ⟨g, rfl⟩ := hπ x
    exact hU g v hv⟩

private theorem exists_apply_ne_one_comp {X G : Type} [Group X] [Group G] {W : Type}
    [AddCommGroup W] [Module (ZMod 2) W] (σ : Representation (ZMod 2) X W) (π : G →* X)
    (hπ : Function.Surjective π) (hnt : ∃ x, σ x ≠ 1) :
    ∃ g, (σ.comp π) g ≠ 1 := by
  obtain ⟨x, hx⟩ := hnt
  obtain ⟨g, rfl⟩ := hπ x
  exact ⟨g, hx⟩

theorem sl3_section_natural {X : Type} [Group X] [Finite X] (hperf : commutator X = ⊤)
    (hodd : ∀ z ∈ Subgroup.center X, ∀ k : ℕ, z ^ 2 ^ k = 1 → z = 1)
    (hP : LieModel (X ⧸ Subgroup.center X) .PSL 3 2 2)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (σ : Representation (ZMod 2) X W) (hirr : σ.IsIrreducible) (hnt : ∃ x, σ x ≠ 1)
    (hdim : Module.finrank (ZMod 2) W ≤ 6) :
    ∃ (θ : Matrix.SpecialLinearGroup (Fin 3) F4 ≃* X) (E : W ≃+ (Fin 3 → F4)), ∀ g w,
      E (σ (θ g) w) =
        ((g : Matrix.SpecialLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) *ᵥ E w := by
  rcases sl3_or_psl_of_quotient hperf hodd hP with h | h
  · obtain ⟨e⟩ := h
    let θ₀ : Matrix.SpecialLinearGroup (Fin 3) F4 ≃* X := e.symm
    let ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 3) F4) W :=
      σ.comp θ₀.toMonoidHom
    have hρirr : ρ.IsIrreducible := irreducible_comp_surjective σ θ₀.toMonoidHom θ₀.surjective hirr
    have hρnt : ∃ x, ρ x ≠ 1 := exists_apply_ne_one_comp σ θ₀.toMonoidHom θ₀.surjective hnt
    obtain ⟨ψ, E, hE⟩ := sl3_natural_form ρ hρirr hρnt hdim
    refine ⟨ψ.symm.trans θ₀, E, fun g w => ?_⟩
    have h := hE (ψ.symm g) w
    simpa [ρ, θ₀, MulEquiv.trans_apply, MulEquiv.apply_symm_apply] using h
  · obtain ⟨e⟩ := h
    exfalso
    let π : Matrix.SpecialLinearGroup (Fin 3) F4 →* X :=
      e.symm.toMonoidHom.comp
        (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F4)))
    let ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 3) F4) W := σ.comp π
    have hπsurj : Function.Surjective π :=
      e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
    have hρirr : ρ.IsIrreducible := irreducible_comp_surjective σ π hπsurj hirr
    have hρnt : ∃ x, ρ x ≠ 1 := exists_apply_ne_one_comp σ π hπsurj hnt
    have hπ1 : π scalarOmega = 1 := by
      dsimp only [π, MonoidHom.comp_apply]
      rw [QuotientGroup.mk'_apply,
        (QuotientGroup.eq_one_iff _).mpr scalarOmega_mem_center, map_one]
    have hρ1 : ρ scalarOmega = 1 := by
      dsimp only [ρ, MonoidHom.comp_apply]
      rw [hπ1, map_one]
    exact sl3_scalarOmega_ne_one ρ hρirr hρnt hdim hρ1

end Section

end CFSG.StandardType.GGSixE6Two
