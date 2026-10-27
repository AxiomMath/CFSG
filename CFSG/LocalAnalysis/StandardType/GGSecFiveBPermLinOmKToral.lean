module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLinOmKTorus
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoHypSix
public import CFSG.LieType.Universal.Catalog
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpKToral
import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerMinus
import CFSG.LocalAnalysis.StandardType.GGSpinInnerAction

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Open CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted


theorem ggSecFiveBPermLinOmK_exists_toral (hMp : GGInnerDiagMpInput) {G : Type} [Group G]
    [Finite G] {p r f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f) (hr : 2 ≤ r)
    {B Bs K : Subgroup G} (hBs : GGBstar p B Bs) (hmark : GGInnerDiagOn Bs K)
    (e : ↥K ≃* spinGroup (quadMinus (r + 2) (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2))
    (hcard : p ^ (r + 1) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) ≤ Nat.card ↥Bs)
    {ω : (GaloisField 2 f)ˣ} (hω : ω ^ p = 1) (hωo : orderOf ω = p) :
    ∃ κ : spinGroup (quadMinus (r + 2) (GaloisField 2 f) (minusCoeffs 2 f).1
        (minusCoeffs 2 f).2) →* G, Function.Injective κ ∧ κ.range = K ∧
      ∀ b ∈ Bs, ∃ t : Fin (r + 1) → Multiplicative (ZMod p), ∀ s,
        b * κ s * b⁻¹ = κ (spinMinusSplitTorus hr (minusCoeffs_irr 2 f) hω t * s *
          (spinMinusSplitTorus hr (minusCoeffs_irr 2 f) hω t)⁻¹) := by
  classical
  let κ₀ : spinGroup (quadMinus (r + 2) (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2) →* G := K.subtype.comp e.symm.toMonoidHom
  have hκ₀inj : Function.Injective κ₀ := K.subtype_injective.comp e.symm.injective
  have hκ₀range : κ₀.range = K := by
    show (K.subtype.comp e.symm.toMonoidHom).range = K
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.symm.surjective, Subgroup.map_top,
      Subgroup.range_subtype]
  have hZ : Subgroup.center ↥K = ⊥ := by
    have hZsp : Subgroup.center (spinGroup (quadMinus (r + 2) (GaloisField 2 f)
        (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) = ⊥ :=
      PsiDiag.SpinM.center_eq_bot (K := GaloisField 2 f) (n := r + 2)
        (b := (minusCoeffs 2 f).1) (c := (minusCoeffs 2 f).2) (minusCoeffs_irr 2 f) (by omega)
    refine (Subgroup.map_eq_bot_iff_of_injective (H := Subgroup.center ↥K)
      (f := e.toMonoidHom) e.injective).mp ?_
    have hmap : (Subgroup.center ↥K).map e.toMonoidHom =
        Subgroup.center (spinGroup (quadMinus (r + 2) (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) := by
      simpa using Subgroup.map_center_eq e
    rw [hmap, hZsp]
  have hinner : ∀ b ∈ Bs, ∃ g ∈ K, ∀ k ∈ K, b * k * b⁻¹ = g * k * g⁻¹ :=
    ggSpinMinusInnerAction_of_mp hMp (by omega) hf hmark κ₀ hκ₀inj hκ₀range
  obtain ⟨-, κ, hκinj, hκrange, htoral⟩ :=
    ggSecFiveBPermSpK_exists_toral_of_inner hBs hκ₀inj hκ₀range hZ hinner hcard
      (D := spinMinusSplitTorus hr (minusCoeffs_irr 2 f) hω)
      (hconj := fun E hE h =>
        spinMinusSplitTorus_exists_mulAut hp2 hr (minusCoeffs_irr 2 f) hω hωo E hE h)
  exact ⟨κ, hκinj, hκrange, htoral⟩

end CFSG.StandardType

end
