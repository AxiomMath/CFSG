module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL28Model
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL28Rank
import CFSG.GroupTheory.E3Params

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped MatrixGroups

theorem finL28_two_pow_mQuot_eq_card_range {W : Type} [CommGroup W] [Finite W] {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (θ : W ≃* Multiplicative V) (g : MulAut W)
    (T : V →ₗ[ZMod 2] V)
    (hT : ∀ w : W, θ (g w) = Multiplicative.ofAdd (T (Multiplicative.toAdd (θ w)))) :
    2 ^ E3.mQuot ⊤ (fixV (Subgroup.zpowers g)) = Nat.card (LinearMap.range (T - 1)) := by
  have hexp : ∀ w : W, w ^ 2 = 1 := by
    intro w
    apply θ.injective
    rw [map_pow, map_one, pow_two]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_one]
    rw [← two_nsmul, ← Nat.cast_smul_eq_nsmul (R := ZMod 2)]
    rw [ZMod.natCast_self 2, zero_smul]
  rw [CFSG.GroupTheory.mQuot_top_eq_rkIdx, rkIdx_fixV_zpowers g, commV_zpowers_eq_map g,
    ← MonoidHom.range_eq_map, ← card_eq_two_pow hexp ((commHom g).range)]
  let e : W ≃ V := θ.toEquiv.trans Multiplicative.toAdd
  have hT' : ∀ u : W, Multiplicative.toAdd (θ (g u)) = T (Multiplicative.toAdd (θ u)) := by
    intro u
    rw [hT u, toAdd_ofAdd]
  have hmap : ∀ u : W, e (commHom g u) = T (e u) - e u := by
    intro u
    calc e (commHom g u)
        = Multiplicative.toAdd (θ (g u * u⁻¹)) := by rw [commHom_apply]; rfl
      _ = Multiplicative.toAdd (θ (g u) * (θ u)⁻¹) := by rw [map_mul, map_inv]
      _ = Multiplicative.toAdd (θ (g u)) + Multiplicative.toAdd ((θ u)⁻¹) := by
            rw [toAdd_mul]
      _ = Multiplicative.toAdd (θ (g u)) - Multiplicative.toAdd (θ u) := by
            rw [toAdd_inv, sub_eq_add_neg]
      _ = T (Multiplicative.toAdd (θ u)) - Multiplicative.toAdd (θ u) := by rw [hT' u]
      _ = T (e u) - e u := rfl
  have hmem : ∀ w : W, w ∈ (commHom g).range ↔ e w ∈ LinearMap.range (T - 1) := by
    intro w
    constructor
    · rintro ⟨u, rfl⟩
      refine LinearMap.mem_range.mpr ⟨e u, ?_⟩
      exact (hmap u).symm
    · rintro ⟨x, hx⟩
      refine MonoidHom.mem_range.mpr ⟨e.symm x, ?_⟩
      apply e.injective
      rw [hmap (e.symm x), e.apply_symm_apply]
      exact hx
  exact Nat.card_congr (Equiv.subtypeEquiv e hmem)

theorem finL28Steinberg_holds : FinL28Steinberg := by
  intro W _ _ hW Y L g hctx hgY hg2 hL hcard
  have hq : CFSG.IsQuasisimple ↥L := hctx.2.2.2.2.1
  have hirr : IsIrrOn L ⊤ ⊥ := hctx.2.2.2.2.2
  have hgL : g ∈ L := finL28_involution_mem hctx hL hgY hg2
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := finL28_exists_sl2_equiv hq hL
  obtain ⟨V, _, _, _, ρ, θ, hρ, hV, hnt, hθ⟩ := finL28_exists_irreducible_rep hW hirr hcard e
  have hgg : g * g = 1 := by
    have h1 := pow_orderOf_eq_one g
    rwa [hg2, pow_two] at h1
  let h : SL(2, F) := e.symm ⟨g, hgL⟩
  have heh : e h = ⟨g, hgL⟩ := e.apply_symm_apply _
  have hge : ((e h : ↥L) : MulAut W) = g := by rw [heh]
  have hh2 : h * h = 1 := by
    apply e.injective
    rw [map_mul, map_one, heh]
    exact Subtype.ext hgg
  have hh1 : h ≠ 1 := by
    intro h1
    rw [h1, map_one] at heh
    have hg1 : g = 1 := congrArg Subtype.val heh.symm
    rw [hg1, orderOf_one] at hg2
    omega
  have hrange := finL28_two_pow_four_le_card_range hF hV ρ hρ hnt hh2 hh1
  have heq := finL28_two_pow_mQuot_eq_card_range θ g (ρ h) (fun w => by
    rw [← hge]
    exact hθ h w)
  rw [← heq] at hrange
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hrange

end CFSG.LocalAnalysis.WeakClosure81
