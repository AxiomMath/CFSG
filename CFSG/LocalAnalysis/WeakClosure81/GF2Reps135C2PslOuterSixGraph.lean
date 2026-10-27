module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslOuterSixRank
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslOuterSixModule
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslOuterSixEq

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix
open CFSG.LieType.SpecialLinear
open CFSG.LieType.SpecialLinear.ExteriorModel

private lemma c2slout6g_eq_one_of_ne_zero {K : Type*} [Field K] [Fintype K]
    (hK : Fintype.card K = 2) {x : K} (hx : x ≠ 0) : x = 1 := by
  classical
  have hcard : Fintype.card Kˣ = 1 := by
    rw [Fintype.card_units, hK]
  haveI hsub : Subsingleton Kˣ :=
    Fintype.card_le_one_iff_subsingleton.mp (by simp [hcard])
  have h := congrArg (fun u : Kˣ => (u : K))
    (Subsingleton.elim (Units.mk0 x hx) 1)
  simpa using h

private lemma c2slout6g_diag_eq_one {K : Type} [Field K] [Fintype K]
    (hK : Fintype.card K = 2) (B : Matrix.GeneralLinearGroup (Fin 6) K)
    (hB : IsUpperGL B) : ∀ i : Fin 6, (B : Matrix (Fin 6) (Fin 6) K) i i = 1 := by
  have htri : (B : Matrix (Fin 6) (Fin 6) K).IsUpperTriangular := hB
  have hdet : (B : Matrix (Fin 6) (Fin 6) K).det =
      ∏ i : Fin 6, (B : Matrix (Fin 6) (Fin 6) K) i i :=
    Matrix.det_of_isUpperTriangular htri
  have hunit : IsUnit ((B : Matrix (Fin 6) (Fin 6) K).det) := Matrix.isUnits_det_units B
  have hne : (∏ i : Fin 6, (B : Matrix (Fin 6) (Fin 6) K) i i) ≠ 0 := by
    rw [← hdet]
    exact hunit.ne_zero
  intro i
  exact c2slout6g_eq_one_of_ne_zero hK
    ((Finset.prod_ne_zero_iff.mp hne) i (Finset.mem_univ i))

theorem w135c2_graph_six_twenty {K : Type} [Field K] [Fintype K] [CharP K 2]
    (hK : Fintype.card K = 2) {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 6) K) W)
    (hirr : ρ.IsIrreducible) (hne : ∃ x, ρ x ≠ 1) (hcard : Nat.card W = 2 ^ 20)
    {d : W ≃ₗ[ZMod 2] W} {B : Matrix.GeneralLinearGroup (Fin 6) K} (hB : IsUpperGL B)
    {τ : K ≃+* K}
    (hd : ∀ (x : Matrix.SpecialLinearGroup (Fin 6) K) (w : W),
      d (ρ x w) = ρ (borelStd 6 K B τ 1 x) (d w)) :
    4 ≤ Module.finrank (ZMod 2) (LinearMap.range ((d : W →ₗ[ZMod 2] W) - 1)) := by
  obtain ⟨β, hβ⟩ := w135c2_six_three_module hK ρ hirr hne hcard
  have hB0 : ∀ i j : Fin 6, j < i → (B : Matrix (Fin 6) (Fin 6) K) i j = 0 :=
    fun i j hij => hB i j hij
  have hB1 : ∀ i : Fin 6, (B : Matrix (Fin 6) (Fin 6) K) i i = 1 :=
    c2slout6g_diag_eq_one hK B hB
  let T : (Set.powersetCard (Fin 6) 3 → K) →ₗ[K] (Set.powersetCard (Fin 6) 3 → K) :=
    Matrix.mulVecLin (minor (B : Matrix (Fin 6) (Fin 6) K) :
        Matrix (Set.powersetCard (Fin 6) 3) (Set.powersetCard (Fin 6) 3) K) ∘ₗ
      (revMap (R := K) (n := 3) (m := 6) (by norm_num)).toLinearMap - LinearMap.id
  have hrank : 6 ≤ Module.finrank K (LinearMap.range T) :=
    w135c2_six_three_rank hK (B : Matrix (Fin 6) (Fin 6) K) hB0 hB1
  have hgraph : ∀ w : W, β (d w) =
      Matrix.mulVecLin (minor (B : Matrix (Fin 6) (Fin 6) K) :
          Matrix (Set.powersetCard (Fin 6) 3) (Set.powersetCard (Fin 6) 3) K)
        (revMap (R := K) (n := 3) (m := 6) (by norm_num) (β w)) :=
    fun w => w135c2_six_three_graph_eq hK ρ hirr hne β hβ (d := d) (B := B) (τ := τ) hd w
  have hβd : ∀ w : W, β (((d : W →ₗ[ZMod 2] W) - 1) w) = T (β w) := by
    intro w
    have h1 : ((d : W →ₗ[ZMod 2] W) - 1) w = d w - w := by
      simp
    rw [h1, AddEquiv.map_sub, hgraph w]
    rfl
  haveI hfinW : Finite (LinearMap.range ((d : W →ₗ[ZMod 2] W) - 1)) :=
    Finite.of_injective Subtype.val Subtype.coe_injective
  haveI hfinK : Finite (LinearMap.range T) :=
    Finite.of_injective Subtype.val Subtype.coe_injective
  haveI hmodW : Module.Finite (ZMod 2) (LinearMap.range ((d : W →ₗ[ZMod 2] W) - 1)) :=
    Module.Finite.of_finite
  haveI hmodK : Module.Finite K (LinearMap.range T) := Module.Finite.of_finite
  have hiff : ∀ a : W, (a ∈ LinearMap.range ((d : W →ₗ[ZMod 2] W) - 1)) ↔
      (β.toEquiv a ∈ LinearMap.range T) := by
    intro a
    rw [LinearMap.mem_range, LinearMap.mem_range]
    constructor
    · rintro ⟨w, hw⟩
      refine ⟨β w, ?_⟩
      rw [← hβd w, hw]
      rfl
    · rintro ⟨z, hz⟩
      refine ⟨β.symm z, ?_⟩
      apply β.injective
      rw [hβd (β.symm z), AddEquiv.apply_symm_apply]
      simpa using hz
  have hcard_range : Nat.card (LinearMap.range ((d : W →ₗ[ZMod 2] W) - 1)) =
      Nat.card (LinearMap.range T) :=
    Nat.card_congr (Equiv.subtypeEquiv β.toEquiv hiff)
  have hcard1 : Nat.card (LinearMap.range ((d : W →ₗ[ZMod 2] W) - 1)) =
      2 ^ Module.finrank (ZMod 2) (LinearMap.range ((d : W →ₗ[ZMod 2] W) - 1)) :=
    (Module.natCard_eq_pow_finrank (K := ZMod 2) (V :=
        LinearMap.range ((d : W →ₗ[ZMod 2] W) - 1))).trans (by simp [Nat.card_zmod])
  have hcard2 : Nat.card (LinearMap.range T) =
      2 ^ Module.finrank K (LinearMap.range T) :=
    (Module.natCard_eq_pow_finrank (K := K) (V := LinearMap.range T)).trans
      (by simp [Nat.card_eq_fintype_card, hK])
  have hfin : Module.finrank (ZMod 2) (LinearMap.range ((d : W →ₗ[ZMod 2] W) - 1)) =
      Module.finrank K (LinearMap.range T) := by
    have hpow : 2 ^ Module.finrank (ZMod 2) (LinearMap.range ((d : W →ₗ[ZMod 2] W) - 1)) =
        2 ^ Module.finrank K (LinearMap.range T) :=
      hcard1.symm.trans (hcard_range.trans hcard2)
    exact Nat.pow_right_injective (le_refl 2) hpow
  rw [hfin]
  exact le_trans (by norm_num : 4 ≤ 6) hrank

end CFSG.LocalAnalysis.WeakClosure81
