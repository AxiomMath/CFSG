module

public import CFSG.LocalAnalysis.StandardType.GGOrthKStructDefs
public import CFSG.LocalAnalysis.StandardType.GGSpJoinSignedPermGen

import CFSG.LocalAnalysis.StandardType.GGOrthKStructKer
import CFSG.LocalAnalysis.StandardType.GGOrthKStructNormalizerAux

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType.GGHalf CFSG.StandardType.SpJoin
  CFSG.LieType.Universal.SpecialLinear Matrix

theorem ggOrthKStruct_normalizer {n : ℕ} (hn : 7 ≤ n)
    (Φ : (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) ≃* ↥(halfTorus n)) (hΦ : IsTorusCoord n Φ)
    {s : SpecialLinearGroup (Fin (n + 1)) F2}
    (hs : s ∈ Subgroup.normalizer ((halfTorus n : Subgroup (SpecialLinearGroup (Fin (n + 1)) F2)) :
      Set (SpecialLinearGroup (Fin (n + 1)) F2))) :
    ∃ h ∈ spSignedGroup ((n + 1) / 2) 3, ∀ a : Fin ((n + 1) / 2) → Multiplicative (ZMod 3),
      s * (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * s⁻¹ =
        (Φ (h a) : SpecialLinearGroup (Fin (n + 1)) F2) := by
  classical
  have hconj : ∀ t ∈ (halfTorus n : Subgroup (SpecialLinearGroup (Fin (n + 1)) F2)),
      s * t * s⁻¹ ∈ halfTorus n := by
    intro t ht
    exact (Subgroup.mem_normalizer_iff.mp hs t).mp ht
  have hconj_inv : ∀ t ∈ (halfTorus n : Subgroup (SpecialLinearGroup (Fin (n + 1)) F2)),
      s⁻¹ * t * s ∈ halfTorus n := by
    intro t ht
    simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hs) t).mp ht
  let conjAut : MulAut (halfTorus n) :=
    { toFun := fun t =>
        (⟨s * (t : SpecialLinearGroup (Fin (n + 1)) F2) * s⁻¹, hconj t t.2⟩ :
          halfTorus n)
      invFun := fun t =>
        (⟨s⁻¹ * (t : SpecialLinearGroup (Fin (n + 1)) F2) * s, hconj_inv t t.2⟩ :
          halfTorus n)
      left_inv := fun t => Subtype.ext (by simp only [Subgroup.coe_mul]; group)
      right_inv := fun t => Subtype.ext (by simp only [Subgroup.coe_mul]; group)
      map_mul' := fun t u => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  let α : MulAut (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) :=
    Φ.trans (conjAut.trans Φ.symm)
  have hΦα (a : Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) :
      (Φ (α a) : SpecialLinearGroup (Fin (n + 1)) F2) = s * (Φ a) * s⁻¹ := by
    dsimp only [α, MulEquiv.trans_apply]
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hwt : ∀ a, okNorm_wt (α a) = okNorm_wt a := by
    intro a
    unfold okNorm_wt
    let S : Matrix (Fin (n + 1)) (Fin (n + 1)) F2 :=
      (s : Matrix (Fin (n + 1)) (Fin (n + 1)) F2)
    let S' : Matrix (Fin (n + 1)) (Fin (n + 1)) F2 :=
      ((s⁻¹ : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2)
    let tM : Matrix (Fin (n + 1)) (Fin (n + 1)) F2 :=
      ((Φ a : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2)
    let t'M : Matrix (Fin (n + 1)) (Fin (n + 1)) F2 :=
      ((Φ (α a) : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2)
    have hSS' : S * S' = 1 := by
      change ((s * s⁻¹ : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2) = 1
      simp
    have hS'S : S' * S = 1 := by
      change ((s⁻¹ * s : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2) = 1
      simp
    have ht' : t'M = S * tM * S' := by
      change (((Φ (α a) : SpecialLinearGroup (Fin (n + 1)) F2) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F2)) =
        (s : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) *
          ((Φ a : SpecialLinearGroup (Fin (n + 1)) F2) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) F2) *
          ((s⁻¹ : SpecialLinearGroup (Fin (n + 1)) F2) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) F2)
      rw [hΦα a]
      simp
    have hsq : (S * tM * S') * (S * tM * S') = S * tM ^ 2 * S' := by
      calc (S * tM * S') * (S * tM * S')
          = S * tM * (S' * S) * tM * S' := by noncomm_ring
        _ = S * tM * 1 * tM * S' := by rw [hS'S]
        _ = S * tM ^ 2 * S' := by noncomm_ring
    have hpoly : t'M ^ 2 + t'M + 1 = S * (tM ^ 2 + tM + 1) * S' := by
      rw [ht']
      rw [pow_two, hsq]
      conv_lhs => rw [← hSS']
      noncomm_ring
    have h1 : (Matrix.toLin' S).comp (Matrix.toLin' S') = LinearMap.id := by
      rw [← Matrix.toLin'_mul, hSS', Matrix.toLin'_one]
    have h2 : (Matrix.toLin' S').comp (Matrix.toLin' S) = LinearMap.id := by
      rw [← Matrix.toLin'_mul, hS'S, Matrix.toLin'_one]
    let e : (Fin (n + 1) → F2) ≃ₗ[F2] (Fin (n + 1) → F2) :=
      LinearEquiv.ofLinear (Matrix.toLin' S) (Matrix.toLin' S') h1 h2
    have hconj_toLin : Matrix.toLin' (t'M ^ 2 + t'M + 1) =
        e.conj (Matrix.toLin' (tM ^ 2 + tM + 1)) := by
      rw [hpoly, Matrix.toLin'_mul, Matrix.toLin'_mul, LinearEquiv.conj_apply,
        LinearEquiv.ofLinear_toLinearMap, LinearEquiv.ofLinear_symm_toLinearMap]
    have hfin : Module.finrank F2 (LinearMap.ker (Matrix.toLin'
        ((((Φ (α a) : SpecialLinearGroup (Fin (n + 1)) F2) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) F2)) ^ 2 +
          ((Φ (α a) : SpecialLinearGroup (Fin (n + 1)) F2) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) F2) + 1))) =
        Module.finrank F2 (LinearMap.ker (Matrix.toLin'
        ((((Φ a : SpecialLinearGroup (Fin (n + 1)) F2) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) F2)) ^ 2 +
          ((Φ a : SpecialLinearGroup (Fin (n + 1)) F2) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) F2) + 1))) := by
      change Module.finrank F2 (LinearMap.ker (Matrix.toLin' (t'M ^ 2 + t'M + 1))) =
        Module.finrank F2 (LinearMap.ker (Matrix.toLin' (tM ^ 2 + tM + 1)))
      rw [hconj_toLin]
      exact okNorm_finrank_ker_conj e (Matrix.toLin' (tM ^ 2 + tM + 1))
    have h1k := ggOrthKStruct_ker Φ hΦ (α a)
    have h2k := ggOrthKStruct_ker Φ hΦ a
    have heq : 2 * (Finset.univ.filter fun j => (α a) j ≠ 1).card =
        2 * (Finset.univ.filter fun j => a j ≠ 1).card :=
      h1k.symm.trans (hfin.trans h2k)
    omega
  exact ⟨MulEquiv.toEquiv α, okNorm_mem_spSignedGroup_of_weight α hwt,
    fun a => (hΦα a).symm⟩

end CFSG.StandardType

end
