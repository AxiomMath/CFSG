module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDModelA3
public import CFSG.LocalAnalysis.StandardType.GGQTwoDModelKlein
public import CFSG.LocalAnalysis.StandardType.GGQTwoDModelWinExt

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.PhanDn.QTwo CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits

section Fork

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2]

theorem exists_linearEquivHom_of_end {V : Type} [AddCommGroup V] [Module F V] {H : Type}
    [Group H] (Φ : H →* Module.End F V) :
    ∃ θ : H →* (V ≃ₗ[F] V), ∀ g v, θ g v = Φ g v := by
  refine ⟨(LinearMap.GeneralLinearGroup.generalLinearEquiv F V).toMonoidHom.comp
    Φ.toHomUnits, ?_⟩
  intro g v
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv, MonoidHom.coe_toHomUnits]

private theorem pmf_kleinPsi_blockEmb_one_eq (E : QuadExt F K (unitaryInvolution K 2 1))
    (h : Su K 2 1 3) :
    kleinPsiHom E (blockEmb K 2 1 4 3 1 (by norm_num) h) =
      (suEndN (F := F) (unitaryInvolution K 2 1) 3 h).toLinearMap := by
  apply LinearMap.ext
  intro x
  simp only [LinearEquiv.coe_toLinearMap, suEndN_apply,
    CFSG.ClassicalGroups.Unitary.smul_def]
  exact kleinPsiHom_blockEmb_one E h x

private theorem pmf_kleinPsi_blockEmb_zero_eq (E : QuadExt F K (unitaryInvolution K 2 1))
    (h : Su K 2 1 3) :
    kleinPsiHom E (blockEmb K 2 1 4 3 0 (by norm_num) h) =
      (tauAt E (2 : Fin 3)).toLinearMap *
        (suEndN (F := F) (unitaryInvolution K 2 1) 3 (revSU3 K 2 1 h)).toLinearMap *
        (tauAt E (2 : Fin 3)).toLinearMap := by
  apply LinearMap.ext
  intro x
  rw [Module.End.mul_apply, Module.End.mul_apply]
  simp only [LinearEquiv.coe_toLinearMap, suEndN_apply,
    CFSG.ClassicalGroups.Unitary.smul_def]
  exact kleinPsiHom_blockEmb_zero E h x

theorem qtwoStd_forkHom_exists (E : QuadExt F K (unitaryInvolution K 2 1)) (m : ℕ)
    (hm : 3 ≤ m) :
    ∃ θ : Su K 2 1 4 →* ((Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)),
      (∀ h : Su K 2 1 3, θ (blockEmb K 2 1 4 3 1 (by norm_num) h) =
          qtwoStdWin (F := F) (K := K) m (m - 2) 3 (by omega) h) ∧
      (∀ h : Su K 2 1 3, θ (blockEmb K 2 1 4 3 0 (by norm_num) h) =
          stdConj E m
            (qtwoStdWin (F := F) (K := K) m (m - 2) 3 (by omega) (revSU3 K 2 1 h))) := by
  obtain ⟨θ, hθ⟩ := exists_linearEquivHom_of_end ((winExt m hm).comp (kleinPsiHom E))
  refine ⟨θ, ?_, ?_⟩
  · intro h
    apply LinearEquiv.ext
    intro v
    rw [hθ, MonoidHom.comp_apply, pmf_kleinPsi_blockEmb_one_eq E h]
    rw [winExt_suEndN m hm h]
    rfl
  · intro h
    apply LinearEquiv.ext
    intro v
    rw [hθ, MonoidHom.comp_apply, pmf_kleinPsi_blockEmb_zero_eq E h]
    rw [map_mul, map_mul]
    rw [winExt_tauAt m hm E, winExt_suEndN m hm (revSU3 K 2 1 h)]
    have hτ : (stdTau E m)⁻¹ = stdTau E m := by
      rw [stdTau]
      exact inv_eq_of_mul_eq_one_right (tauAt_mul_self E (Fin.last m))
    unfold stdConj
    rw [MulAut.conj_apply, hτ]
    rw [← LinearEquiv.coe_toLinearMap (e := stdTau E m * qtwoStdWin (F := F) (K := K) m
      (m - 2) 3 (by omega) (revSU3 K 2 1 h) * stdTau E m)]
    rw [LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_mul]

theorem qtwoStd_A3_fork (E : QuadExt F K (unitaryInvolution K 2 1)) (hK : Nat.card K = 4)
    (m : ℕ) (hm : 3 ≤ m) (i j k : Fin (m + 1)) (hi : i.val = m - 1) (hj : j.val = m - 2)
    (hk : k.val = m) :
    ∃ θ : Su K 2 1 4 →* ((Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)),
      θ.range = qtwoStdW E m hm i j ⊔ qtwoStdW E m hm j k := by
  obtain ⟨θ, h1, h0⟩ := qtwoStd_forkHom_exists E m hm
  refine ⟨θ, ?_⟩
  have hcomp1 : θ.comp (blockEmb K 2 1 4 3 1 (by norm_num)) =
      qtwoStdWin (F := F) (K := K) m (m - 2) 3 (by omega) := by
    apply MonoidHom.ext
    intro h
    exact h1 h
  have hcomp0 : θ.comp (blockEmb K 2 1 4 3 0 (by norm_num)) =
      (stdConj E m).toMonoidHom.comp
        ((qtwoStdWin (F := F) (K := K) m (m - 2) 3 (by omega)).comp
          (revSU3 K 2 1).toMonoidHom) := by
    apply MonoidHom.ext
    intro h
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact h0 h
  have hcomp0range : (θ.comp (blockEmb K 2 1 4 3 0 (by norm_num))).range =
      (qtwoStdWin (F := F) (K := K) m (m - 2) 3 (by omega)).range.map
        (stdConj E m).toMonoidHom := by
    rw [hcomp0, MonoidHom.range_comp, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr (revSU3 K 2 1).surjective, Subgroup.map_top]
  have hmain : θ.range =
      (qtwoStdWin (F := F) (K := K) m (m - 2) 3 (by omega)).range ⊔
        (qtwoStdWin (F := F) (K := K) m (m - 2) 3 (by omega)).range.map
          (stdConj E m).toMonoidHom := by
    rw [MonoidHom.range_eq_map θ, ← blockEmb_three_sup_eq_top hK, Subgroup.map_sup,
      ← MonoidHom.range_comp θ (blockEmb K 2 1 4 3 0 (by norm_num)),
      ← MonoidHom.range_comp θ (blockEmb K 2 1 4 3 1 (by norm_num)),
      hcomp0range, hcomp1, sup_comm]
  have hWij : qtwoStdW E m hm i j =
      (qtwoStdWin (F := F) (K := K) m (m - 2) 3 (by omega)).range := by
    rw [qtwoStdW_symm E m hm i j,
      qtwoStdW_chain (F := F) (K := K) E m hm (m - 2) (by omega) j i hj (by omega)]
  have hWjk : qtwoStdW E m hm j k =
      (qtwoStdWin (F := F) (K := K) m (m - 2) 3 (by omega)).range.map
        (stdConj E m).toMonoidHom :=
    qtwoStdW_fork (F := F) (K := K) E m hm j k hj hk
  rw [hWij, hWjk]
  exact hmain

end Fork

end CFSG.StandardType.QTwo

end
