module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDModelDefs

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.PhanDn.QTwo CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits
open CFSG.ClassicalGroups.Unitary

section WinExt

variable {F K : Type} [Field F] [Field K] [Algebra F K] (m : ℕ) (hm : 3 ≤ m)

@[expose] noncomputable def pmw_extFun (φ : Module.End F (Fin 3 → K)) (v : Fin (m + 1) → K) :
    Fin (m + 1) → K :=
  fun i =>
    if h : m - 2 ≤ i.val then
      φ (fun t => v ⟨m - 2 + t.val, by omega⟩) ⟨i.val - (m - 2), by omega⟩
    else v i

private theorem pmw_extFun_apply_of_le (φ : Module.End F (Fin 3 → K))
    (v : Fin (m + 1) → K) (i : Fin (m + 1)) (h : m - 2 ≤ i.val) :
    pmw_extFun (F := F) m hm φ v i =
      φ (fun t => v ⟨m - 2 + t.val, by omega⟩) ⟨i.val - (m - 2), by omega⟩ := by
  unfold pmw_extFun
  rw [dif_pos h]

private theorem pmw_extFun_apply_of_lt (φ : Module.End F (Fin 3 → K))
    (v : Fin (m + 1) → K) (i : Fin (m + 1)) (hi : i.val < m - 2) :
    pmw_extFun (F := F) m hm φ v i = v i := by
  unfold pmw_extFun
  rw [dif_neg (by omega : ¬ m - 2 ≤ i.val)]

private theorem pmw_extFun_apply_window (φ : Module.End F (Fin 3 → K))
    (v : Fin (m + 1) → K) (t : Fin 3) :
    pmw_extFun (F := F) m hm φ v ⟨m - 2 + t.val, by omega⟩ =
      φ (fun s => v ⟨m - 2 + s.val, by omega⟩) t := by
  rw [pmw_extFun_apply_of_le (F := F) m hm φ v ⟨m - 2 + t.val, by omega⟩
    (by simp only [Fin.val_mk]; omega)]
  have hidx : (⟨(⟨m - 2 + t.val, by omega⟩ : Fin (m + 1)).val - (m - 2),
      by omega⟩ : Fin 3) = t :=
    Fin.ext (by simp only [Fin.val_mk]; omega)
  rw [hidx]

theorem pmw_extFun_map_add (φ : Module.End F (Fin 3 → K))
    (v w : Fin (m + 1) → K) :
    pmw_extFun (F := F) m hm φ (v + w) =
      pmw_extFun (F := F) m hm φ v + pmw_extFun (F := F) m hm φ w := by
  funext i
  rw [Pi.add_apply]
  by_cases h : m - 2 ≤ i.val
  · unfold pmw_extFun
    rw [dif_pos h, dif_pos h, dif_pos h]
    have hfun : (fun t : Fin 3 => (v + w) ⟨m - 2 + t.val, by omega⟩) =
        (fun t : Fin 3 => v ⟨m - 2 + t.val, by omega⟩) +
          (fun t : Fin 3 => w ⟨m - 2 + t.val, by omega⟩) := by
      funext t; rfl
    rw [hfun, map_add, Pi.add_apply]
  · unfold pmw_extFun
    rw [dif_neg h, dif_neg h, dif_neg h, Pi.add_apply]

theorem pmw_extFun_map_smul (c : F) (φ : Module.End F (Fin 3 → K))
    (v : Fin (m + 1) → K) :
    pmw_extFun (F := F) m hm φ (c • v) = c • pmw_extFun (F := F) m hm φ v := by
  funext i
  rw [Pi.smul_apply]
  by_cases h : m - 2 ≤ i.val
  · unfold pmw_extFun
    rw [dif_pos h, dif_pos h]
    have hfun : (fun t : Fin 3 => (c • v) ⟨m - 2 + t.val, by omega⟩) =
        c • (fun t : Fin 3 => v ⟨m - 2 + t.val, by omega⟩) := by
      funext t; rfl
    rw [hfun, map_smul, Pi.smul_apply]
  · unfold pmw_extFun
    rw [dif_neg h, dif_neg h, Pi.smul_apply]

@[expose] noncomputable def pmw_ext (φ : Module.End F (Fin 3 → K)) :
    Module.End F (Fin (m + 1) → K) where
  toFun := pmw_extFun (F := F) m hm φ
  map_add' := pmw_extFun_map_add (F := F) m hm φ
  map_smul' := fun c v => pmw_extFun_map_smul (F := F) m hm c φ v

theorem pmw_ext_map_one :
    pmw_ext (F := F) m hm (1 : Module.End F (Fin 3 → K)) = 1 := by
  apply LinearMap.ext; intro v; funext i
  change pmw_extFun (F := F) m hm (1 : Module.End F (Fin 3 → K)) v i = v i
  by_cases h : m - 2 ≤ i.val
  · rw [pmw_extFun_apply_of_le (F := F) m hm _ v i h, Module.End.one_apply]
    exact congrArg v (Fin.ext (by simp only [Fin.val_mk]; omega))
  · rw [pmw_extFun_apply_of_lt (F := F) m hm _ v i (not_le.1 h)]

theorem pmw_ext_map_mul (φ ψ : Module.End F (Fin 3 → K)) :
    pmw_ext (F := F) m hm (φ * ψ) =
      pmw_ext (F := F) m hm φ * pmw_ext (F := F) m hm ψ := by
  apply LinearMap.ext; intro v; funext i
  change pmw_extFun (F := F) m hm (φ * ψ) v i =
    pmw_extFun (F := F) m hm φ (pmw_extFun (F := F) m hm ψ v) i
  by_cases h : m - 2 ≤ i.val
  · rw [pmw_extFun_apply_of_le (F := F) m hm (φ * ψ) v i h,
        pmw_extFun_apply_of_le (F := F) m hm φ (pmw_extFun (F := F) m hm ψ v) i h,
        Module.End.mul_apply]
    refine congrArg (fun x => φ x ⟨i.val - (m - 2), by omega⟩) ?_
    funext t
    rw [pmw_extFun_apply_window (F := F) m hm ψ v t]
  · rw [pmw_extFun_apply_of_lt (F := F) m hm (φ * ψ) v i (not_le.1 h),
        pmw_extFun_apply_of_lt (F := F) m hm φ (pmw_extFun (F := F) m hm ψ v) i
          (not_le.1 h),
        pmw_extFun_apply_of_lt (F := F) m hm ψ v i (not_le.1 h)]

@[expose] noncomputable def winExt :
    Module.End F (Fin 3 → K) →* Module.End F (Fin (m + 1) → K) where
  toFun φ := pmw_ext (F := F) m hm φ
  map_one' := pmw_ext_map_one (F := F) m hm
  map_mul' := pmw_ext_map_mul (F := F) m hm

private theorem pmw_winExt_apply_of_le (φ : Module.End F (Fin 3 → K))
    (v : Fin (m + 1) → K) (i : Fin (m + 1)) (h : m - 2 ≤ i.val) :
    winExt m hm φ v i =
      φ (fun t => v ⟨m - 2 + t.val, by omega⟩) ⟨i.val - (m - 2), by omega⟩ :=
  pmw_extFun_apply_of_le (F := F) m hm φ v i h

private theorem pmw_winExt_apply_of_lt (φ : Module.End F (Fin 3 → K))
    (v : Fin (m + 1) → K) (i : Fin (m + 1)) (hi : i.val < m - 2) :
    winExt m hm φ v i = v i :=
  pmw_extFun_apply_of_lt (F := F) m hm φ v i hi

theorem winExt_apply_window (φ : Module.End F (Fin 3 → K)) (v : Fin (m + 1) → K) (t : Fin 3) :
    winExt m hm φ v ⟨m - 2 + t.val, by omega⟩ = φ (fun s => v ⟨m - 2 + s.val, by omega⟩) t :=
  pmw_extFun_apply_window (F := F) m hm φ v t

theorem winExt_apply_of_lt (φ : Module.End F (Fin 3 → K)) (v : Fin (m + 1) → K)
    (i : Fin (m + 1)) (hi : i.val < m - 2) : winExt m hm φ v i = v i :=
  pmw_extFun_apply_of_lt (F := F) m hm φ v i hi

end WinExt

section Identify

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2] (m : ℕ)
  (hm : 3 ≤ m)

theorem winExt_suEndN (h : Su K 2 1 3) :
    winExt m hm (suEndN (F := F) (unitaryInvolution K 2 1) 3 h).toLinearMap =
      (qtwoStdWin (F := F) (K := K) m (m - 2) 3 (by omega) h).toLinearMap := by
  apply LinearMap.ext; intro v; funext i
  have hblk : (m - 2) + 3 ≤ m + 1 := by omega
  by_cases hle : m - 2 ≤ i.val
  · rw [pmw_winExt_apply_of_le (F := F) m hm _ v i hle]
    rw [show (suEndN (F := F) (unitaryInvolution K 2 1) 3 h).toLinearMap =
        suEndNLinear (F := F) (unitaryInvolution K 2 1) 3 h from rfl,
      suEndNLinear_apply, smul_def]
    conv_rhs => rw [show i = blockIdx (m - 2) hblk ⟨i.val - (m - 2), by omega⟩ from
      Fin.ext (by simp only [blockIdx_val]; omega)]
    unfold qtwoStdWin
    rw [MonoidHom.comp_apply,
      show (suEndN (F := F) (unitaryInvolution K 2 1) (m + 1)
          (blockEmb K 2 1 (m + 1) 3 (m - 2) hblk h)).toLinearMap =
        suEndNLinear (F := F) (unitaryInvolution K 2 1) (m + 1)
          (blockEmb K 2 1 (m + 1) 3 (m - 2) hblk h) from rfl,
      suEndNLinear_apply, smul_def, coe_coe_blockEmb, blockMat_mulVec_blockIdx]
    rfl
  · rw [pmw_winExt_apply_of_lt (F := F) m hm _ v i (not_le.1 hle)]
    unfold qtwoStdWin
    rw [MonoidHom.comp_apply,
      show (suEndN (F := F) (unitaryInvolution K 2 1) (m + 1)
          (blockEmb K 2 1 (m + 1) 3 (m - 2) hblk h)).toLinearMap =
        suEndNLinear (F := F) (unitaryInvolution K 2 1) (m + 1)
          (blockEmb K 2 1 (m + 1) 3 (m - 2) hblk h) from rfl,
      suEndNLinear_apply, smul_def, coe_coe_blockEmb,
      blockMat_mulVec_of_not_mem _ _ (by omega)]

theorem winExt_tauAt (E : QuadExt F K (unitaryInvolution K 2 1)) :
    winExt m hm (tauAt E (2 : Fin 3)).toLinearMap = (stdTau E m).toLinearMap := by
  apply LinearMap.ext; intro v; funext i
  by_cases hle : m - 2 ≤ i.val
  · rw [pmw_winExt_apply_of_le (F := F) m hm _ v i hle]
    change tauAt E (2 : Fin 3) (fun t => v ⟨m - 2 + t.val, by omega⟩)
        ⟨i.val - (m - 2), by omega⟩ = tauAt E (Fin.last m) v i
    rw [tauAt_apply, tauAt_apply]
    have hval : v ⟨m - 2 + (⟨i.val - (m - 2), by omega⟩ : Fin 3).val, by omega⟩ = v i :=
      congrArg v (Fin.ext (by simp only [Fin.val_mk]; omega))
    rw [hval]
    have hcond : ((⟨i.val - (m - 2), by omega⟩ : Fin 3) = 2) ↔ i = Fin.last m := by
      rw [Fin.ext_iff, Fin.ext_iff]
      simp only [Fin.val_mk, Fin.val_last]
      have h2 : (2 : Fin 3).val = 2 := by decide
      rw [h2]
      omega
    by_cases hi : i = Fin.last m
    · rw [if_pos (hcond.mpr hi), if_pos hi]
    · rw [if_neg (fun hc => hi (hcond.mp hc)), if_neg hi]
  · rw [pmw_winExt_apply_of_lt (F := F) m hm _ v i (not_le.1 hle)]
    change v i = tauAt E (Fin.last m) v i
    rw [tauAt_apply, if_neg (by
      intro hi
      have hi' := congrArg Fin.val hi
      simp only [Fin.val_last] at hi'
      omega)]

end Identify

end CFSG.StandardType.QTwo

end
