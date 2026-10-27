module

public import CFSG.LocalAnalysis.WeakClosure81.SpUFixFactDefs
public import CFSG.LocalAnalysis.WeakClosure81.SpUFixFactURoot
import CFSG.LocalAnalysis.WeakClosure81.SpUFixFactUPerp
import CFSG.LocalAnalysis.WeakClosure81.SpUFixFactURootEq
import CFSG.LocalAnalysis.WeakClosure81.SpUFixFactUAut
import CFSG.LocalAnalysis.WeakClosure81.SpUFixFactCore

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

noncomputable def spUFixGeomU (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ} (hm : 4 ≤ m)
    {e : Fin m → F} (he0 : e ≠ 0) (he : herm (unitaryInvolution F 2 n) e e = 0) :
    SpUFixGeom (StatedProj (StatedSU m (2 ^ n) F)) (spUFixRootU hF m e) F (Fin m → F) where
  τ := unitaryInvolution F 2 n
  β := herm (unitaryInvolution F 2 n)
  β_add_left := herm_add_left _
  β_smul_left := herm_smul_left _
  β_add_right := herm_add_right _
  β_smul_right := herm_smul_right _
  X := spUFixRootU hF m
  X_smul _ _ hc hv := spUFixRootU_smul hF hc hv
  X_inj _ _ hv hw hvv hww h := exists_smul_of_spUFixRootU_eq hF hv hw hvv hww h
  X_invol _ hv _ hx := mul_self_of_mem_spUFixRootU hF hv hx
  X_comm _ _ hv hw hvw _ hx _ hy := commute_of_mem_spUFixRootU hF hv hw hvw hx hy
  X_order_three _ _ _ _ hv hw hvw := exists_mul_pow_three_spUFixRootU hF hv hw hvw
  conj x := exists_linearMap_map_conj_spUFixRootU hF x
  a := e
  a_ne := he0
  a_iso := he
  R_eq := rfl
  trans _ hv0 hv := exists_spUFixRootU_eq_map hF (by omega) he0 hv0 he hv
  second := spUFix_exists_herm_eq_zero_not_smul hF hm he0 he
  aut α hα2 _ hout := spUFix_exists_semilinear_statedProjSU hF hm α hα2 hout

theorem spUFixConclusion_statedProjSU (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ} (hm : 4 ≤ m)
    (R : Subgroup (StatedProj (StatedSU m (2 ^ n) F))) (hR : Nat.card R = 2 ^ n)
    (hRt : ∀ x ∈ R, x ≠ 1 → IsUnitaryTransvectionIn m n x)
    {Sy : Subgroup (StatedProj (StatedSU m (2 ^ n) F))}
    (hSy : ∃ P : Sylow 2 (StatedProj (StatedSU m (2 ^ n) F)),
      (P : Subgroup (StatedProj (StatedSU m (2 ^ n) F))) = Sy) (hRSy : R ≤ Sy)
    (hSyR : Sy ≤ Subgroup.normalizer (R : Set (StatedProj (StatedSU m (2 ^ n) F)))) :
    SpUFixConclusion (StatedProj (StatedSU m (2 ^ n) F)) R Sy := by
  obtain ⟨e, he0, he, rfl⟩ := exists_eq_spUFixRootU hF hm R hR hRt
  exact (spUFixGeomU hF hm he0 he).spUFixConclusion hSy hRSy hSyR

end CFSG.LocalAnalysis.WeakClosure81

end
