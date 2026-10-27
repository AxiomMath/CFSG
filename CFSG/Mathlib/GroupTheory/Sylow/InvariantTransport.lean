module


public import CFSG.GroupTheory.ConjKerCenter
public import CFSG.HardMathSupport.Lang.Triality.SylowInnerExt

public section

namespace CFSG.SylowAction

open Subgroup

open scoped Pointwise

theorem exists_simultaneous_conjugation
    {p : ℕ} [Fact p.Prime]
    {F : Type*} [Group F] [Finite F]
    (hcenter : IsPGroup p (Subgroup.center F))
    (T : Sylow p (MulAut F))
    (B : Subgroup (MulAut F)) (hB : IsPGroup p B)
    (P : Sylow p F)
    (hBP : ∀ β : MulAut F, β ∈ B →
      (P : Subgroup F).map β.toMonoidHom = (P : Subgroup F)) :
    ∃ α : MulAut F,
      (P : Subgroup F).map α.toMonoidHom =
        (T : Subgroup (MulAut F)).comap (MulAut.conj : F →* MulAut F) ∧
      B.map (MulAut.conj α).toMonoidHom ≤ (T : Subgroup (MulAut F)) := by
  classical
  let j : F →* MulAut F := MulAut.conj
  let H : Subgroup (MulAut F) := B ⊔ (P : Subgroup F).map j
  have hconj : ∀ (ψ : MulAut F) (x : F), ψ * j x * ψ⁻¹ = j (ψ x) :=
    fun ψ x => CFSG.HardMathSupport.Lang.Triality.mulAut_mul_conj_mul_inv ψ x
  have hnorm : B ≤ Subgroup.normalizer ((P : Subgroup F).map j) := by
    intro β hβ
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hcomp : ((MulAut.conj β).toMonoidHom.comp j) = j.comp β.toMonoidHom := by
      ext x y
      exact congrArg (fun e : MulAut F => e y) (hconj β x)
    calc ((P : Subgroup F).map j).map (MulAut.conj β).toMonoidHom
        = (P : Subgroup F).map ((MulAut.conj β).toMonoidHom.comp j) := by
          rw [Subgroup.map_map]
      _ = (P : Subgroup F).map (j.comp β.toMonoidHom) := by rw [hcomp]
      _ = ((P : Subgroup F).map β.toMonoidHom).map j := by rw [Subgroup.map_map]
      _ = (P : Subgroup F).map j := by rw [hBP β hβ]
  have hHp : IsPGroup p ↥H := by
    dsimp only [H]
    exact hB.to_sup_of_normal_right' (P.isPGroup'.map j) hnorm
  obtain ⟨Q, hHQ⟩ := hHp.exists_le_sylow
  obtain ⟨γ, hγ⟩ := MulAction.exists_smul_eq (MulAut F) Q T
  have hcoeQ : (MulAut.conj γ) • (Q : Subgroup (MulAut F)) =
      (T : Subgroup (MulAut F)) := by
    rw [← Sylow.coe_subgroup_smul, hγ]
  have hBT : B.map (MulAut.conj γ).toMonoidHom ≤ (T : Subgroup (MulAut F)) := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hx
    have hbQ : b ∈ (Q : Subgroup (MulAut F)) := hHQ (Subgroup.mem_sup_left hb)
    have hmem := Subgroup.smul_mem_pointwise_smul b (MulAut.conj γ)
      (Q : Subgroup (MulAut F)) hbQ
    rw [hcoeQ] at hmem
    simpa only [MulAut.smul_def, MulEquiv.coe_toMonoidHom] using hmem
  have hjP : ((P : Subgroup F).map j).map (MulAut.conj γ).toMonoidHom ≤
      (T : Subgroup (MulAut F)) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hy
    have hqQ : j q ∈ (Q : Subgroup (MulAut F)) :=
      hHQ (Subgroup.mem_sup_right (Subgroup.mem_map_of_mem j hq))
    have hmem := Subgroup.smul_mem_pointwise_smul (j q) (MulAut.conj γ)
      (Q : Subgroup (MulAut F)) hqQ
    rw [hcoeQ] at hmem
    simpa only [MulAut.smul_def, MulEquiv.coe_toMonoidHom] using hmem
  have hmapj : ((P : Subgroup F).map γ.toMonoidHom).map j ≤
      (T : Subgroup (MulAut F)) := by
    have hcomp : j.comp γ.toMonoidHom = (MulAut.conj γ).toMonoidHom.comp j := by
      ext x y
      exact (congrArg (fun e : MulAut F => e y) (hconj γ x)).symm
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map]
    exact hjP
  have hcomap : IsPGroup p ↥((T : Subgroup (MulAut F)).comap j) := by
    apply T.isPGroup'.comap_of_ker_isPGroup j
    rw [show j = (MulAut.conj : F →* MulAut F) from rfl,
      CFSG.GroupTheory.ker_conj_eq_center]
    exact hcenter
  let Pγ : Sylow p F := Sylow.mapSurjective (p := p) (f := γ.toMonoidHom) γ.surjective P
  have hPγ : (Pγ : Subgroup F) = (P : Subgroup F).map γ.toMonoidHom :=
    Sylow.coe_mapSurjective γ.surjective P
  have hle : (Pγ : Subgroup F) ≤ (T : Subgroup (MulAut F)).comap j :=
    Subgroup.map_le_iff_le_comap.mp (by rw [hPγ]; exact hmapj)
  have hpre : (T : Subgroup (MulAut F)).comap j = (Pγ : Subgroup F) :=
    Pγ.is_maximal' hcomap hle
  exact ⟨γ, by rw [hpre, hPγ], hBT⟩

end CFSG.SylowAction
