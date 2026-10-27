module

public import CFSG.LocalAnalysis.WeakClosure81.W172Local
public import CFSG.LocalAnalysis.WeakClosure81.W172ModD

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace MinCex172

variable {D : Data G} {V₀ V H : Subgroup G}

private theorem w172_d3_commutator_mul {e₁ a z : G} (hz : z * e₁ = e₁ * z) :
    ⁅e₁, a * z⁆ = ⁅e₁, a⁆ := by
  have hz' : z * e₁⁻¹ = e₁⁻¹ * z := by
    have h := congrArg (fun y => e₁⁻¹ * y * e₁⁻¹) hz
    simp only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right] at h
    simpa [mul_assoc] using h.symm
  calc ⁅e₁, a * z⁆ = e₁ * a * (z * e₁⁻¹) * z⁻¹ * a⁻¹ := by
        rw [commutatorElement_def]; group
    _ = e₁ * a * (e₁⁻¹ * z) * z⁻¹ * a⁻¹ := by rw [hz']
    _ = ⁅e₁, a⁆ := by rw [commutatorElement_def]; group

theorem w172_mem_conj_of_img_normalizer (h162 : W3Thm162Gt2 G) (c : MinCex172 D V₀ V H) {g : G}
    (hg : Gam183 V H (eOmegaZ H D.T) 1 g)
    (hm : E3.mQuot (vInH V H g)
      (vInH V H g ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G)) ≤ 1)
    (M : ModDataE H (eOmegaZ H D.T)) {h : G} (hh : h ∈ H)
    (hn : M.ρ ⟨h, hh⟩ ∈ Subgroup.normalizer
      ((M.img (vInH V H g) : Subgroup (LGL 2 M.W)) : Set (LGL 2 M.W))) :
    h ∈ conjSubgroup D.M g := by
  classical
  have hAH : vInH V H g ≤ H := inf_le_right
  have hcomm : ⁅eOmegaZ H D.T, vInH V H g⁆ ≤ eOmegaZ H D.T ⊓ conjSubgroup V₀ g :=
    w172_comm_le_of_mQuot_le_one h162 c hg hm
  have hne : ⁅eOmegaZ H D.T, vInH V H g⁆ ≠ ⊥ := by
    intro hbot
    exact hg.2 (Subgroup.le_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot))
  have hEnorm : ∀ e ∈ eOmegaZ H D.T, h * e * h⁻¹ ∈ eOmegaZ H D.T := fun e he =>
    (Subgroup.mem_normalizer_iff.mp (Hyp183.normalizer_eOmegaZ H D.T hh) e).mp he
  have hle : ⁅eOmegaZ H D.T, vInH V H g⁆ ≤
      conjSubgroup (eOmegaZ H D.T ⊓ conjSubgroup V₀ g) h := by
    refine Subgroup.commutator_le.mpr fun e he a ha => ?_
    rw [mem_conjSubgroup_iff]
    have haH : a ∈ H := hAH ha
    have hrA : M.ρ ⟨a, haH⟩ ∈ M.img (vInH V H g) := M.mem_img.2 ⟨⟨a, haH⟩, ha, rfl⟩
    have hconj : M.ρ ⟨h, hh⟩ * M.ρ ⟨a, haH⟩ * (M.ρ ⟨h, hh⟩)⁻¹ ∈ M.img (vInH V H g) :=
      (Subgroup.mem_normalizer_iff.mp hn (M.ρ ⟨a, haH⟩)).mp hrA
    obtain ⟨a', ha'A, ha'ρ⟩ := M.mem_img.1 hconj
    have hy : M.ρ (⟨h, hh⟩ * ⟨a, haH⟩ * ⟨h, hh⟩⁻¹) = M.ρ a' := by
      rw [map_mul, map_mul, map_inv, ha'ρ]
    have hz1 : M.ρ (a'⁻¹ * (⟨h, hh⟩ * ⟨a, haH⟩ * ⟨h, hh⟩⁻¹)) = 1 := by
      rw [map_mul, map_inv, hy, inv_mul_cancel]
    have hzC : (a' : G)⁻¹ * (h * a * h⁻¹) ∈ Subgroup.centralizer (eOmegaZ H D.T : Set G) := by
      have := (M.ρ_eq_one_iff _).1 hz1
      simpa using this
    set z : G := (a' : G)⁻¹ * (h * a * h⁻¹) with hzdef
    have hhah : h * a * h⁻¹ = (a' : G) * z := by rw [hzdef]; group
    have he₁ : h * e * h⁻¹ ∈ eOmegaZ H D.T := hEnorm e he
    have hzcomm : z * (h * e * h⁻¹) = (h * e * h⁻¹) * z :=
      (Subgroup.mem_centralizer_iff.mp hzC (h * e * h⁻¹) he₁).symm
    have hcommconj : h * ⁅e, a⁆ * h⁻¹ = ⁅h * e * h⁻¹, (a' : G)⁆ := by
      calc h * ⁅e, a⁆ * h⁻¹ = ⁅h * e * h⁻¹, h * a * h⁻¹⁆ := by
            rw [commutatorElement_def, commutatorElement_def]; group
        _ = ⁅h * e * h⁻¹, (a' : G) * z⁆ := by rw [hhah]
        _ = ⁅h * e * h⁻¹, (a' : G)⁆ := w172_d3_commutator_mul hzcomm
    rw [hcommconj]
    exact hcomm (Subgroup.commutator_mem_commutator he₁ ha'A)
  have hleInter : ⁅eOmegaZ H D.T, vInH V H g⁆ ≤ (eOmegaZ H D.T ⊓ conjSubgroup V₀ g) ⊓
      conjSubgroup (eOmegaZ H D.T ⊓ conjSubgroup V₀ g) h := le_inf hcomm hle
  have hneInter : (eOmegaZ H D.T ⊓ conjSubgroup V₀ g) ⊓
      conjSubgroup (eOmegaZ H D.T ⊓ conjSubgroup V₀ g) h ≠ ⊥ := by
    intro hbot
    exact hne (le_bot_iff.mp (hleInter.trans (le_of_eq hbot)))
  exact w172_mem_conj_of_inf_ne_bot c hh hneInter

theorem w172_img_normalizer_of_mem_conj (c : MinCex172 D V₀ V H) {g : G}
    (M : ModDataE H (eOmegaZ H D.T)) {h : G} (hh : h ∈ H) (hM : h ∈ conjSubgroup D.M g) :
    M.ρ ⟨h, hh⟩ ∈ Subgroup.normalizer
      ((M.img (vInH V H g) : Subgroup (LGL 2 M.W)) : Set (LGL 2 M.W)) := by
  have hMn : Subgroup.normalizer (conjSubgroup V g : Set G) = conjSubgroup D.M g := by
    rw [← E3.conjSubgroup_normalizer, c.hyp.setting.normalizer_eq]
  have hconjV : conjSubgroup (conjSubgroup V g) h⁻¹ = conjSubgroup V g := by
    rw [conjSubgroup_eq_iff_mem_normalizer, hMn]
    exact (conjSubgroup D.M g).inv_mem hM
  have hconjH : conjSubgroup H h⁻¹ = H :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (H.le_normalizer (H.inv_mem hh))
  have hconjA : conjSubgroup (vInH V H g) h⁻¹ = vInH V H g := by
    unfold vInH
    rw [E3.conjSubgroup_inf, hconjV, hconjH]
  have hcj : cj (M.ρ ⟨h, hh⟩) (M.img (vInH V H g)) = M.img (vInH V H g) := by
    rw [M.img_conj (A := vInH V H g) inf_le_right ⟨h, hh⟩]
    exact congrArg M.img hconjA
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hcj

theorem w172_mem_conj_iff_comm (h162 : W3Thm162Gt2 G) (c : MinCex172 D V₀ V H) {g : G}
    (hg : Gam183 V H (eOmegaZ H D.T) 1 g)
    (hm : E3.mQuot (vInH V H g)
      (vInH V H g ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G)) ≤ 1)
    (M : ModDataE H (eOmegaZ H D.T)) {e : LGL 2 M.W}
    (hge : M.img (vInH V H g) = Subgroup.zpowers e) (he : e * e = 1) (he1 : e ≠ 1) {h : G}
    (hh : h ∈ H) :
    h ∈ conjSubgroup D.M g ↔ M.ρ ⟨h, hh⟩ * e = e * M.ρ ⟨h, hh⟩ := by
  rw [← w172_mem_normalizer_zpowers_iff he he1, ← hge]
  exact ⟨w172_img_normalizer_of_mem_conj c M hh,
    w172_mem_conj_of_img_normalizer h162 c hg hm M hh⟩

end MinCex172

end CFSG.LocalAnalysis.WeakClosure81

end
