module

public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Defs
public import CFSG.LocalAnalysis.WeakClosure81.W183Mem

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem w183_normalizer_le_normalizer_centralizer (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) :=
  Subgroup.le_normalizer_of_normal_subgroupOf (H := Subgroup.centralizer (X : Set G))
    (K := Subgroup.normalizer (X : Set G))
    (Subgroup.centralizer_le_normalizer (X : Set G))

private theorem w183_mem_sup_of_le_normalizer {A C : Subgroup G}
    (hAC : A ≤ Subgroup.normalizer (C : Set G)) {x : G} :
    x ∈ A ⊔ C ↔ ∃ a ∈ A, ∃ c ∈ C, a * c = x := by
  constructor
  · intro hx
    have hx' : x ∈ (A : Set G) * (C : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right A C hAC]
      exact hx
    exact Set.mem_mul.mp hx'
  · rintro ⟨a, ha, c, hc, rfl⟩
    show a * c ∈ (↑(A ⊔ C) : Set G)
    rw [Subgroup.coe_mul_of_left_le_normalizer_right A C hAC]
    exact Set.mem_mul.mpr ⟨a, ha, c, hc, rfl⟩

namespace Ctx188

variable {D : Data G} {V₀ V H : Subgroup G} {i j : ℕ}

theorem br1_weakClosure (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T))
    (hN : calNIn H D.T = {H ⊓ D.M}) :
    ∀ A ∈ packFamilyU D V H i M, A ≤ M.img D.T →
      (∀ B ∈ packGensU D V H i M, B ≤ Subgroup.normalizer (A : Set (LGL 2 M.W))) →
      ∀ X : Subgroup (LGL 2 M.W), X ≤ M.img H → M.img D.T ≤ X → X ≠ M.img H →
        X ≤ Subgroup.normalizer (A : Set (LGL 2 M.W)) := by
  intro A hA hAle hB X hXY hTX hXne
  obtain ⟨g₀, hg₀, hAeq⟩ := hA
  set Dg : Subgroup G := vInH V H g₀ with hDgdef
  have hAeqD : A = M.img Dg := hAeq.trans (congrArg M.img hDgdef.symm)
  have hAleD : M.img Dg ≤ M.img D.T := hAeqD ▸ hAle
  have hDgH : Dg ≤ H := by rw [hDgdef]; exact inf_le_right
  have hDgab : IsElemAbelian 2 Dg := by
    rw [hDgdef]
    exact (E3.isElemAbelian_conjSubgroup x.hyp.setting.isElemAbelian g₀).mono inf_le_left
  have hDgP : IsPGroup 2 Dg := CFSG.Open.IsElemAbelian.isPGroup hDgab
  set C : Subgroup G := H ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G) with hCdef
  have hCnormH : H ≤ Subgroup.normalizer (C : Set G) := by
    rw [hCdef]
    exact (le_inf H.le_normalizer
      ((Hyp183.normalizer_eOmegaZ H D.T).trans
        (w183_normalizer_le_normalizer_centralizer (eOmegaZ H D.T)))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hTC : D.T ≤ Subgroup.normalizer (C : Set G) := x.hyp.hyp171.2.1.trans hCnormH
  have hDgJ : Dg ≤ D.T ⊔ C := by
    intro d hd
    have hdH : d ∈ H := hDgH hd
    have hρd : M.ρ ⟨d, hdH⟩ ∈ M.img D.T :=
      hAleD (M.mem_img.2 ⟨⟨d, hdH⟩, hd, rfl⟩)
    obtain ⟨j, hjT, hjρ⟩ := M.mem_img.1 hρd
    have hρ1 : M.ρ (j⁻¹ * ⟨d, hdH⟩) = 1 := by
      rw [map_mul, map_inv, hjρ, inv_mul_cancel]
    have hmemC : (j : G)⁻¹ * d ∈ C := by
      rw [hCdef]
      refine ⟨H.mul_mem (H.inv_mem j.2) hdH, ?_⟩
      have h1 := (M.ρ_eq_one_iff (j⁻¹ * ⟨d, hdH⟩)).1 hρ1
      simpa using h1
    rw [← mul_inv_cancel_left (j : G) d]
    exact (D.T ⊔ C).mul_mem (Subgroup.mem_sup_left hjT) (Subgroup.mem_sup_right hmemC)
  have hSJ : IsSylowIn 2 D.T (D.T ⊔ C) :=
    isSylowIn_of_le_of_le x.hyp.isSylowIn_T le_sup_left
      (sup_le x.hyp.hyp171.2.1 inf_le_left)
  obtain ⟨y, hyJ, hDy⟩ := E3.exists_le_conj_of_isSylowIn hSJ hDgJ hDgP
  obtain ⟨t, htT, c, hcC, htc⟩ := (w183_mem_sup_of_le_normalizer hTC).mp hyJ
  rw [hCdef] at hcC
  have hcH : c ∈ H := hcC.1
  have hcCent : c ∈ Subgroup.centralizer (eOmegaZ H D.T : Set G) := hcC.2
  have hDg_le_c : Dg ≤ conjSubgroup D.T c := by
    have h1 : Dg ≤ conjSubgroup (conjSubgroup D.T t) c := by
      rw [conjSubgroup_conjSubgroup]
      rw [htc]
      exact hDy
    rwa [conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer htT)] at h1
  have hc₀le : conjSubgroup Dg c⁻¹ ≤ D.T :=
    (E3.conjSubgroup_le_iff_le_inv (A := Dg) (B := D.T) (h := c⁻¹)).mpr (by
      simpa using hDg_le_c)
  set g : G := g₀ * c⁻¹ with hgdef
  have hg : Gam183 V H (eOmegaZ H D.T) i g := by
    rw [hgdef]
    exact Gam183.conj (Hyp183.normalizer_eOmegaZ H D.T) (H.inv_mem hcH) hg₀
  have hgT : vInH V H g ≤ D.T := by
    rw [hgdef, vInH_mul g₀ (H.inv_mem hcH), ← hDgdef]
    exact hc₀le
  have hAeqg : M.img (vInH V H g) = A := by
    have h1 : M.img (vInH V H g) = M.img (conjSubgroup Dg c⁻¹) := by
      rw [hgdef, vInH_mul g₀ (H.inv_mem hcH), ← hDgdef]
    have h2 : M.img (conjSubgroup Dg c⁻¹) = A := by
      have hkey := M.img_conj (A := Dg) hDgH ⟨c, hcH⟩
      have hρc : M.ρ ⟨c, hcH⟩ = 1 := (M.ρ_eq_one_iff ⟨c, hcH⟩).2 hcCent
      rw [hρc, cj_one] at hkey
      rw [hAeqD]
      exact hkey.symm
    exact h1.trans h2
  set Nw : Subgroup (↥H) :=
    (Subgroup.normalizer (A : Set (LGL 2 M.W))).comap M.ρ with hNwdef
  have hB₀le : ∀ B₀ ∈ E3.gammaSet V i D.T, B₀ ≤ Nw.map H.subtype := by
    intro B₀ hB₀ b hbB₀
    have hbT : b ∈ D.T := (E3.mem_gammaSet_iff.mp hB₀).1 hbB₀
    have hbH : b ∈ H := x.hyp.hyp171.2.1 hbT
    by_cases hbot : M.img B₀ = ⊥
    · have hb1 : M.ρ ⟨b, hbH⟩ = 1 := by
        have hmem : M.ρ ⟨b, hbH⟩ ∈ M.img B₀ :=
          M.mem_img.2 ⟨⟨b, hbH⟩, hbB₀, rfl⟩
        rw [hbot] at hmem
        exact Subgroup.mem_bot.mp hmem
      refine Subgroup.mem_map.2 ⟨⟨b, hbH⟩, ?_, rfl⟩
      rw [hNwdef, Subgroup.mem_comap, hb1]
      exact Subgroup.one_mem _
    · have hBG : M.img B₀ ∈ packGensU D V H i M := ⟨hbot, B₀, hB₀, rfl⟩
      have hle := hB (M.img B₀) hBG
      refine Subgroup.mem_map.2 ⟨⟨b, hbH⟩, ?_, rfl⟩
      rw [hNwdef, Subgroup.mem_comap]
      exact hle (M.mem_img.2 ⟨⟨b, hbH⟩, hbB₀, rfl⟩)
  have hWclos : E3.wClos V i D.T ≤ Nw.map H.subtype :=
    E3.wClos_le_of_forall hB₀le
  have hW : ∀ (w : G) (hw : w ∈ H), w ∈ E3.wClos V i D.T →
      M.ρ ⟨w, hw⟩ ∈ Subgroup.normalizer
        ((M.img (vInH V H g) : Subgroup (LGL 2 M.W)) : Set (LGL 2 M.W)) := by
    intro w hw hwW
    have hmem := hWclos hwW
    rw [Subgroup.mem_map] at hmem
    obtain ⟨y, hy, hyw⟩ := hmem
    have hyw' : y = ⟨w, hw⟩ := Subtype.ext hyw
    rw [hyw', hNwdef, Subgroup.mem_comap] at hy
    simpa [hAeqg] using hy
  have hgM : g ∈ D.M := x.mem_M_of_wClos_normalizes M hg hgT hW
  have hconjV : conjSubgroup V g = V := by
    rw [conjSubgroup_eq_iff_mem_normalizer, x.hyp.setting.normalizer_eq]
    exact hgM
  have hVH : vInH V H g = V ⊓ H := by
    unfold vInH
    rw [hconjV]
  have hAeqV : A = M.img (V ⊓ H) := by
    rw [← hAeqg, hVH]
  set X₀ : Subgroup G := (X.comap M.ρ).map H.subtype with hX₀def
  have hTX₀ : D.T ≤ X₀ := by
    intro t htT
    have htH : t ∈ H := x.hyp.hyp171.2.1 htT
    refine Subgroup.mem_map.2 ⟨⟨t, htH⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    exact hTX (M.mem_img.2 ⟨⟨t, htH⟩, htT, rfl⟩)
  have hX₀H : X₀ ≤ H := Subgroup.map_subtype_le _
  have hX₀ne : X₀ ≠ H := by
    intro heq
    apply hXne
    apply le_antisymm hXY
    intro r hr
    obtain ⟨j, -, hjρ⟩ := M.mem_img.1 hr
    rw [← hjρ]
    have hjX₀ : (j : G) ∈ X₀ := by rw [heq]; exact j.2
    rw [hX₀def, Subgroup.mem_map] at hjX₀
    obtain ⟨y, hy, hyj⟩ := hjX₀
    have hyj' : y = j := Subtype.ext hyj
    rw [hyj', Subgroup.mem_comap] at hy
    exact hy
  have hX₀lt : X₀ < H := lt_of_le_of_ne hX₀H hX₀ne
  obtain ⟨Y, hY, hX₀Y⟩ := exists_mem_calNIn_of_lt hTX₀ hX₀lt
  rw [hN] at hY
  have hYeq : Y = H ⊓ D.M := Set.mem_singleton_iff.mp hY
  rw [hYeq] at hX₀Y
  have hX₀M : X₀ ≤ D.M := hX₀Y.trans inf_le_right
  intro z hz
  obtain ⟨j, -, hjz⟩ := M.mem_img.1 (hXY hz)
  rw [← hjz]
  have hjX : M.ρ j ∈ X := by rw [hjz]; exact hz
  have hjX₀ : (j : G) ∈ X₀ := by
    rw [hX₀def]
    exact Subgroup.mem_map.2 ⟨j, by rwa [Subgroup.mem_comap], rfl⟩
  have hjM : (j : G) ∈ conjSubgroup D.M 1 := by
    rw [conjSubgroup_one]
    exact hX₀M hjX₀
  have hres := x.hyp.img_normalizer_of_mem_conj M j.2 hjM
  have hthis : M.img (vInH V H 1) = A := by
    rw [vInH, conjSubgroup_one, ← hAeqV]
  have hres' : M.ρ j ∈ Subgroup.normalizer (A : Set (LGL 2 M.W)) := by
    have hje : (⟨(j : G), j.2⟩ : ↥H) = j := Subtype.ext rfl
    rw [hje] at hres
    simpa [hthis] using hres
  exact hres'

end Ctx188

end CFSG.LocalAnalysis.WeakClosure81

end
