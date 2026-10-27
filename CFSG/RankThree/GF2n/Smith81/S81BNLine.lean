module

public import CFSG.RankThree.GF2n.Smith81.S81BA5Rank
public import CFSG.RankThree.GF2n.Smith81.S81BNCore

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

open Matrix exteriorPower CFSG.Open CFSG.RankThree.GF2n.Smith81.EGeom

variable {K : Type} [Field K]

theorem plucker_1 (v : Fin 3 → Fin 6 → K) :
    minor3 v 0 2 4 * minor3 v 0 1 3 - minor3 v 0 1 4 * minor3 v 0 2 3
      - minor3 v 0 3 4 * minor3 v 0 1 2 = 0 := by
  simp [minor3, Matrix.det_fin_three]
  ring

theorem plucker_2 (v : Fin 3 → Fin 6 → K) :
    minor3 v 0 1 2 * minor3 v 3 4 5 + minor3 v 0 2 3 * minor3 v 1 4 5
      - minor3 v 0 2 4 * minor3 v 1 3 5 + minor3 v 0 2 5 * minor3 v 1 3 4 = 0 := by
  simp [minor3, Matrix.det_fin_three]
  ring

theorem gam_p0_pure {g : Cube K ≃ₗ[K] Cube K} (hg : g ∈ Gam K) :
    ∃ v : Fin 3 → Fin 6 → K, g (p0 K) = ιMulti K 3 v := by
  obtain ⟨A, _, rfl⟩ := Subgroup.mem_map.mp hg
  rw [rhoEquiv_apply, p0_eq]
  exact ⟨_, rho_ιMulti K A _⟩

private theorem coord_cb_self (I : Set.powersetCard (Fin 6) 3) :
    coord K (cubeBasis K I) I = 1 := by
  simp [coord_cubeBasis]

private theorem coord_cb_ne {I J : Set.powersetCard (Fin 6) 3} (h : I.val ≠ J.val) :
    coord K (cubeBasis K I) J = 0 := by
  have h' : I ≠ J := fun e => h (congrArg Subtype.val e)
  simp [coord_cubeBasis, h']

theorem not_pure_special {a b c : K} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (v : Fin 3 → Fin 6 → K) :
    a • p0 K + b • cubeBasis K S013 ≠ c • ιMulti K 3 v := by
  intro h
  have hJ : ∀ J : Set.powersetCard (Fin 6) 3,
      a * coord K (cubeBasis K S024) J + b * coord K (cubeBasis K S013) J =
        c * coord K (ιMulti K 3 v) J := by
    intro J
    have h' := congrArg (fun ξ => coord K ξ J) h
    simpa only [coord_add, coord_smul, p0] using h'
  have f1 : a = c * minor3 v 0 2 4 := by
    have h1 := hJ S024
    have a1 : coord K (cubeBasis K S013) S024 = 0 := coord_cb_ne (by decide)
    have a2 : coord K (ιMulti K 3 v) S024 = minor3 v 0 2 4 :=
      coord_ιMulti_sorted v (by decide) (by decide)
    rw [coord_cb_self S024, a1, a2] at h1
    linear_combination h1
  have f2 : b = c * minor3 v 0 1 3 := by
    have h2 := hJ S013
    have a1 : coord K (cubeBasis K S024) S013 = 0 := coord_cb_ne (by decide)
    have a2 : coord K (ιMulti K 3 v) S013 = minor3 v 0 1 3 :=
      coord_ιMulti_sorted v (by decide) (by decide)
    rw [coord_cb_self S013, a1, a2] at h2
    linear_combination h2
  have g14 : minor3 v 0 1 4 = 0 := by
    have h3 := hJ (tripleSet 0 1 4 (by decide) (by decide) (by decide))
    have a1 : coord K (cubeBasis K S024)
        (tripleSet 0 1 4 (by decide) (by decide) (by decide)) = 0 :=
      coord_cb_ne (by decide)
    have a2 : coord K (cubeBasis K S013)
        (tripleSet 0 1 4 (by decide) (by decide) (by decide)) = 0 :=
      coord_cb_ne (by decide)
    have a3 : coord K (ιMulti K 3 v) (tripleSet 0 1 4 (by decide) (by decide) (by decide)) =
        minor3 v 0 1 4 := coord_ιMulti_sorted v (by decide) (by decide)
    rw [a1, a2, a3] at h3
    have h3' : c * minor3 v 0 1 4 = 0 := by linear_combination -h3
    exact (mul_eq_zero.mp h3').resolve_left hc
  have g34 : minor3 v 0 3 4 = 0 := by
    have h4 := hJ S034
    have a1 : coord K (cubeBasis K S024) S034 = 0 := coord_cb_ne (by decide)
    have a2 : coord K (cubeBasis K S013) S034 = 0 := coord_cb_ne (by decide)
    have a3 : coord K (ιMulti K 3 v) S034 = minor3 v 0 3 4 :=
      coord_ιMulti_sorted v (by decide) (by decide)
    rw [a1, a2, a3] at h4
    have h4' : c * minor3 v 0 3 4 = 0 := by linear_combination -h4
    exact (mul_eq_zero.mp h4').resolve_left hc
  have hP := plucker_1 v
  have hab : a * b = 0 := by
    linear_combination b * f1 + (c * minor3 v 0 2 4) * f2 + c ^ 2 * hP
      + (c ^ 2 * minor3 v 0 2 3) * g14 + (c ^ 2 * minor3 v 0 1 2) * g34
  exact mul_ne_zero ha hb hab

theorem not_pure_opposite {a b c : K} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (v : Fin 3 → Fin 6 → K) :
    a • p0 K + b • cubeBasis K S135 ≠ c • ιMulti K 3 v := by
  intro h
  have hJ : ∀ J : Set.powersetCard (Fin 6) 3,
      a * coord K (cubeBasis K S024) J + b * coord K (cubeBasis K S135) J =
        c * coord K (ιMulti K 3 v) J := by
    intro J
    have h' := congrArg (fun ξ => coord K ξ J) h
    simpa only [coord_add, coord_smul, p0] using h'
  have f1 : a = c * minor3 v 0 2 4 := by
    have h1 := hJ S024
    have a1 : coord K (cubeBasis K S135) S024 = 0 := coord_cb_ne (by decide)
    have a2 : coord K (ιMulti K 3 v) S024 = minor3 v 0 2 4 :=
      coord_ιMulti_sorted v (by decide) (by decide)
    rw [coord_cb_self S024, a1, a2] at h1
    linear_combination h1
  have f2 : b = c * minor3 v 1 3 5 := by
    have h2 := hJ S135
    have a1 : coord K (cubeBasis K S024) S135 = 0 := coord_cb_ne (by decide)
    have a2 : coord K (ιMulti K 3 v) S135 = minor3 v 1 3 5 :=
      coord_ιMulti_sorted v (by decide) (by decide)
    rw [coord_cb_self S135, a1, a2] at h2
    linear_combination h2
  have g012 : minor3 v 0 1 2 = 0 := by
    have h3 := hJ (tripleSet 0 1 2 (by decide) (by decide) (by decide))
    have a1 : coord K (cubeBasis K S024)
        (tripleSet 0 1 2 (by decide) (by decide) (by decide)) = 0 :=
      coord_cb_ne (by decide)
    have a2 : coord K (cubeBasis K S135)
        (tripleSet 0 1 2 (by decide) (by decide) (by decide)) = 0 :=
      coord_cb_ne (by decide)
    have a3 : coord K (ιMulti K 3 v) (tripleSet 0 1 2 (by decide) (by decide) (by decide)) =
        minor3 v 0 1 2 := coord_ιMulti_sorted v (by decide) (by decide)
    rw [a1, a2, a3] at h3
    have h3' : c * minor3 v 0 1 2 = 0 := by linear_combination -h3
    exact (mul_eq_zero.mp h3').resolve_left hc
  have g023 : minor3 v 0 2 3 = 0 := by
    have h4 := hJ (tripleSet 0 2 3 (by decide) (by decide) (by decide))
    have a1 : coord K (cubeBasis K S024)
        (tripleSet 0 2 3 (by decide) (by decide) (by decide)) = 0 :=
      coord_cb_ne (by decide)
    have a2 : coord K (cubeBasis K S135)
        (tripleSet 0 2 3 (by decide) (by decide) (by decide)) = 0 :=
      coord_cb_ne (by decide)
    have a3 : coord K (ιMulti K 3 v) (tripleSet 0 2 3 (by decide) (by decide) (by decide)) =
        minor3 v 0 2 3 := coord_ιMulti_sorted v (by decide) (by decide)
    rw [a1, a2, a3] at h4
    have h4' : c * minor3 v 0 2 3 = 0 := by linear_combination -h4
    exact (mul_eq_zero.mp h4').resolve_left hc
  have g134 : minor3 v 1 3 4 = 0 := by
    have h5 := hJ (tripleSet 1 3 4 (by decide) (by decide) (by decide))
    have a1 : coord K (cubeBasis K S024)
        (tripleSet 1 3 4 (by decide) (by decide) (by decide)) = 0 :=
      coord_cb_ne (by decide)
    have a2 : coord K (cubeBasis K S135)
        (tripleSet 1 3 4 (by decide) (by decide) (by decide)) = 0 :=
      coord_cb_ne (by decide)
    have a3 : coord K (ιMulti K 3 v) (tripleSet 1 3 4 (by decide) (by decide) (by decide)) =
        minor3 v 1 3 4 := coord_ιMulti_sorted v (by decide) (by decide)
    rw [a1, a2, a3] at h5
    have h5' : c * minor3 v 1 3 4 = 0 := by linear_combination -h5
    exact (mul_eq_zero.mp h5').resolve_left hc
  have hP := plucker_2 v
  have hab : a * b = 0 := by
    linear_combination b * f1 + (c * minor3 v 0 2 4) * f2 - c ^ 2 * hP
      + (c ^ 2 * minor3 v 3 4 5) * g012 + (c ^ 2 * minor3 v 1 4 5) * g023
      + (c ^ 2 * minor3 v 0 2 5) * g134
  exact mul_ne_zero ha hb hab

theorem exists_gam_S013 : ∃ g ∈ Gam K, g (p0 K) = cubeBasis K S013 := by
  have hli : LinearIndependent K ![e K 0, e K 1, e K 3] :=
    linearIndependent_of_ιMulti_ne_zero
      (by rw [← cubeBasis_S013]; exact (cubeBasis K).ne_zero S013)
  obtain ⟨g, hg, hgp⟩ := exists_gam_p0_eq_iota ![e K 0, e K 1, e K 3] hli
  exact ⟨g, hg, hgp.trans cubeBasis_S013.symm⟩

theorem exists_gam_S135 : ∃ g ∈ Gam K, g (p0 K) = cubeBasis K S135 := by
  have hli : LinearIndependent K ![e K 1, e K 3, e K 5] :=
    linearIndependent_of_ιMulti_ne_zero
      (by rw [← cubeBasis_S135]; exact (cubeBasis K).ne_zero S135)
  obtain ⟨g, hg, hgp⟩ := exists_gam_p0_eq_iota ![e K 1, e K 3, e K 5] hli
  exact ⟨g, hg, hgp.trans cubeBasis_S135.symm⟩

private theorem a5l_p0_mem_W0 : p0 K ∈ Wsp (Submodule.span K {p0 K}) (U0 K) := by
  rw [mem_Wsp]
  intro u hu
  rw [U0_fix u hu, sub_self]
  exact Submodule.zero_mem _

private theorem a5l_span_le :
    Submodule.span K {p0 K} ≤ Wsp (Submodule.span K {p0 K}) (U0 K) :=
  Submodule.span_le.mpr (Set.singleton_subset_iff.mpr a5l_p0_mem_W0)

private theorem a5l_cube013_not_mem :
    cubeBasis K S013 ∉ Wsp (Submodule.span K {p0 K}) (U0 K) := by
  intro hmem
  have hodd : 2 ≤ (S013.val.filter (fun i : Fin 6 => i.val % 2 = 1)).card := by
    show 2 ≤ (({0, 1, 3} : Finset (Fin 6)).filter (fun i : Fin 6 => i.val % 2 = 1)).card
    decide
  have h1 := coord_eq_zero_of_mem_W0 hmem S013 hodd
  rw [coord_cubeBasis, if_pos rfl] at h1
  exact one_ne_zero h1

private theorem a5l_beta013 : beta K (p0 K) (cubeBasis K S013) = 0 := by
  have hnd : ¬ Disjoint S024.val S013.val := by
    show ¬ Disjoint ({0, 2, 4} : Finset (Fin 6)) ({0, 1, 3} : Finset (Fin 6))
    decide
  rw [p0]
  exact beta_cubeBasis_of_not_disjoint hnd

theorem a5_line_special [Finite K] {g g' : Cube K ≃ₗ[K] Cube K} (hg : g ∈ Gam K) (hg' : g' ∈ Gam K)
    (hW : g (p0 K) ∉ Wsp (Submodule.span K {p0 K}) (U0 K))
    (hβ : beta K (p0 K) (g (p0 K)) = 0) {a b c : K} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : a • p0 K + b • g (p0 K) = c • g' (p0 K)) : False := by
  obtain ⟨gs, hgs, hgsp⟩ := exists_gam_S013 (K := K)
  have hgsW : gs (p0 K) ∉ Wsp (Submodule.span K {p0 K}) (U0 K) := by
    rw [hgsp]
    exact a5l_cube013_not_mem
  have hgsb : beta K (p0 K) (gs (p0 K)) = 0 := by
    rw [hgsp]
    exact a5l_beta013
  have hsp : g (p0 K) ∈ Submodule.span K {p0 K} ↔ gs (p0 K) ∈ Submodule.span K {p0 K} :=
    iff_of_false (fun hm => hW (a5l_span_le hm)) (fun hm => hgsW (a5l_span_le hm))
  have hWiff : g (p0 K) ∈ Wsp (Submodule.span K {p0 K}) (U0 K) ↔
      gs (p0 K) ∈ Wsp (Submodule.span K {p0 K}) (U0 K) :=
    iff_of_false hW hgsW
  have hbiff : beta K (p0 K) (g (p0 K)) = 0 ↔ beta K (p0 K) (gs (p0 K)) = 0 :=
    iff_of_true hβ hgsb
  obtain ⟨H, hH, ⟨d, hd, hHp⟩, ⟨t, ht, hHg⟩⟩ := a5_rank4 g hg gs hgs hsp hWiff hbiff
  have hrel : H (a • p0 K + b • g (p0 K)) = H (c • g' (p0 K)) := by rw [h]
  rw [map_add, map_smul, map_smul, map_smul, hHp, hHg, smul_smul, smul_smul, hgsp] at hrel
  obtain ⟨v, hv⟩ := gam_p0_pure (mul_mem hH hg')
  have hv' : H (g' (p0 K)) = ιMulti K 3 v := hv
  rw [hv'] at hrel
  exact not_pure_special (mul_ne_zero ha hd) (mul_ne_zero hb ht) hc v hrel

private theorem a5l_beta135 : beta K (p0 K) (cubeBasis K S135) ≠ 0 := by
  have hd : Disjoint S024.val S135.val := by
    show Disjoint ({0, 2, 4} : Finset (Fin 6)) ({1, 3, 5} : Finset (Fin 6))
    decide
  rw [p0]
  exact beta_cubeBasis_ne_zero_of_disjoint hd

theorem a5_line_opposite [Finite K] {g g' : Cube K ≃ₗ[K] Cube K} (hg : g ∈ Gam K)
    (hg' : g' ∈ Gam K) (hβ : beta K (p0 K) (g (p0 K)) ≠ 0) {a b c : K} (ha : a ≠ 0)
    (hb : b ≠ 0) (hc : c ≠ 0) (h : a • p0 K + b • g (p0 K) = c • g' (p0 K)) : False := by
  obtain ⟨go, hgo, hgop⟩ := exists_gam_S135 (K := K)
  have hgW : g (p0 K) ∉ Wsp (Submodule.span K {p0 K}) (U0 K) :=
    fun hm => hβ (beta_p0_of_mem_W0 hm)
  have hgob : beta K (p0 K) (go (p0 K)) ≠ 0 := by
    rw [hgop]
    exact a5l_beta135
  have hgoW : go (p0 K) ∉ Wsp (Submodule.span K {p0 K}) (U0 K) :=
    fun hm => hgob (beta_p0_of_mem_W0 hm)
  have hsp : g (p0 K) ∈ Submodule.span K {p0 K} ↔ go (p0 K) ∈ Submodule.span K {p0 K} :=
    iff_of_false (fun hm => hgW (a5l_span_le hm)) (fun hm => hgoW (a5l_span_le hm))
  have hWiff : g (p0 K) ∈ Wsp (Submodule.span K {p0 K}) (U0 K) ↔
      go (p0 K) ∈ Wsp (Submodule.span K {p0 K}) (U0 K) :=
    iff_of_false hgW hgoW
  have hbiff : beta K (p0 K) (g (p0 K)) = 0 ↔ beta K (p0 K) (go (p0 K)) = 0 :=
    iff_of_false hβ hgob
  obtain ⟨H, hH, ⟨d, hd, hHp⟩, ⟨t, ht, hHg⟩⟩ := a5_rank4 g hg go hgo hsp hWiff hbiff
  have hrel : H (a • p0 K + b • g (p0 K)) = H (c • g' (p0 K)) := by rw [h]
  rw [map_add, map_smul, map_smul, map_smul, hHp, hHg, smul_smul, smul_smul, hgop] at hrel
  obtain ⟨v, hv⟩ := gam_p0_pure (mul_mem hH hg')
  have hv' : H (g' (p0 K)) = ιMulti K 3 v := hv
  rw [hv'] at hrel
  exact not_pure_opposite (mul_ne_zero ha hd) (mul_ne_zero hb ht) hc v hrel

theorem a5_line_core [Finite K] {g g' : Cube K ≃ₗ[K] Cube K} (hg : g ∈ Gam K) (hg' : g' ∈ Gam K)
    {a b c : K} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : a • p0 K + b • g (p0 K) = c • g' (p0 K)) :
    g (p0 K) ∈ Wsp (Submodule.span K {p0 K}) (U0 K) := by
  by_cases hW : g (p0 K) ∈ Wsp (Submodule.span K {p0 K}) (U0 K)
  · exact hW
  · by_cases hβ : beta K (p0 K) (g (p0 K)) = 0
    · exact (a5_line_special hg hg' hW hβ ha hb hc h).elim
    · exact (a5_line_opposite hg hg' hβ ha hb hc h).elim

theorem a5MinuscLine [Finite K] : MinuscLine (Gam K) (p0 K) (U0 K) where
  line_iff g₁ hg₁ g₂ hg₂ g₃ hg₃ a b c ha hb hc h := by
    have hinv : g₁⁻¹ ∈ Gam K := inv_mem hg₁
    have h' : a • p0 K + b • (g₁⁻¹ * g₂) (p0 K) = c • (g₁⁻¹ * g₃) (p0 K) := by
      have h1 := congrArg (fun v => g₁⁻¹ v) h
      simpa [map_add, map_smul] using h1
    have hcore := a5_line_core (mul_mem hinv hg₂) (mul_mem hinv hg₃) ha hb hc h'
    have hspan : Submodule.span K {g₁ (p0 K)} =
        (Submodule.span K {p0 K}).map (g₁ : Cube K →ₗ[K] Cube K) := by
      rw [Submodule.map_span, Set.image_singleton]
      rfl
    rw [hspan, Wsp_map]
    exact ⟨(g₁⁻¹ * g₂) (p0 K), hcore, by simp⟩

end CFSG.RankThree.GF2n.Smith81.A5Cube
