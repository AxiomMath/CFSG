module

public import CFSG.Quasithin.Vol2.Ch11SecA14Lines
public import CFSG.Quasithin.Vol2.Ch10SecABasicCent

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem map_conj_eq_of_mem_centralizer {U V : Subgroup G} (hUV : U ≤ V) {c : G}
    (hc : c ∈ Subgroup.centralizer (V : Set G)) : U.map (MulAut.conj c).toMonoidHom = U :=
  map_conj_eq_of_mem_normalizer (Subgroup.centralizer_le_normalizer (U : Set G)
    (Subgroup.centralizer_le (by exact_mod_cast hUV) hc))

variable [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem iSup_lOf_eq (hD : FactDeltaSp4) (hD' : FactDeltaG2) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I n) (hk : ¬ KindSL3 L (fsuV T I) n) {U₁ U₂ U₃ : Subgroup G}
    (hU₁ : IsVi T L I n 1 U₁) (hU₂ : IsVi T L I n 2 U₂) (hU₃ : IsVi T L I n 3 U₃) :
    (⨆ x ∈ LOf L U₁, LOf L (U₂.map (MulAut.conj x).toMonoidHom)) = L := by
  set N := ⨆ x ∈ LOf L U₁, LOf L (U₂.map (MulAut.conj x).toMonoidHom) with hNdef
  have hL := L_le_normalizer_fsuV h
  have hNL : N ≤ L := iSup₂_le fun x _ => lOf_le L _
  have hH : autOn L (fsuV T I) ≤ autOn N (fsuV T I) := by
    rw [← (deltaFacts hD hD' h1102 h hk hU₁ hU₂ hU₃).2.2]
    refine iSup₂_le fun g hg => ?_
    rw [← autOn_lOf hL (IsVi.le_fsuV hU₁)] at hg
    obtain ⟨x, hx, hxV, rfl⟩ := mem_autOn_iff.mp hg
    have hU₂x : U₂.map (MulAut.conj x).toMonoidHom ≤ fsuV T I := by
      rw [← map_conj_eq_of_mem_normalizer hxV]
      exact Subgroup.map_mono (IsVi.le_fsuV hU₂)
    rw [← subgroupOf_map_conj hxV, ← autOn_lOf hL hU₂x]
    exact autOn_mono (le_iSup₂_of_le x hx le_rfl)
  have hsup : ∀ l ∈ L, ∃ m ∈ N, m⁻¹ * l ∈ pCoreOf 2 L := by
    intro l hl
    obtain ⟨m, hm, hmV, he⟩ := mem_autOn_iff.mp (hH (conjV_mem_autOn hl (hL hl)))
    refine ⟨m, hm, ?_⟩
    rw [← centralizer_eq_pCoreOf h1102 h]
    refine Subgroup.mem_inf.mpr ⟨L.mul_mem (L.inv_mem (hNL hm)) hl, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have e := congrArg (fun φ : MulAut ↥(fsuV T I) => ((φ ⟨v, hv⟩ : ↥(fsuV T I)) : G)) he
    simp only [conjV_apply_coe] at e
    calc v * (m⁻¹ * l) = m⁻¹ * (m * v * m⁻¹) * l := by group
      _ = m⁻¹ * (l * v * l⁻¹) * l := by rw [e]
      _ = m⁻¹ * l * v := by group
  have hn : L ≤ Subgroup.normalizer (N : Set G) := by
    intro l hl
    obtain ⟨m, hm, hc⟩ := hsup l hl
    have hl' : l = m * (m⁻¹ * l) := by group
    rw [hl']
    refine Subgroup.mul_mem _ (Subgroup.le_normalizer hm) ?_
    rw [← centralizer_eq_pCoreOf h1102 h] at hc
    obtain ⟨hcL, hcC⟩ := Subgroup.mem_inf.mp hc
    refine mem_normalizer_of_map_le ?_
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun x hx => ?_
    rw [← Subgroup.map_le_iff_le_comap, map_conj_lOf _ (Subgroup.le_normalizer hcL)]
    have hU₂x : U₂.map (MulAut.conj x).toMonoidHom ≤ fsuV T I := by
      rw [← map_conj_eq_of_mem_normalizer (hL ((lOf_le L U₁) hx))]
      exact Subgroup.map_mono (IsVi.le_fsuV hU₂)
    rw [map_conj_eq_of_mem_centralizer hU₂x hcC]
    exact le_iSup₂_of_le x hx le_rfl
  exact Ch10.SecA.eq_of_forall_mul_mem_pCoreOf h.fsu.faithful hNL hn hsup

end CFSG.Quasithin.Vol2.Ch11.SecA
