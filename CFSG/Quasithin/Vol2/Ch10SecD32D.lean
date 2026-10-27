module

public import CFSG.Quasithin.Vol2.Ch10SecD32B
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Helpers

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem exists_conj_fsuM (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h1029 : Stmt10_2_9) (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I)
    (hc : fsuCVM T L I = ⊥) {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    {z : G} (hzV : z ∈ fsuVM T L I) (hz1 : z ≠ 1) (hzT : T ≤ Subgroup.centralizer ({z} : Set G))
    {u : G} (hu : u ∈ fsuVM T L I) {g : G} (hg : g⁻¹ * u * g ∈ fsuVM T L I) :
    ∃ m ∈ fsuM T L, g⁻¹ * u * g = m⁻¹ * u * m := by
  have hzt : t * z = z * t := Subgroup.mem_centralizer_singleton_iff.mp (hzT ht)
  by_cases hu1 : u = 1
  · refine ⟨1, (fsuM T L).one_mem, ?_⟩
    rw [hu1]
    group
  have hu1' : g⁻¹ * u * g ≠ 1 := fun h' => hu1 (by
    calc u = g * (g⁻¹ * u * g) * g⁻¹ := by group
      _ = 1 := by rw [h']; group)
  have hL0M : ∀ {x : G}, x ∈ fsuL0 T L → x ∈ fsuM T L := fun hx => SecA.fsuL0_le_fsuM T L hx
  rcases conj_z_or_mem h37 h38 h h3 hc ht htn hzV hz1 hzt hu with ⟨x, hx, hxu⟩ | hu'
  · rcases conj_z_or_mem h37 h38 h h3 hc ht htn hzV hz1 hzt hg with ⟨x', hx', hxu'⟩ | hu''
    · refine ⟨x * x'⁻¹, (fsuM T L).mul_mem (hL0M hx) ((fsuM T L).inv_mem (hL0M hx')), ?_⟩
      rw [← hxu', ← hxu]
      group
    · exact (not_conj_z_mem h37 h38 h1029 h hc ht htn hzT hu'' hu1' (y := g⁻¹ * x)
        (by rw [← hxu]; group)).elim
  · rcases conj_z_or_mem h37 h38 h h3 hc ht htn hzV hz1 hzt hg with ⟨x', hx', hxu'⟩ | hu''
    · refine (not_conj_z_mem h37 h38 h1029 h hc ht htn hzT hu' hu1 (y := g * x') ?_).elim
      calc g * x' * z * (g * x')⁻¹ = g * (x' * z * x'⁻¹) * g⁻¹ := by group
        _ = g * (g⁻¹ * u * g) * g⁻¹ := by rw [hxu']
        _ = u := by group
    · exact exists_conj_nondiag h3 hc ht hu' hu'' hu1 hu1'

theorem fusionIsTI_V (h331 : Stmt3_3_1) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h1029 : Stmt10_2_9) (h : Hyp10 G T L I)
    (h3 : Case10_1_1Three T L I) (hc : fsuCVM T L I = ⊥) {z : G} (hzV : z ∈ fsuVM T L I)
    (hz1 : z ≠ 1) (hzT : T ≤ Subgroup.centralizer ({z} : Set G))
    (hzM : Subgroup.centralizer ({z} : Set G) ≤ fsuM T L) : fusionIsTI (fsuVM T L I) := by
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp h.not_normal
  have hzt : t * z = z * t := Subgroup.mem_centralizer_singleton_iff.mp (hzT ht)
  exact Lin2.fusionIsTI_of_centralizer_le
    (SecA.normalizer_fsuVM_eq h (SecB.fsuM_isMaxTwoLocal h331 h))
    (fun u hu hu1 => centralizer_le_fsuM h37 h38 h1029 h h3 hc ht htn hzV hz1 hzt hzM hu hu1)
    (fun u hu g hg => exists_conj_fsuM h37 h38 h1029 h h3 hc ht htn hzV hz1 hzT hu hg)

end CFSG.Quasithin.Vol2.Ch10.SecD
