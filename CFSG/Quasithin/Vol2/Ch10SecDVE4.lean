module

public import CFSG.Quasithin.Vol2.Ch10SecDVE3
public import CFSG.Quasithin.Vol2.Ch10SecD32A
public import CFSG.Quasithin.Vol2.Ch10SecDFacts211b

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique

theorem factVEIrred (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) :
    FactVEIrred := by
  intro G _ _ T L I h h3 hc t v1 v2 hd U hEU hUV hXU hTU
  have hv2t := conj_v2 h37 h38 h h3 hc hd
  obtain ⟨x, hxL, hxX, hxo, hxC⟩ := exists_odd_mem_Xz h37 h38 h h3 hc hd
  obtain ⟨ht, htn, hv1, hv11, hv2, hv21⟩ := hd
  have hcomm12 := commute_V1_V2 h ht
  have hVsup := SecA.fsuVM_eq_sup h37 h38 h ht htn
  have hxz : x ∈ Subgroup.centralizer ({v1 * v2} : Set G) := (oTwoUpper_le _ hxX).2
  have hxv2 : x * v2 * x⁻¹ = v2 := by
    rw [Subgroup.mem_centralizer_iff.mp (V2_le_centralizer_L h37 h38 h ht htn hv2.1) x hxL]
    group
  have hxv1 : x * v1 * x⁻¹ = v1 := by
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp hxz
    calc x * v1 * x⁻¹ = x * (v1 * v2) * x⁻¹ * (x * v2 * x⁻¹)⁻¹ := by group
      _ = v1 := by rw [h1, hxv2]; group
  have hxU : x ∈ Subgroup.normalizer (U : Set G) := hXU hxX
  have hv1U : v1 ∈ U := hEU (Subgroup.subset_closure (by simp))
  have hEmem : ∀ a b : G, (a = 1 ∨ a = v1) → (b = 1 ∨ b = v2) →
      a * b ∈ Subgroup.closure ({v1, v2} : Set G) := by
    intro a b ha hb
    refine Subgroup.mul_mem _ ?_ ?_
    · rcases ha with rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.subset_closure (by simp)
    · rcases hb with rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.subset_closure (by simp)
  have htV2 : ∀ y ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆, t * y * t⁻¹ ∈ fsuUL T L I := by
    intro y hy
    rw [← SecA.conjugate_commutator_fsuVM (SecA.le_fsuM T L ht), SecA.mem_conjugate_iff] at hy
    exact hy
  have htt : t * t ∈ Subgroup.normalizer (fsuUL T L I : Set G) :=
    SecA.le_normalizer_commutator (X := T1 T L)
      (inf_le_left.trans (SecA.le_normalizer_fsuVM T L I)) inf_le_right
      ⟨T.mul_mem ht ht, SecA.mul_self_mem_normalizer h37 h38 h ht htn⟩
  have htV1 : ∀ y ∈ fsuUL T L I, t * y * t⁻¹ ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆ := by
    intro y hy
    rw [← SecA.conjugate_commutator_fsuVM (SecA.le_fsuM T L ht), SecA.mem_conjugate_iff]
    have := (Subgroup.mem_normalizer_iff.mp htt y).mp hy
    simpa [mul_assoc] using this
  by_contra hcon
  push Not at hcon
  obtain ⟨u, huU, huE⟩ : ∃ u ∈ U, u ∉ Subgroup.closure ({v1, v2} : Set G) := by
    by_contra h'
    push Not at h'
    exact hcon.1 (le_antisymm h' hEU)
  obtain ⟨u1, hu1, u2, hu2, rfl⟩ := exists_mul_of_mem_sup_of_comm hcomm12 (hVsup.le (hUV huU))
  have hV1U : fsuUL T L I ≤ U := by
    by_cases h1 : u1 = 1 ∨ u1 = v1
    · have h2 : u2 ≠ 1 ∧ u2 ≠ v2 := by
        by_contra h2
        apply huE
        refine hEmem u1 u2 h1 ?_
        by_cases h21 : u2 = 1
        · exact Or.inl h21
        · exact Or.inr (by tauto)
      have htu : t * (u1 * u2) * t⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hTU ht) _).mp huU
      have e : t * (u1 * u2) * t⁻¹ = (t * u2 * t⁻¹) * (t * u1 * t⁻¹) := by
        rw [hcomm12 u1 hu1 u2 hu2]
        group
      rw [e] at htu
      refine le_of_component h37 h38 h h3 hc ht htn hv1.1 hv11 hxL hxo hxv1 hxC hxU hv1U htu
        (htV2 u2 hu2) (htV1 u1 hu1) ?_ ?_
      · intro h3'
        apply h2.1
        calc u2 = t⁻¹ * (t * u2 * t⁻¹) * t := by group
          _ = 1 := by rw [h3']; group
      · intro h3'
        apply h2.2
        calc u2 = t⁻¹ * (t * u2 * t⁻¹) * t := by group
          _ = t⁻¹ * (t * v2 * t⁻¹) * t := by rw [h3', hv2t]
          _ = v2 := by group
    · push Not at h1
      exact le_of_component h37 h38 h h3 hc ht htn hv1.1 hv11 hxL hxo hxv1 hxC hxU hv1U huU hu1
        hu2 h1.1 h1.2
  have hV2U : ⁅fsuVM T L I, CFSG.conjugate L t⁆ ≤ U := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (hTU ht) y).mpr (hV1U (htV2 y hy))
  exact hcon.2 (le_antisymm hUV (hVsup.le.trans (sup_le hV1U hV2U)))

end CFSG.Quasithin.Vol2.Ch10.SecD
