module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtY15111Set17
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtY15111Cop

public section

namespace CFSG.Quasithin

namespace Y15111

open CFSG.Open CFSG.QuasithinUnique B2F

variable {G : Type} [Group G] [Finite G] {H T M V U : Subgroup G} {x z : G}

theorem dpP_inf_centralizer_le (s : E2.Setting17 H T M V U x z) :
    E2.dpP H V U z ⊓ Subgroup.centralizer (V : Set G) ≤ U := by
  rintro d ⟨hdP, hdC⟩
  obtain ⟨u, hu, a, ha, rfl⟩ := s.dp.mem_P hdP
  have huC : u ∈ Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact isElemAbelian_comm s.dp.elem hv (s.dp.UV hu)
  have haC : a ∈ Subgroup.centralizer (V : Set G) := by
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ huC) hdC
    simpa using this
  have hU : U ⊓ Subgroup.centralizer (E2.dpA H V U z : Set G) = E2.dpZ V z :=
    s.dp.U_inf_centralizer s.CA
  have hA := s.dp.A_inf_centralizer_U hU
  have haU : a ∈ E2.dpA H V U z ⊓ Subgroup.centralizer (U : Set G) := by
    refine ⟨ha, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    exact Subgroup.mem_centralizer_iff.mp haC v (s.dp.UV hv)
  rw [hA] at haU
  exact U.mul_mem hu (s.dp.ZU haU)

theorem exists_involution_dpA (s : E2.Setting17 H T M V U x z) :
    ∃ a ∈ E2.dpA H V U z, a ∉ Subgroup.centralizer (V : Set G) ∧ a * a = 1 := by
  have hex : ∃ a ∈ E2.dpA H V U z, a ∉ Subgroup.centralizer (V : Set G) := by
    by_contra hcon
    push Not at hcon
    have hVC : V ≤ Subgroup.centralizer (E2.dpA H V U z : Set G) := by
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (Subgroup.mem_centralizer_iff.mp (hcon a ha) v hv).symm
    have h1 : V ⊓ Subgroup.centralizer (E2.dpA H V U z : Set G) = V := inf_eq_left.mpr hVC
    have h2 := s.CA
    rw [h1] at h2
    have h3 := s.Z2
    rw [← h2, s.V16] at h3
    norm_num at h3
  obtain ⟨a, ha, haC⟩ := hex
  exact ⟨a, ha, haC, by simpa [pow_two] using s.dp.Ael.2 a ha⟩

theorem comm_mem_V (s : E2.Setting17 H T M V U x z)
    (hHP : H ≤ Subgroup.normalizer (E2.dpP H V U z : Set G)) {a : G} (ha : a ∈ E2.dpP H V U z)
    {r : G} (hrT : r ∈ T) (hrC : r ∈ Subgroup.centralizer (V : Set G)) :
    a * r * a⁻¹ * r⁻¹ ∈ V := by
  have haT : a ∈ T := s.dp.QT (dpP_le_pCoreOf s ha)
  have h1 : r * a⁻¹ * r⁻¹ ∈ E2.dpP H V U z :=
    (Subgroup.mem_normalizer_iff.mp (hHP (s.dp.TH hrT)) a⁻¹).mp ((E2.dpP H V U z).inv_mem ha)
  have hP : a * r * a⁻¹ * r⁻¹ ∈ E2.dpP H V U z := by
    have e : a * r * a⁻¹ * r⁻¹ = a * (r * a⁻¹ * r⁻¹) := by group
    rw [e]
    exact (E2.dpP H V U z).mul_mem ha h1
  have haN : a ∈ Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) :=
    mem_normalizer_centralizer (s.dp.TV haT)
  have h2 : a * r * a⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
    (Subgroup.mem_normalizer_iff.mp haN r).mp hrC
  have hC : a * r * a⁻¹ * r⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
    Subgroup.mul_mem _ h2 (Subgroup.inv_mem _ hrC)
  exact s.dp.UV (dpP_inf_centralizer_le s ⟨hP, hC⟩)

end Y15111

end CFSG.Quasithin
