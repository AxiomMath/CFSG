module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocLineG4

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.Open U42F431
open scoped Pointwise

namespace Ctx

variable {G : Type} [Group G]
  (C : Ctx G)

theorem isPt_Φ2_sY {p : Fin 45} (hp : p ∈ L0S) : C.IsPt (C.Φ2 (sY p)) := by
  obtain ⟨e, heP, hee⟩ := exists_P2_conj_sY hp
  refine ⟨C.Φ2 e, ?_⟩
  rw [C.z_eq, ← C.Φ2_conj heP mem_P2_xY, hee]

variable [Finite G]

theorem not_isPt_sY_mul {p : Fin 45} (hp : p = 0 ∨ p = 20 ∨ p = 24) :
    ¬ C.IsPt (C.Φ2 (sY p) * C.tG) := by
  have hpL : p ∈ L0S := by
    rcases hp with rfl | rfl | rfl
    · exact zero_mem_L0S
    · exact (mem_L0S_iff 20).2 (by simp)
    · exact (mem_L0S_iff 24).2 (by simp)
  rintro ⟨g, hg⟩
  have hmul : C.Φ2 (sY p) * C.tG = C.Φ2 (sY p * tPrime) := by
    rw [tG_def, C.Φ2_mul (Vsub_le_P2 (sY_mem_Vsub hpL)) (Vsub_le_P2 tPrime_mem_Vsub)]
  rw [hmul] at hg
  exact C.not_conj_z (Vsub.mul_mem (sY_mem_Vsub hpL) tPrime_mem_Vsub) (not_isConj_sY_mul hp) g hg

theorem line_unique {u : G} (hu : C.IsPt u) (hut : u * C.tG = C.tG * u) {W W' : Subgroup G}
    (hW : C.IsLn W) (hW' : C.IsLn W') (huW : u ∈ W) (htW : C.tG ∈ W) (huW' : u ∈ W')
    (htW' : C.tG ∈ W') : W = W' := by
  obtain ⟨g, rfl⟩ := hu
  obtain ⟨a, m, -, -, -, -, -, -, -, huniq⟩ := C.local_line hut
  rw [huniq W hW huW htW, huniq W' hW' huW' htW']

theorem line_comm {u u' : G} (hu : C.IsPt u) (hu' : C.IsPt u') (hut : u * C.tG = C.tG * u)
    (hu't : u' * C.tG = C.tG * u') (huu' : u * u' = u' * u) {W : Subgroup G} (hW : C.IsLn W)
    (huW : u ∈ W) (htW : C.tG ∈ W) : u' ∈ W := by
  obtain ⟨g, hgu⟩ := hu
  subst hgu
  obtain ⟨a, m, haP, hmP, haΦ, hV, ha2, ha1, hnc, huniq⟩ := C.local_line hut
  rw [huniq W hW huW htW]
  obtain ⟨a', ha'P, ha'Φ, ha'2, ha'1⟩ := C.exists_pull huu' (C.isPt_sq hu') (C.isPt_ne_one hu')
  have hc' : IsConj xY a' := C.isConj_of_isPt ha'P ha'2 ha'1 hu' ha'Φ
  have hcomm : a * a' = a' * a := by
    apply C.Φ1_inj (P1.mul_mem haP ha'P) (P1.mul_mem ha'P haP)
    rw [C.Φ1_mul haP ha'P, C.Φ1_mul ha'P haP, haΦ, ha'Φ]
    calc g⁻¹ * C.tG * g * (g⁻¹ * u' * g) = g⁻¹ * (C.tG * u') * g := by group
      _ = g⁻¹ * (u' * C.tG) * g := by rw [hu't]
      _ = g⁻¹ * u' * g * (g⁻¹ * C.tG * g) := by group
  have hVa' := mem_Vconj_of_comm hV ha2 ha1 hnc hc' hcomm
  have h1 := C.Φ1_mem_V2 (mem_Vconj.1 hVa')
  have ha'P' : a' ∈ P1 := ha'P
  rw [C.Φ1_mul (P1.mul_mem (P1.inv_mem hmP) ha'P') hmP, C.Φ1_mul (P1.inv_mem hmP) ha'P',
    C.Φ1_inv hmP, ha'Φ] at h1
  rw [mem_map_conj]
  have : (g * C.Φ1 m)⁻¹ * u' * (g * C.Φ1 m) = (C.Φ1 m)⁻¹ * (g⁻¹ * u' * g) * C.Φ1 m := by group
  rwa [this]

end Ctx

end CFSG.Quasithin.H13.F431.U42
