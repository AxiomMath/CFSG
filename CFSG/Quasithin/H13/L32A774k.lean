module

public import CFSG.Quasithin.H13.L32A773h

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

namespace Ctx73

variable {T L V : Subgroup G} {l₀ : G} (C : Ctx73 G T L V l₀)
include C

theorem normalizer_eq (h67 : Lemma14_7_67) : Subgroup.normalizer (L : Set G) = L := by
  obtain ⟨-, -, -, -, hVZ, -, -⟩ := C.lemma14_7_72
  have hNS : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (sL T L V : Set G) := by
    rw [← C.pCoreOf_eq_sL]
    exact normalizer_le_normalizer_pCoreOf 2 L
  have hSV : Subgroup.normalizer (sL T L V : Set G) ≤ Subgroup.normalizer (V : Set G) := by
    refine le_normalizer_of_conj_mem' fun g hg v hv => ?_
    rw [hVZ] at hv ⊢
    obtain ⟨hvS, hvC⟩ := Subgroup.mem_inf.mp hv
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hg v).mp hvS, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hs' : g⁻¹ * s * g ∈ sL T L V := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) s).mp hs
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hvC _ hs'
    calc s * (g * v * g⁻¹) = g * ((g⁻¹ * s * g) * v) * g⁻¹ := by group
      _ = g * (v * (g⁻¹ * s * g)) * g⁻¹ := by rw [h1]
      _ = g * v * g⁻¹ * s := by group
  have hNV := (h67 G T L V C.hyp).2.2.2.2
  refine le_antisymm (fun g hg => ?_) Subgroup.le_normalizer
  have h1 := hSV (hNS hg)
  rw [← hNV, sup_eq_left.mpr C.T_le_L] at h1
  exact h1

theorem lemma14_7_74 (h67 : Lemma14_7_67) :
    (Subgroup.normalizer (L : Set G) = L ∧
      sL T L V = pCoreOf 2 (Subgroup.normalizer (L : Set G))) ∧
    (hz T V = kz T V ⊔ T ∧ pCoreOf 2 (hz T V) = pCoreOf 2 (kz T V)) := by
  refine ⟨⟨C.normalizer_eq h67, ?_⟩, (C.h63 G T L V C.hyp).2.2.1, C.pCoreOf_hz_eq⟩
  rw [C.normalizer_eq h67]
  exact C.pCoreOf_eq_sL.symm

end Ctx73

theorem lemma14_7_74_of
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h63 : Thm14_7_63)
    (h67 : Lemma14_7_67) (h68 : Lemma14_7_68) (h69 : Lemma14_7_69) (h70 : Lemma14_7_70)
    (h71 : Lemma14_7_71) (vh63 : H6.VolI_H_6_3) (vh65 : H6.VolI_H_6_5) : Lemma14_7_74 := by
  have h1334 : A6.Stmt13_3_4 := U3.stmt13_3_4_of h1332
  intro G _ _ T L V h
  have hF : HypF98 T V L (fsuV1 T V) V (hz T V) :=
    Setting147.hypF98 ⟨h, h.isHzOne_hz h63⟩ (stmt13_3_2_two_of_stmt13_3_2 h1332)
      (stmtL32NModule_of_inputs h1332 h1334) h1222
  obtain ⟨l₀, C⟩ := exists_ctx73 h h1222 h1332 h1334 h63 hF h68 h69 h70 h71 vh63 vh65
  exact C.lemma14_7_74 h67

end CFSG.Quasithin.H13.L32A
