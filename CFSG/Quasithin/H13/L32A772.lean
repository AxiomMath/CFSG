module

public import CFSG.Quasithin.H13.L32A774j
public import CFSG.Quasithin.H13.U3L134

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem exists_ctx73 {T L V : Subgroup G} (h : Hyp147 G T L V) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h68 : Lemma14_7_68) (h69 : Lemma14_7_69)
    (h70 : Lemma14_7_70) (h71 : Lemma14_7_71) (vh63 : H6.VolI_H_6_3)
    (vh65 : H6.VolI_H_6_5) : ∃ l₀ : G, Ctx73 G T L V l₀ := by
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  obtain ⟨hcard, γ, γ', g, k, V₂, hN, -, -, hcap, hrel, -, hb3, l₀, hl₀, hUα⟩ := h70 G T L V h
  have hU := fsuU_eq_conjClosure_hz hMod h
  have hne : conjSub l₀ (fsuU T V) ≠ fsuU T V := by
    rw [← hUα, hU]
    exact hN.uα_ne hF
  have hnorm : fsuU T V ≤ Subgroup.normalizer (conjSub l₀ (fsuU T V) : Set G) := by
    rw [← hUα, hU]
    exact hN.le_normalizer hF
  have hα := h69 G T L V h γ γ' g k hN
  rw [hUα] at hcap hrel hα
  have C72 : Ctx72 G T L V l₀ :=
    { hyp := h, h1222 := h1222, h1332 := h1332, h1334 := h1334, h63 := h63, hF := hF,
      card_u0 := hcard, mem := hl₀, ne := hne, norm := hnorm, cap := hcap, rel := hrel,
      b3 := hb3, h71 := (h71 G T L V h).1.2 }
  exact ⟨l₀,
    { toCtx72 := C72, u0_eq := C72.u0_eq h68, vh63 := vh63, vh65 := vh65, l71 := h71,
      uα := hα }⟩

namespace Ctx73

variable {T L V : Subgroup G} {l₀ : G} (C : Ctx73 G T L V l₀)
include C

theorem lemma14_7_72 :
    sL T L V = pCoreOf 2 L ∧ pCoreOf 2 L = ⁅pCoreOf 2 L, L⁆ ∧
      IsSteinbergSection L (sL T L V) V ∧
      (∀ u ∈ fsuU T V, (∀ k ∈ kz T V, k * u * k⁻¹ * u⁻¹ ∈ fsuV1 T V) → u ∈ fsuV1 T V) ∧
      V = centerOf (sL T L V) ∧ V = frattiniOf (sL T L V) ∧ V = ⁅sL T L V, sL T L V⁆ := by
  obtain ⟨-, -, -, hV1, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
  have hUe := isElemAbelian_fsuU_of C.hyp C.hMod
  have hS := C.pCoreOf_eq_sL
  refine ⟨hS.symm, ?_, C.isSteinbergSection C.u0_eq C.vh63 C.vh65 C.l71, ?_,
    (C.centerOf_eq C.u0_eq C.vh63 C.vh65 C.l71).symm, (C.frattiniOf_eq_v C.u0_eq).symm,
    (C.commutator_eq_v C.u0_eq).symm⟩
  · rw [hS]
    exact (C.commutator_sL_eq C.u0_eq C.vh63 C.vh65 C.l71).symm
  · intro u hu hK
    have hu0 : u ∈ u0 T V := mem_centralizerMod.mpr ⟨hu, by
      rw [normalizer_eq_centralizer_of_card_two hV1, Subgroup.mem_centralizer_iff]
      intro w hw
      exact F7.isElemAbelian_comm hUe (v_le_fsuU (Subgroup.mem_inf.mp hw).1) hu,
      fun k hk => by
        have := inv_mem (hK k hk)
        rwa [show (k * u * k⁻¹ * u⁻¹)⁻¹ = u * k * u⁻¹ * k⁻¹ by group] at this⟩
    rw [← C.u0_eq]
    exact hu0

end Ctx73

theorem lemma14_7_72_of
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h63 : Thm14_7_63)
    (h68 : Lemma14_7_68) (h69 : Lemma14_7_69) (h70 : Lemma14_7_70) (h71 : Lemma14_7_71)
    (vh63 : H6.VolI_H_6_3) (vh65 : H6.VolI_H_6_5) : Lemma14_7_72 := by
  have h1334 : A6.Stmt13_3_4 := U3.stmt13_3_4_of h1332
  intro G _ _ T L V h
  have hF : HypF98 T V L (fsuV1 T V) V (hz T V) :=
    Setting147.hypF98 ⟨h, h.isHzOne_hz h63⟩ (stmt13_3_2_two_of_stmt13_3_2 h1332)
      (stmtL32NModule_of_inputs h1332 h1334) h1222
  obtain ⟨l₀, C⟩ := exists_ctx73 h h1222 h1332 h1334 h63 hF h68 h69 h70 h71 vh63 vh65
  exact C.lemma14_7_72

end CFSG.Quasithin.H13.L32A
