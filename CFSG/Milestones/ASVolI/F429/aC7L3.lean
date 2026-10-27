module

import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Polygon
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Milestones.ASVolI.F4Polygon

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.ASVolI.ChF.ClassicalRoots CFSG.Quasithin

section L3Root

variable {K : Type} [Field K] {E : Type} [Group E]

theorem burnsideF429a_L3_T_mem_ctr (φ : ↥(StatedSL 3 K) →* E) {g : ↥(StatedSL 3 K)} {t : K}
    (hgv : (g : GL (Fin 3) K).val = (1 : Matrix (Fin 3) (Fin 3) K) + matrixUnit 0 2 t) :
    φ g ∈ ctr ((burnsideF4f_U0 K).map φ) := by
  have hgU : g ∈ burnsideF4f_U0 K := by
    refine ⟨(burnsideF4f_mem_B0 _).mpr ?_, ?_, ?_, ?_⟩ <;>
      simp [hgv, matrixUnit, Matrix.one_apply]
  have h01 : (g : GL (Fin 3) K).val 0 1 = 0 := by simp [hgv, matrixUnit, Matrix.one_apply]
  have h12 : (g : GL (Fin 3) K).val 1 2 = 0 := by simp [hgv, matrixUnit, Matrix.one_apply]
  refine Subgroup.mem_inf.2 ⟨⟨g, hgU, rfl⟩, Subgroup.mem_centralizer_iff.2 ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  rw [← map_mul, ← map_mul, (burnsideF4f_U0_comm_E02 hgU hu h01 h12).symm]

end L3Root

theorem burnsideF429a_c7_L3 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .L3 2 f Gp M₁ M₂) :
    ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) = hyp.toHypF_4_4g.chart.longRoot := by
  obtain ⟨marking, hb, -, -, hl⟩ := burnsideF4f_L3_marking hyp.toHypF_4_4g.chart
  have hK : Nat.card marking.field = 2 ^ f := by simpa using marking.field_card
  haveI : CharP marking.field 2 := burnsideF4f_charP_of_card marking.exponent_pos hK
  have hbasis : marking.basis = 1 := marking.basis_compatible
  let φ : ↥(StatedSL 3 marking.field) →* E := Gp.subtype.comp marking.transport
  have hker : ∀ g : ↥(StatedSL 3 marking.field),
      φ g = 1 ↔ (g : GL (Fin 3) marking.field) ∈ StatedScalars (Fin 3) marking.field := by
    intro g
    rw [← burnsideF4f_transport_eq_one_iff marking g]
    show ((marking.transport g : ↥Gp) : E) = 1 ↔ _
    rw [OneMemClass.coe_eq_one]
  have hB : Gp ⊓ (M₁ ⊓ M₂) = (burnsideF4f_B0 marking.field).map φ := by
    rw [hyp.toHypF_4_4g.chart_matches.1, hb]
    unfold ClassicalRoots.Marking.borel
    rw [Subgroup.map_map, hbasis]
    rfl
  rw [hB, burnsideF4f_L3_pCore_B0 φ hker, hl]
  apply le_antisymm
  · rintro z ⟨⟨g, hgU, rfl⟩, hzC⟩
    have hcomm : ∀ n ∈ (burnsideF4f_U0 marking.field).map φ, φ g * n = n * φ g :=
      fun n hn => (Subgroup.mem_centralizer_iff.mp hzC n hn).symm
    obtain ⟨ha, hc⟩ := burnsideF4f_L3_central φ hker hgU hcomm
    obtain ⟨g10, g20, g21⟩ := burnsideF4f_B0_entries (burnsideF4f_U0_le_B0 hgU)
    refine ⟨marking.transport g, ⟨g, ?_, rfl⟩, rfl⟩
    rw [hbasis]
    refine Subgroup.subset_closure ⟨Or.inr (Or.inr rfl), (g : GL (Fin 3) marking.field).val 0 2,
      0, trivial, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [markedMatrix, positiveMatrix, linearRoot, matrixUnit, Matrix.one_apply,
        burnsideF4f_U0_diag hgU, ha, hc, g10, g20, g21]
  · unfold ClassicalRoots.Marking.root
    rw [Subgroup.map_map, Subgroup.map_le_iff_le_comap, hbasis]
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨-, t, c, -, hg⟩
    have hgv : (g : GL (Fin 3) marking.field).val =
        (1 : Matrix (Fin 3) (Fin 3) marking.field) + matrixUnit 0 2 t := by
      rw [hg]
      simp [markedMatrix, positiveMatrix, linearRoot]
    exact burnsideF429a_L3_T_mem_ctr φ (g := g) hgv

end CFSG.ASVolI
