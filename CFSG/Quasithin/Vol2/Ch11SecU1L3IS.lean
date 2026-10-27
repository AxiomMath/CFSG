module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismTransport
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80L3Par

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.L3I

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
  Module CFSG.Quasithin.E2P.Asc80 CFSG.Quasithin.A38c15
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime]

@[expose] noncomputable def lineE3 (p : ℕ) [Fact p.Prime] : Submodule (ZMod p) (Fin 3 → ZMod p) :=
  Submodule.span (ZMod p) {(Pi.single 2 1 : Fin 3 → ZMod p)}

theorem linePar_eq_stabilizer : linePar p = stabilizer (lineE3 p) := by
  ext g
  rw [mem_linePar_iff, mem_stabilizer, lineE3, Submodule.map_span, Set.image_singleton,
    Submodule.span_singleton_eq_span_singleton, mulVecLin_apply, mulVec_single_one]
  constructor
  · rintro ⟨h0, h1⟩
    have hdet : (g : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1 := g.2
    rw [det_eq_ulBlock_mul h0 h1] at hdet
    have h22 : (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 2 2 ≠ 0 := fun h => by
      rw [h, mul_zero] at hdet
      exact zero_ne_one hdet
    refine ⟨(Units.mk0 _ h22)⁻¹, ?_⟩
    ext i
    fin_cases i
    · simp [col, h0]
    · simp [col, h1]
    · simp [col, Units.smul_def, inv_mul_cancel₀ h22]
  · rintro ⟨z, hz⟩
    have e0 := congrFun hz 0
    have e1 := congrFun hz 1
    simp [col] at e0 e1
    exact ⟨(smul_eq_zero_iff_eq z).mp e0, (smul_eq_zero_iff_eq z).mp e1⟩

@[expose] noncomputable def psl3EquivP (p : ℕ) [Fact p.Prime] : PSL3 p ≃* projectiveSL 3 (ZMod p) :=
  LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 (ZMod p)

theorem map_lineC_eq : (lineC p).map (psl3EquivP p).toMonoidHom = projStabilizer (lineE3 p) := by
  rw [lineC, Subgroup.map_map, linePar_eq_stabilizer]
  rfl

theorem map_planeC_eq :
    (planeC p).map (psl3EquivP p).toMonoidHom = projStabilizer (dotOrth (lineE3 p)) := by
  obtain ⟨-, -, -, -, -, -, -, -, hdual, -⟩ :=
    standard_automorphism_transport (n := 3) (K := ZMod p)
  rw [← hdual, ← map_lineC_eq, planeC, planePar_eq_map, lineC, Subgroup.map_map,
    Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
  congr 1

end CFSG.Quasithin.Vol2.Ch11.SecU1.L3I
