module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartTwo.KFacts.AutPSU

public section

namespace CFSG.RankThree.PartTwo.Sec21

namespace Item211Res6Proof

open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts
open Matrix
open scoped MatrixGroups

section UniEmb

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

@[expose] def suToSL : unitarySU p f K 3 →* SL(3, K) where
  toFun g := ⟨((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K), ((mem_unitarySU_iff h).mp g.2).1⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

theorem coe_suToSL (g : unitarySU p f K 3) :
    ((suToSL h g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
  rfl

theorem toGL_suToSL (g : unitarySU p f K 3) :
    SpecialLinearGroup.toGL (suToSL h g) = (g : GL (Fin 3) K) :=
  Units.ext rfl

@[expose] noncomputable def psuToPSL : unitaryPSU h 3 →* projectiveSL 3 K :=
  QuotientGroup.lift (unitaryScalars h 3) ((proj 3 K).comp (suToSL h)) (by
    intro g hg
    obtain ⟨c, -, hc3, hgc⟩ := mem_unitaryScalars.mp hg
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, proj_eq_one_iff]
    refine ⟨c, hc3, ?_⟩
    rw [coe_suToSL, hgc]
    rfl)

theorem psuToPSL_mk (g : unitarySU p f K 3) :
    psuToPSL h (g : unitaryPSU h 3) = proj 3 K (suToSL h g) :=
  rfl

theorem psuToPSL_injective : Function.Injective (psuToPSL h) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [psuToPSL_mk, proj_eq_one_iff] at hx
    obtain ⟨c, hc3, hgc⟩ := hx
    rw [QuotientGroup.eq_one_iff]
    have hg := ((mem_unitarySU_iff h).mp g.2).2
    rw [← coe_suToSL h g, hgc] at hg
    have hn : h.bar (c : K) * c = 1 := by
      have := congrFun (congrFun hg 0) 0
      simpa [Matrix.scalar_apply, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal] using
        this
    refine ⟨c, ?_, hc3, ?_⟩
    · rw [UnitaryFieldData.norm, mul_comm]
      exact hn
    · apply Units.ext
      rw [← coe_suToSL h g, hgc]
      rfl

theorem conjAut_fieldAut_psuToPSL (A : unitaryIsom3 h) (σ : K ≃+* K) (x : unitaryPSU h 3) :
    (conjAut 3 K A * fieldAut 3 K σ) (psuToPSL h x) =
      psuToPSL h ((psuConj h A * psuField h σ) x) := by
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [MulAut.mul_apply, MulAut.mul_apply, psuToPSL_mk, fieldAut_proj, conjAut_proj,
      psuField_mk, psuConj_mk, psuToPSL_mk]
    congr 1
    apply Subtype.ext
    rw [coe_slConjugation, coe_suToSL, coe_suConj, Units.val_mul, Units.val_mul,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, coe_suToSL, coe_suField,
      UnitaryHigher.coe_glAut]
    rfl

end UniEmb

end Item211Res6Proof

end CFSG.RankThree.PartTwo.Sec21
