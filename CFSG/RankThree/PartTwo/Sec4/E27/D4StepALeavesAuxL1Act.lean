module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.Chevalley.SteinbergBITrialitySingularSL3

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec4.E27

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups Pointwise

section Act

variable {Ω : Type} [Field Ω]

@[expose] def diagGL (a b : Ω) (ha : a ≠ 0) (hb : b ≠ 0) : GL (Fin 3) Ω where
  val := Matrix.diagonal ![a * b, b, 1]
  inv := Matrix.diagonal ![(a * b)⁻¹, b⁻¹, 1]
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    fin_cases k
    · exact mul_inv_cancel₀ (mul_ne_zero ha hb)
    · exact mul_inv_cancel₀ hb
    · simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    fin_cases k
    · exact inv_mul_cancel₀ (mul_ne_zero ha hb)
    · exact inv_mul_cancel₀ hb
    · simp

theorem torus_action_on_Qv (v : WeylGroup Tag.D4) {h : ModGL Tag.D4 Ω}
    (hh : h ∈ torusGroup Tag.D4 Ω) :
    ∃ D : GL (Fin 3) Ω, ∀ y y' : d4A2Qv Ω v, (y' : ModGL Tag.D4 Ω) = h * y * h⁻¹ →
      Matrix.SpecialLinearGroup.toGL (d4A2QvEquiv v y') =
        D * Matrix.SpecialLinearGroup.toGL (d4A2QvEquiv v y) * D⁻¹ := by
  classical
  set n : ModGL Tag.D4 Ω := canonicalRep (coxeterSystem Tag.D4) Ω v with hn
  have hnN := canonicalRep_mem_normalizer (τ := Tag.D4) (R := Ω) v
  have hh' : n⁻¹ * h * n ∈ torusGroup Tag.D4 Ω := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hnN) h).1 hh
    simpa using this
  obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh'
  have ha : ((n⁻¹ * h * n : ModGL Tag.D4 Ω) : Module.End Ω (RootModule Tag.D4 Ω))
      (rootVec Tag.D4 Ω (Pi.single 0 1)) =
        ((l 0 : Ωˣ) : Ω) • rootVec Tag.D4 Ω (Pi.single 0 1) := by
    rw [hl]
    refine (rootDiag_rootVec l (isRoot_single Tag.D4 0)).trans ?_
    rw [rootChar_single_D4]
  have hb : ((n⁻¹ * h * n : ModGL Tag.D4 Ω) : Module.End Ω (RootModule Tag.D4 Ω))
      (rootVec Tag.D4 Ω (Pi.single 2 1)) =
        ((l 2 : Ωˣ) : Ω) • rootVec Tag.D4 Ω (Pi.single 2 1) := by
    rw [hl]
    refine (rootDiag_rootVec l (isRoot_single Tag.D4 2)).trans ?_
    rw [rootChar_single_D4]
  refine ⟨diagGL ((l 0 : Ωˣ) : Ω) ((l 2 : Ωˣ) : Ω) (l 0).ne_zero (l 2).ne_zero,
    fun y y' hy' => ?_⟩
  obtain ⟨q, hq, hyq⟩ := y.2
  have hyq' : (y : ModGL Tag.D4 Ω) = n * q * n⁻¹ := hyq.symm
  have hq' : n⁻¹ * (y : ModGL Tag.D4 Ω) * n = q := by
    rw [hyq']
    group
  have hy'q : n⁻¹ * (y' : ModGL Tag.D4 Ω) * n =
      (n⁻¹ * h * n) * q * (n⁻¹ * h * n)⁻¹ := by
    rw [hy', hyq']
    group
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_d4A2QvEquiv, coe_d4A2QvEquiv, hq', hy'q]
  exact (d4A2Mat_conj_torus hh' ha hb hq).2

theorem action_of_prod_Qv (v : WeylGroup Tag.D4) {m : ModGL Tag.D4 Ω}
    (hm : m ∈ (torusGroup Tag.D4 Ω : Set (ModGL Tag.D4 Ω)) *
      (d4A2Qv Ω v : Set (ModGL Tag.D4 Ω))) :
    ∃ N : GL (Fin 3) Ω, ∀ y y' : d4A2Qv Ω v, (y' : ModGL Tag.D4 Ω) = m * y * m⁻¹ →
      Matrix.SpecialLinearGroup.toGL (d4A2QvEquiv v y') =
        N * Matrix.SpecialLinearGroup.toGL (d4A2QvEquiv v y) * N⁻¹ := by
  obtain ⟨h, hh, u, hu, rfl⟩ := hm
  obtain ⟨D, hD⟩ := torus_action_on_Qv v hh
  refine ⟨D * Matrix.SpecialLinearGroup.toGL (d4A2QvEquiv v ⟨u, hu⟩), fun y y' hy' => ?_⟩
  set y'' : d4A2Qv Ω v := ⟨u * (y : ModGL Tag.D4 Ω) * u⁻¹,
    mul_mem (mul_mem hu y.2) (inv_mem hu)⟩ with hy''
  have h1 := hD y'' y' (by rw [hy']; simp only [hy'']; group)
  have h2 : d4A2QvEquiv v y'' = d4A2QvEquiv v ⟨u, hu⟩ * d4A2QvEquiv v y *
      (d4A2QvEquiv v ⟨u, hu⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [h1, h2]
  simp only [map_mul, map_inv]
  group

end Act

end CFSG.RankThree.PartTwo.Sec4.E27
