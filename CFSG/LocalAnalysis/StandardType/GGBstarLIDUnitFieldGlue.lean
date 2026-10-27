module

public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryDvdField
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDUnitFieldIso

public section

namespace CFSG.StandardType

namespace LIDUF

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher InndiagSU TableBUI TableBUD
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.SectionRank.OddCover (diagHom coe_diagHom diagHom_injective det_diagHom)

variable {K : Type} [Field K] {d n : ℕ}

theorem adjM_mul_self_of_mem {h : UnitaryFieldData 2 n K} {g : GL (Fin d) K}
    (hg : g ∈ primeFormUnitary h (idGram K d)) :
    adjM h.bar (g : Matrix (Fin d) (Fin d) K) * (g : Matrix (Fin d) (Fin d) K) = 1 := by
  have h1 := mem_primeFormUnitary.mp hg
  simpa [adjM, idGram, Units.val_one, Matrix.mul_one] using h1

theorem coe_glAut_eq_map (φ : K ≃+* K) (g : GL (Fin d) K) :
    ((glAut φ g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      (g : Matrix (Fin d) (Fin d) K).map φ := by
  ext i j
  rfl

theorem exists_fixed_involution (h : UnitaryFieldData 2 n K) [Finite K] [CharP K 2] {r : ℕ}
    (Q : GL (Fin d) K) (hQ : Q ∈ primeFormUnitary h (idGram K d))
    (U : Matrix (Fin d) (Fin r) K) (hU : adjM h.bar U * U = 0)
    (hns : tvGL h.bar hU ∉ LargeEvenScalars (Fin d) K)
    {Eb : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))}
    (hEb : ∀ e ∈ Eb, ∃ σ : Fin d → Kˣ, (∀ k, ((σ k : Kˣ) : K) ^ (2 ^ n + 1) = 1) ∧
      FrameAct h Q hQ e σ ∧
        tv h.bar (Matrix.diagonal (fun k => ((σ k : Kˣ) : K)) * U) = tv h.bar U)
    {f : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))}
    {B' : GL (Fin d) K} (hB' : B' ∈ primeFormUnitary h (idGram K d)) {φ : K ≃+* K}
    (hsl : IsSemilin (frameMk h Q hQ) f B' φ) (hφb : ∀ x, φ (h.bar x) = h.bar (φ x))
    (hP : tv h.bar ((B' : Matrix (Fin d) (Fin d) K) * U.map φ) = tv h.bar U) :
    ∃ m : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)), m ≠ 1 ∧ m ^ 2 = 1 ∧
      (∀ e ∈ Eb, e m = m) ∧ f m = m := by
  classical
  have hb := h.bar_bar
  set M : ↥(unitarySU 2 n K d) := ⟨tvGL h.bar hU, tvGL_mem_unitarySU h hU⟩ with hM
  have hMcoe : ((M : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = tv h.bar U := rfl
  refine ⟨frameMk h Q hQ M, ?_, ?_, ?_, ?_⟩
  · intro h1
    have h2 : frameMk h Q hQ 1 = frameMk h Q hQ M := by rw [map_one, h1]
    obtain ⟨a, ha⟩ := exists_scalar_of_frameMk_eq h Q hQ h2
    apply hns
    refine ⟨a, ?_⟩
    have ha' : tvGL h.bar hU = Matrix.GeneralLinearGroup.scalar (Fin d) a * 1 := ha
    rw [ha', mul_one]
  · have hM2 : M ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, sq]
      exact tvGL_mul_self h.bar hU)
    rw [← map_pow, hM2, map_one]
  · intro e he
    obtain ⟨σ, hσn, hfr, hDU⟩ := hEb e he
    refine hfr.apply M M ?_
    have hD := diagHom_mem_primeFormUnitary h hσn
    have hDu := adjM_mul_self_of_mem hD
    have key := tv_conj h.bar hb hDu U
    have hDU' : tv h.bar (((diagHom d σ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * U) =
        tv h.bar U := by
      rw [coe_diagHom]
      exact hDU
    rw [hDU'] at key
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact key.symm
  · refine hsl M M ?_
    have hBu := adjM_mul_self_of_mem hB'
    have key := tv_conj h.bar hb hBu (U.map φ)
    rw [hP] at key
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_glAut_eq_map, hMcoe]
    have := tv_map h.bar (φ : K →+* K) hφb U
    rw [show (U.map φ) = U.map (φ : K →+* K) from rfl] at key
    rw [show ((tv h.bar U).map φ) = (tv h.bar U).map (φ : K →+* K) from rfl, this]
    exact key.symm

end LIDUF

end CFSG.StandardType

end
