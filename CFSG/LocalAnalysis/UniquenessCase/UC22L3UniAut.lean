module

public import CFSG.LocalAnalysis.UniquenessCase.UC22L3UniBlock
import CFSG.RankThree.PartTwo.Sec17.Item17Res7ProofL3AutUni
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherIsotropicRadical
public import Certificates.Kernel.ThCent.Leaves
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.LieType.Chevalley.LangRootArithmetic
import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
import CFSG.RankThree.PartTwo.Sec4.LThreePiSLOn
import CFSG.RankThree.PartTwo.Sec4.StatementsCensus

public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.L3Uni

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.GH74.KGroups.L3Eps
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped MatrixGroups

variable {p f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData p f F)

local notation "𝟙" => ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)

theorem field_d (σ : F ≃+* F) : primeFormFieldU h isPrimeFormGram_one σ (d h) = d h := by
  apply Subtype.ext
  rw [coe_primeFormFieldU, coe_d]
  apply Units.ext
  rw [coe_glAut, L3Lin.coe_dG, coe_dNeg]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem field_commute_e_sq (σ : F ≃+* F) :
    primeFormFieldHom h isPrimeFormGram_one σ * e h ^ 2 =
      e h ^ 2 * primeFormFieldHom h isPrimeFormGram_one σ := by
  rw [e_sq]
  have he := primeFormField_conj_eq h isPrimeFormGram_one σ (d h)
  rw [field_d] at he
  calc primeFormFieldHom h isPrimeFormGram_one σ * primeFormConjHom h 𝟙 (d h) =
      (primeFormFieldHom h isPrimeFormGram_one σ * primeFormConjHom h 𝟙 (d h) *
        (primeFormFieldHom h isPrimeFormGram_one σ)⁻¹) *
          primeFormFieldHom h isPrimeFormGram_one σ := by group
    _ = primeFormConjHom h 𝟙 (d h) * primeFormFieldHom h isPrimeFormGram_one σ := by rw [he]

theorem exists_lift_C (h5 : 5 ≤ p ^ f) (v : MulAut (primeFormP h 𝟙))
    (hv : v * e h ^ 2 = e h ^ 2 * v) :
    ∃ (A : ↥(CenU h)) (σ : F ≃+* F),
      v = (piC h A : MulAut (primeFormP h 𝟙)) * primeFormFieldHom h isPrimeFormGram_one σ := by
  obtain ⟨⟨A, σ⟩, hA⟩ := primeFormPsi_surjective h isPrimeFormGram_one (by norm_num)
    (show ¬ (3 = 3 ∧ p ^ f = 2) by omega) v
  have hAv : v = primeFormConjHom h 𝟙 A * primeFormFieldHom h isPrimeFormGram_one σ := by
    rw [← hA, primeFormPsi_apply]
  have hAc : primeFormConjHom h 𝟙 A * e h ^ 2 = e h ^ 2 * primeFormConjHom h 𝟙 A := by
    apply mul_right_cancel (b := primeFormFieldHom h isPrimeFormGram_one σ)
    calc primeFormConjHom h 𝟙 A * e h ^ 2 * primeFormFieldHom h isPrimeFormGram_one σ =
        primeFormConjHom h 𝟙 A * primeFormFieldHom h isPrimeFormGram_one σ * e h ^ 2 := by
          rw [mul_assoc, ← field_commute_e_sq, ← mul_assoc]
      _ = e h ^ 2 * primeFormConjHom h 𝟙 A * primeFormFieldHom h isPrimeFormGram_one σ := by
        rw [← hAv, hv, hAv, ← mul_assoc]
  have hc : A ∈ CenU h := by
    have he := commute_of_conjHom h (T := d h)
      (by rw [coe_d, L3Lin.trace_dG]; exact neg_ne_zero.2 one_ne_zero)
      (by simpa only [e_sq] using hAc)
    exact mem_centralizer_singleton_iff.2 (congrArg Subtype.val he)
  exact ⟨⟨A, hc⟩, σ, hAv⟩

theorem eq_one_or_bar (hf : f = 1) (σ : F ≃+* F) : σ = 1 ∨ ∀ x, σ x = h.bar x := by
  subst hf
  have hc : Nat.card F = p ^ 2 := by simpa using h.card
  rcases CFSG.RankThree.PartTwo.Sec17.Proof17Res7.ringEquiv_eq_one_or_frob h.prime hc σ with hs | hs
  · exact Or.inl hs
  · right
    intro x
    simpa only [h.bar_apply, pow_one] using hs x

theorem field_conj_Kb (hf : f = 1) (_h2 : (2 : F) ≠ 0) (hq : Odd (p ^ f))
    (σ : F ≃+* F) : ∃ j : ↥(C h), ∀ x ∈ Kb h hq,
      primeFormFieldHom h isPrimeFormGram_one σ * x *
          (primeFormFieldHom h isPrimeFormGram_one σ)⁻¹ =
        (j : MulAut (primeFormP h 𝟙)) * x * (j : MulAut (primeFormP h 𝟙))⁻¹ := by
  rcases eq_one_or_bar h hf σ with hs | hs
  · subst hs
    exact ⟨1, fun x _ => by simp only [map_one, inv_one, one_mul, mul_one, Subgroup.coe_one]⟩
  · let B : primeFormUnitary h (1 : Matrix (Fin 2) (Fin 2) F) :=
      ⟨Uni.jU h, by
        rw [mem_primeFormUnitary, Matrix.mul_one]
        exact ((mem_unitarySU_iff h).1 (Uni.jU h).2).2⟩
    refine ⟨blockC h B, ?_⟩
    rintro _ ⟨y, ⟨Y, hY⟩, rfl⟩
    let Yu : primeFormUnitary h (1 : Matrix (Fin 2) (Fin 2) F) :=
      ⟨Y, by
        rw [mem_primeFormUnitary, Matrix.mul_one]
        exact ((mem_unitarySU_iff h).1 Y.2).2⟩
    have hxy : MulAut.conj y = primeFormConjHom h 𝟙 (blockU h Yu) := by
      have hc : blockU h Yu =
          ⟨suEquiv h (Uni.levU hq.pos Y), (suEquiv h (Uni.levU hq.pos Y)).2.1⟩ := Subtype.ext rfl
      rw [hc, primeFormConjHom_eq_conj]
      change MulAut.conj y = MulAut.conj (proj h (Uni.levU hq.pos Y))
      change proj h (Uni.levU hq.pos Y) = y at hY
      rw [hY]
    rw [hxy, primeFormField_conj_eq]
    change primeFormConjHom h 𝟙 _ = primeFormConjHom h 𝟙 (blockU h B) *
      primeFormConjHom h 𝟙 _ * (primeFormConjHom h 𝟙 (blockU h B))⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change glAut σ (CFSG.RankThree.SubgroupLists.blockGL3 (Y : GL (Fin 2) F)) =
      Uni.jGL h * CFSG.RankThree.SubgroupLists.blockGL3 (Y : GL (Fin 2) F) * (Uni.jGL h)⁻¹
    have he := Uni.glAut_blockGL3_mul_jGL h hs Y
    calc glAut σ (CFSG.RankThree.SubgroupLists.blockGL3 (Y : GL (Fin 2) F)) =
        (glAut σ (CFSG.RankThree.SubgroupLists.blockGL3 (Y : GL (Fin 2) F)) * Uni.jGL h) *
          (Uni.jGL h)⁻¹ := by group
      _ = _ := by rw [he]

theorem exists_conj_Kb (hf : f = 1) (h2 : (2 : F) ≠ 0) (hq : Odd (p ^ f)) (h5 : 5 ≤ p ^ f)
    (v : MulAut (primeFormP h 𝟙)) (hv : v * e h ^ 2 = e h ^ 2 * v) :
    ∃ g ∈ C h, ∀ x ∈ Kb h hq, v * x * v⁻¹ = g * x * g⁻¹ := by
  obtain ⟨A, σ, rfl⟩ := exists_lift_C h h5 v hv
  obtain ⟨j, hj⟩ := field_conj_Kb h hf h2 hq σ
  refine ⟨(piC h A : MulAut (primeFormP h 𝟙)) * j, (C h).mul_mem (piC h A).2 j.2, ?_⟩
  intro x hx
  calc ((piC h A : MulAut (primeFormP h 𝟙)) * primeFormFieldHom h isPrimeFormGram_one σ) * x *
      ((piC h A : MulAut (primeFormP h 𝟙)) * primeFormFieldHom h isPrimeFormGram_one σ)⁻¹ =
        (piC h A : MulAut (primeFormP h 𝟙)) *
          (primeFormFieldHom h isPrimeFormGram_one σ * x *
            (primeFormFieldHom h isPrimeFormGram_one σ)⁻¹) * (piC h A : MulAut (primeFormP h 𝟙))⁻¹ := by group
    _ = _ := by rw [hj x hx]; group

theorem conj_mem_Kb (hf : f = 1) (h2 : (2 : F) ≠ 0) (hq : Odd (p ^ f)) (h5 : 5 ≤ p ^ f)
    (v : MulAut (primeFormP h 𝟙)) (hv : v * e h ^ 2 = e h ^ 2 * v)
    (x : MulAut (primeFormP h 𝟙)) (hx : x ∈ Kb h hq) : v * x * v⁻¹ ∈ Kb h hq := by
  obtain ⟨g, hg, hact⟩ := exists_conj_Kb h hf h2 hq h5 v hv
  rw [hact x hx]
  let gc : ↥(C h) := ⟨g, hg⟩
  let xc : ↥(C h) := ⟨x, Kb_le h hq hx⟩
  have hxu : psi h h2 xc ∈ unitarySU p f F 2 := (psi_Kb h h2 hq xc).1 hx
  apply (psi_Kb h h2 hq (gc * xc * gc⁻¹)).2
  rw [map_mul, map_mul, map_inv, unitarySU_eq_gramSU h 2]
  exact conj_mem_gramSU h (1 : Matrix (Fin 2) (Fin 2) F) (psi_unitary h h2 gc)
    ((unitarySU_eq_gramSU h 2) ▸ hxu)

end CFSG.LocalAnalysis.UniquenessCase.UC22.L3Uni
