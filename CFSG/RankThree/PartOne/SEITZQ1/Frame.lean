module

public import CFSG.RankThree.PartOne.KF4.LongA2Frame
public import CFSG.RankThree.PartOne.KLR.TwistPerm

public noncomputable section

namespace CFSG.RankThree.PartOne.SEITZQ1

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KLR
open CFSG.RankThree.E6 (chainRoot)

open scoped MatrixGroups

variable {L : Type} [Field L]

section Standard

theorem f4Long_Mat_chain_charTwo [CharP L 2] (i j : Fin 3) (hij : i ≠ j) (t : L) :
    f4Long_data.Mat (pinnedX Tag.F4 L (chainRoot f4chainLong i j) t) = 1 + single i j t := by
  obtain ⟨c01, c12, c10, c21⟩ := f4chainLong_values
  have hn : weylElt Tag.F4 L (f4Index 0) 1 ∈ subsystemGroup Tag.F4 L f4LongSupport :=
    weylElt_mem_subsystemGroup ((mem_f4LongSupport _).2 (Or.inl rfl)) 1
  match i, j, hij with
  | 0, 0, h => exact absurd rfl h
  | 0, 1, _ => rw [c01, pinnedX_single, f4Long_Mat_x1]
  | 1, 2, _ => rw [c12, pinnedX_single, f4Long_Mat_x2]
  | 1, 0, _ => rw [c10, pinnedX_neg_single, f4Long_Mat_y1]
  | 2, 1, _ => rw [c21, pinnedX_neg_single, f4Long_Mat_y2]
  | 1, 1, h => exact absurd rfl h
  | 2, 2, h => exact absurd rfl h
  | 0, 2, _ =>
    obtain ⟨ε, hεε, h⟩ := weylElt_mul_pinnedX_mul_inv L (f4Index 0)
      (isRoot_single Tag.F4 (f4Index 1))
    have hε : ε = 1 := eq_one_of_mul_self_eq_one_charTwo hεε
    have hr : reflect Tag.F4 (f4Index 0) (Pi.single (f4Index 1) 1) =
        chainRoot f4chainLong 0 2 := by
      decide +kernel
    rw [hr, hε] at h
    have hα : Pi.single (f4Index 1) 1 ∈ parabolicRoots Tag.F4 f4LongSupport := by
      have := f4chainLong_mem_parabolicRoots (k := 1) (l := 2) (by decide)
      rwa [f4chainLong_values.2.1] at this
    have e : pinnedX Tag.F4 L (chainRoot f4chainLong 0 2) t =
        weylElt Tag.F4 L (f4Index 0) 1 * pinnedX Tag.F4 L (Pi.single (f4Index 1) 1) t *
          (weylElt Tag.F4 L (f4Index 0) 1)⁻¹ := by
      rw [h, one_mul]
    have hX := pinnedX_mem_f4Long hα t
    rw [e, f4Long_data.Mat_mul (mul_mem hn hX) (inv_mem hn), f4Long_data.Mat_mul hn hX,
      f4Long_Mat_n1, f4Long_Mat_n1_inv, pinnedX_single, f4Long_Mat_x2]
    exact f4LongN_conj_12 _
  | 2, 0, _ =>
    obtain ⟨ε, hεε, h⟩ := weylElt_mul_pinnedX_mul_inv L (f4Index 0)
      (isRoot_neg_single Tag.F4 (f4Index 1))
    have hε : ε = 1 := eq_one_of_mul_self_eq_one_charTwo hεε
    have hr : reflect Tag.F4 (f4Index 0) (-Pi.single (f4Index 1) 1) =
        chainRoot f4chainLong 2 0 := by
      decide +kernel
    rw [hr, hε] at h
    have hα : -Pi.single (f4Index 1) 1 ∈ parabolicRoots Tag.F4 f4LongSupport := by
      have := f4chainLong_mem_parabolicRoots (k := 2) (l := 1) (by decide)
      rwa [f4chainLong_values.2.2.2] at this
    have e : pinnedX Tag.F4 L (chainRoot f4chainLong 2 0) t =
        weylElt Tag.F4 L (f4Index 0) 1 * pinnedX Tag.F4 L (-Pi.single (f4Index 1) 1) t *
          (weylElt Tag.F4 L (f4Index 0) 1)⁻¹ := by
      rw [h, one_mul]
    have hX := pinnedX_mem_f4Long hα t
    rw [e, f4Long_data.Mat_mul (mul_mem hn hX) (inv_mem hn), f4Long_data.Mat_mul hn hX,
      f4Long_Mat_n1, f4Long_Mat_n1_inv, pinnedX_neg_single, f4Long_Mat_y2]
    exact f4LongN_conj_21 _

theorem f4rhoLong_transvection_charTwo [CharP L 2] (i j : Fin 3) (hij : i ≠ j) (t : L) :
    f4rhoLong L (Matrix.SpecialLinearGroup.transvection hij t) =
      pinnedX Tag.F4 L (chainRoot f4chainLong i j) t := by
  have hmem := pinnedX_mem_f4Long (K := L) (f4chainLong_mem_parabolicRoots hij) t
  have hrep : f4LongRep L ⟨pinnedX Tag.F4 L (chainRoot f4chainLong i j) t, hmem⟩ =
      Matrix.SpecialLinearGroup.transvection hij t := by
    apply Subtype.ext
    rw [coe_f4LongRep, f4Long_Mat_chain_charTwo i j hij, CFSG.LinearGroups.coe_transvection]
  rw [← hrep]
  exact f4rhoLong_f4LongRep hmem

end Standard

section Transported

@[expose] def f4rhoLongR (L : Type) [Field L] : SL(3, L) →* ModGL ReeTag.F4.tag L :=
  f4rhoLong L

@[expose] def chainRootR (i j : Fin 3) : Fin ReeTag.F4.tag.rank → ℤ :=
  chainRoot f4chainLong i j

theorem isRoot_chainRootR {i j : Fin 3} (hij : i ≠ j) : IsRoot ReeTag.F4.tag (chainRootR i j) :=
  (f4chainLong_mem_parabolicRoots hij).1

theorem f4rhoLongR_transvection [CharP L 2] (i j : Fin 3) (hij : i ≠ j) (t : L) :
    f4rhoLongR L (Matrix.SpecialLinearGroup.transvection hij t) =
      pinnedX ReeTag.F4.tag L (chainRootR i j) t :=
  f4rhoLong_transvection_charTwo i j hij t

theorem f4rhoLongR_injective : Function.Injective (f4rhoLongR L) :=
  f4rhoLong_injective

@[expose] def q1U : WeylGroup ReeTag.F4.tag :=
  (coxeterSystem ReeTag.F4.tag).wordProd [0, 2, 1, 3, 2]

@[expose] def q1Sig (i j : Fin 3) : Fin ReeTag.F4.tag.rank → ℤ :=
  q1U • chainRootR i j

theorem isRoot_q1Sig {i j : Fin 3} (hij : i ≠ j) : IsRoot ReeTag.F4.tag (q1Sig i j) :=
  IsRoot.smul (isRoot_chainRootR hij) q1U

theorem q1Sig_values : q1Sig 0 1 = ![0, 1, 2, 0] ∧ q1Sig 1 2 = ![1, 1, 2, 2] ∧
    q1Sig 0 2 = ![1, 2, 4, 2] ∧ q1Sig 1 0 = ![0, -1, -2, 0] ∧ q1Sig 2 1 = ![-1, -1, -2, -2] ∧
    q1Sig 2 0 = ![-1, -2, -4, -2] := by
  have h : ∀ i j : Fin 3, q1Sig i j = CFSG.RankThree.Lattice.wordMat Tag.F4 [0, 2, 1, 3, 2] *ᵥ
      chainRoot f4chainLong i j := fun i j =>
    CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec Tag.F4 _ _
  simp only [h]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (funext k; fin_cases k <;> decide +kernel)

@[expose] def q1Rho (L : Type) [Field L] : SL(3, L) →* ModGL ReeTag.F4.tag L :=
  (MulAut.conj (canonicalRep (coxeterSystem ReeTag.F4.tag) L q1U)).toMonoidHom.comp (f4rhoLongR L)

theorem q1Rho_transvection [CharP L 2] (i j : Fin 3) (hij : i ≠ j) (t : L) :
    q1Rho L (Matrix.SpecialLinearGroup.transvection hij t) =
      pinnedX ReeTag.F4.tag L (q1Sig i j) t := by
  show canonicalRep (coxeterSystem ReeTag.F4.tag) L q1U *
      f4rhoLongR L (Matrix.SpecialLinearGroup.transvection hij t) *
      (canonicalRep (coxeterSystem ReeTag.F4.tag) L q1U)⁻¹ = _
  rw [f4rhoLongR_transvection i j hij t]
  exact canonicalRep_conj_pinnedX q1U (isRoot_chainRootR hij) t

theorem q1Rho_injective : Function.Injective (q1Rho L) :=
  (MulAut.conj _).injective.comp f4rhoLongR_injective

end Transported

end CFSG.RankThree.PartOne.SEITZQ1
