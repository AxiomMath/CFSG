module

public import CFSG.RankThree.PartOne.KF4.LongA2Native
public import CFSG.RankThree.PartOne.KF4.A2Frame

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
open CFSG.RankThree.E6 (chainRoot)
open scoped MatrixGroups

section Standard

variable
  (L : Type) [Field L]

theorem f4LongRep_bijective : Function.Bijective (f4LongRep L) :=
  ⟨f4LongRep_injective, f4LongRep_surjective⟩

@[expose] def f4LongEquiv : SL(3, L) ≃* subsystemGroup Tag.F4 L f4LongSupport :=
  (MulEquiv.ofBijective (f4LongRep L) (f4LongRep_bijective L)).symm

@[expose] def f4rhoLong : SL(3, L) →* ModGL Tag.F4 L :=
  (subsystemGroup Tag.F4 L f4LongSupport).subtype.comp (f4LongEquiv L).toMonoidHom

variable {L}

theorem f4LongRep_f4LongEquiv (X : SL(3, L)) : f4LongRep L (f4LongEquiv L X) = X :=
  (MulEquiv.ofBijective (f4LongRep L) (f4LongRep_bijective L)).apply_symm_apply X

theorem f4rhoLong_f4LongRep {g : ModGL Tag.F4 L} (hg : g ∈ subsystemGroup Tag.F4 L f4LongSupport) :
    f4rhoLong L (f4LongRep L ⟨g, hg⟩) = g := by
  have h := (MulEquiv.ofBijective (f4LongRep L) (f4LongRep_bijective L)).symm_apply_apply
    (⟨g, hg⟩ : subsystemGroup Tag.F4 L f4LongSupport)
  exact congrArg Subtype.val h

theorem f4rhoLong_mem (X : SL(3, L)) : f4rhoLong L X ∈ subsystemGroup Tag.F4 L f4LongSupport :=
  (f4LongEquiv L X).2

theorem Mat_f4rhoLong (X : SL(3, L)) :
    f4Long_data.Mat (f4rhoLong L X) = (X : Matrix (Fin 3) (Fin 3) L) :=
  congrArg (fun Y : SL(3, L) => (Y : Matrix (Fin 3) (Fin 3) L)) (f4LongRep_f4LongEquiv X)

theorem f4rhoLong_injective : Function.Injective (f4rhoLong L) := by
  intro X Y h
  apply Subtype.ext
  rw [← Mat_f4rhoLong X, ← Mat_f4rhoLong Y, h]

theorem f4rhoLong_range : (f4rhoLong L).range = subsystemGroup Tag.F4 L f4LongSupport := by
  refine le_antisymm (fun g ⟨X, hX⟩ => hX ▸ f4rhoLong_mem X) fun g hg => ?_
  exact ⟨f4LongRep L ⟨g, hg⟩, f4rhoLong_f4LongRep hg⟩

theorem f4rhoLong_transvection (i j : Fin 3) (hij : i ≠ j) :
    ∃ ε : Lˣ, ∀ t : L, f4rhoLong L (Matrix.SpecialLinearGroup.transvection hij t) =
      pinnedX Tag.F4 L (chainRoot f4chainLong i j) ((ε : L) * t) := by
  obtain ⟨ε, hε⟩ := f4LongRootFamily_all (K := L) i j hij
  refine ⟨ε⁻¹, fun s => ?_⟩
  have hmem := pinnedX_mem_f4Long (K := L) (f4chainLong_mem_parabolicRoots hij)
    (((ε⁻¹ : Lˣ) : L) * s)
  have hrep : f4LongRep L ⟨pinnedX Tag.F4 L (chainRoot f4chainLong i j) (((ε⁻¹ : Lˣ) : L) * s),
      hmem⟩ = Matrix.SpecialLinearGroup.transvection hij s := by
    apply Subtype.ext
    rw [coe_f4LongRep, hε, CFSG.LinearGroups.coe_transvection]
    congr 2
    rw [← mul_assoc, Units.mul_inv, one_mul]
  rw [← hrep]
  exact f4rhoLong_f4LongRep hmem

theorem f4rhoLong_diag (A : SL(3, L))
    (hA : ∀ i j : Fin 3, i ≠ j → (A : Matrix (Fin 3) (Fin 3) L) i j = 0) :
    f4rhoLong L A ∈ torusGroup Tag.F4 L := by
  have hdiag : (A : Matrix (Fin 3) (Fin 3) L) =
      Matrix.diagonal fun i => (A : Matrix (Fin 3) (Fin 3) L) i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hA i j hij, Matrix.diagonal_apply_ne _ hij]
  have hdet : (A : Matrix (Fin 3) (Fin 3) L).det = 1 := A.2
  rw [hdiag, Matrix.det_diagonal, Fin.prod_univ_three] at hdet
  have h0 : (A : Matrix (Fin 3) (Fin 3) L) 0 0 ≠ 0 := fun h => by
    rw [h, zero_mul, zero_mul] at hdet
    exact zero_ne_one hdet
  have h01 : (A : Matrix (Fin 3) (Fin 3) L) 0 0 * (A : Matrix (Fin 3) (Fin 3) L) 1 1 ≠ 0 :=
    fun h => by
      rw [h, zero_mul] at hdet
      exact zero_ne_one hdet
  set ua : Lˣ := Units.mk0 _ h0 with hua
  set ub : Lˣ := Units.mk0 _ h01 with hub
  have hrep : f4LongRep L ⟨torus2Elt (f4Index 0) (f4Index 1) ua ub,
      torus2Elt_mem_f4Long ua ub⟩ = A := by
    apply Subtype.ext
    rw [coe_f4LongRep, f4Long_Mat_torus, hdiag]
    have h22 : (A : Matrix (Fin 3) (Fin 3) L) 2 2 =
        ((A : Matrix (Fin 3) (Fin 3) L) 0 0 * (A : Matrix (Fin 3) (Fin 3) L) 1 1)⁻¹ :=
      eq_inv_of_mul_eq_one_right hdet
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hua, hub, Matrix.diagonal_apply_ne]
    rw [h22, _root_.mul_inv_rev]
  have hJ : f4rhoLong L A = torus2Elt (f4Index 0) (f4Index 1) ua ub := by
    rw [← hrep]
    exact f4rhoLong_f4LongRep (torus2Elt_mem_f4Long ua ub)
  rw [hJ]
  have hmem : torus2Elt (f4Index 0) (f4Index 1) ua ub ∈
      subsystemGroup Tag.F4 L f4LongSupport ⊓ torusGroup Tag.F4 L := by
    rw [subsystemGroup_inf_torusGroup (τ := Tag.F4) (K := L) (A := f4LongSupport)]
    exact mem_subsystemTorus_f4Long.2 ⟨ua, ub, rfl⟩
  exact hmem.2

theorem f4Long_frame :
    IsA2Frame (f4rhoLong L) (fun i j => chainRoot f4chainLong i j) where
  injective := f4rhoLong_injective
  isRoot i j hij := (f4chainLong_mem_parabolicRoots hij).1
  neg i j := f4chainLong_neg i j
  add i j k := f4chainLong_add i j k
  transv i j hij := f4rhoLong_transvection i j hij
  range := by
    rw [f4rhoLong_range, subsystemGroup_eq_rootSpan]
    congr 1
    ext r
    constructor
    · intro hr
      obtain ⟨k, l, hkl, rfl⟩ := exists_f4chainLong_of_mem hr
      exact ⟨k, l, hkl, rfl⟩
    · rintro ⟨i, j, hij, rfl⟩
      exact f4chainLong_mem_parabolicRoots hij
  diag A hA := f4rhoLong_diag A hA

end Standard

end CFSG.RankThree.PartOne.KF4
