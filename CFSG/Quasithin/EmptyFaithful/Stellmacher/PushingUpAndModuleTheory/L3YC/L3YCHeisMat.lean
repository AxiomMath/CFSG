module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCHeis
public import CFSG.Quasithin.Background.C48PfFourModPfGrp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open Matrix CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin.C48Pf.FMod

namespace Stellmacher.PU.L3YC

@[expose] def heisMat (h : Heis) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, h.x 0, h.x 1, h.x 2, h.w;
     0, 1, 0, 0, h.y 0;
     0, 0, 1, 0, h.y 1;
     0, 0, 0, 1, h.y 2;
     0, 0, 0, 0, 1]

theorem heisMat_mul (a b : Heis) : heisMat a * heisMat b = heisMat (a * b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heisMat, Matrix.mul_apply, Fin.sum_univ_five, dotProduct, Fin.sum_univ_three] <;> ring

theorem heisMat_one : heisMat 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heisMat]

theorem det_heisMat (h : Heis) : (heisMat h).det = 1 := by
  have h1 : (heisMat h).det * (heisMat h⁻¹).det = 1 := by
    rw [← Matrix.det_mul, heisMat_mul, mul_inv_cancel, heisMat_one, Matrix.det_one]
  have hne : (heisMat h).det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  generalize (heisMat h).det = t at hne ⊢
  revert t
  decide

@[expose] noncomputable def heisHom : Heis →* SpecialLinearGroup (Fin 5) (ZMod 2) where
  toFun h := ⟨heisMat h, det_heisMat h⟩
  map_one' := Subtype.ext heisMat_one
  map_mul' a b := Subtype.ext (heisMat_mul a b).symm

theorem heisHom_coe (h : Heis) :
    ((heisHom h : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
      heisMat h := rfl

theorem heisHom_injective : Function.Injective heisHom := by
  intro a b hab
  have h := congrArg (fun g : SpecialLinearGroup (Fin 5) (ZMod 2) =>
    (g : Matrix (Fin 5) (Fin 5) (ZMod 2))) hab
  simp only [heisHom_coe] at h
  have e : ∀ i j, heisMat a i j = heisMat b i j := fun i j => congrFun (congrFun h i) j
  ext i
  · fin_cases i
    · simpa [heisMat] using e 0 1
    · simpa [heisMat] using e 0 2
    · simpa [heisMat] using e 0 3
  · fin_cases i
    · simpa [heisMat] using e 1 4
    · simpa [heisMat] using e 2 4
    · simpa [heisMat] using e 3 4
  · simpa [heisMat] using e 0 4

theorem eq_heisMat_of_blockForm {A : Matrix (Fin 5) (Fin 5) (ZMod 2)} (hA : BlockForm 1 3 A)
    (hb : blkAt 1 3 (by norm_num) A = 1) : ∃ h : Heis, A = heisMat h := by
  obtain ⟨hA1, hA2, hA3, hA4⟩ := hA
  have hm : ∀ i j : Fin 3, A ⟨1 + (i : ℕ), by omega⟩ ⟨1 + (j : ℕ), by omega⟩ =
      (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j := fun i j => by
    have := congrFun (congrFun hb i) j
    simpa [blkAt_apply] using this
  refine ⟨⟨![A 0 1, A 0 2, A 0 3], ![A 1 4, A 2 4, A 3 4], A 0 4⟩, ?_⟩
  have h00 : A 0 0 = 1 := by simpa using hA3 0 0 (by decide) (by decide)
  have h44 : A 4 4 = 1 := by simpa using hA4 4 4 (by decide) (by decide)
  have h10 : A 1 0 = 0 := hA1 1 0 (by decide) (by decide)
  have h20 : A 2 0 = 0 := hA1 2 0 (by decide) (by decide)
  have h30 : A 3 0 = 0 := hA1 3 0 (by decide) (by decide)
  have h40 : A 4 0 = 0 := hA1 4 0 (by decide) (by decide)
  have h41 : A 4 1 = 0 := hA2 4 1 (by decide) (by decide)
  have h42 : A 4 2 = 0 := hA2 4 2 (by decide) (by decide)
  have h43 : A 4 3 = 0 := hA2 4 3 (by decide) (by decide)
  have h11 := hm 0 0
  have h12 := hm 0 1
  have h13 := hm 0 2
  have h21 := hm 1 0
  have h22 := hm 1 1
  have h23 := hm 1 2
  have h31 := hm 2 0
  have h32 := hm 2 1
  have h33 := hm 2 2
  simp at h11 h12 h13 h21 h22 h23 h31 h32 h33
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heisMat, *]

end Stellmacher.PU.L3YC

end CFSG.Quasithin
