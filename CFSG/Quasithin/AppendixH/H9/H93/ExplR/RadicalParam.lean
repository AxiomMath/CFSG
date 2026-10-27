module

public import CFSG.Quasithin.AppendixH.H9.H93.ExplicitDefs
public import CFSG.Quasithin.AppendixH.H9.ModelBasic

public section

namespace CFSG.ASVolI.ChH

open scoped Matrix
open CFSG.Quasithin CFSG.Open

@[expose] def Nmat (ε : Fin 4 → ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, ε 0, ε 1; 0, 0, ε 2, ε 3; 0, 0, 0, 0; 0, 0, 0, 0]

theorem Nmat_mul_Nmat (ε ε' : Fin 4 → ZMod 2) : Nmat ε * Nmat ε' = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Nmat, Matrix.mul_apply, Fin.sum_univ_four]

theorem Nmat_add (ε ε' : Fin 4 → ZMod 2) : Nmat (ε + ε') = Nmat ε + Nmat ε' := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Nmat]

theorem Nmat_zero : Nmat 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Nmat]

theorem one_add_Nmat_mul (ε ε' : Fin 4 → ZMod 2) :
    (1 + Nmat ε) * (1 + Nmat ε') = 1 + Nmat (ε + ε') := by
  calc (1 + Nmat ε) * (1 + Nmat ε')
      = 1 + Nmat ε + Nmat ε' + Nmat ε * Nmat ε' := by noncomm_ring
    _ = 1 + Nmat (ε + ε') := by rw [Nmat_mul_Nmat, add_zero, Nmat_add, add_assoc]

private theorem add_self_fin4 (ε : Fin 4 → ZMod 2) : ε + ε = 0 := by
  funext i
  simpa using CharTwo.add_self_eq_zero (ε i)

theorem one_add_Nmat_sq (ε : Fin 4 → ZMod 2) : (1 + Nmat ε) * (1 + Nmat ε) = 1 := by
  rw [one_add_Nmat_mul, add_self_fin4, Nmat_zero, add_zero]

@[expose] def radicalGL (ε : Fin 4 → ZMod 2) : GL (Fin 4) (ZMod 2) :=
  invGL4 (1 + Nmat ε) (one_add_Nmat_sq ε)

theorem radicalGL_val (ε : Fin 4 → ZMod 2) :
    ((radicalGL ε : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1 + Nmat ε := rfl

theorem dualGLn_radicalGL_val (ε : Fin 4 → ZMod 2) :
    ((dualGLn 4 (radicalGL ε) : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      (1 + Nmat ε)ᵀ := rfl

@[expose] def radicalGLHom : Multiplicative (Fin 4 → ZMod 2) →* GL (Fin 4) (ZMod 2) :=
  MonoidHom.mk' (fun x => radicalGL (Multiplicative.toAdd x)) fun x y => Units.ext (by
    show 1 + Nmat (Multiplicative.toAdd (x * y)) =
      (1 + Nmat (Multiplicative.toAdd x)) * (1 + Nmat (Multiplicative.toAdd y))
    rw [toAdd_mul, one_add_Nmat_mul])

@[expose] noncomputable def radicalHom : Multiplicative (Fin 4 → ZMod 2) →* MulAut (PairN 4) :=
  (pairActN 4).comp radicalGLHom

theorem radicalHom_ofAdd (ε : Fin 4 → ZMod 2) :
    radicalHom (Multiplicative.ofAdd ε) = pairActN 4 (radicalGL ε) := rfl

theorem radicalHom_pairVec (ε a b : Fin 4 → ZMod 2) :
    radicalHom (Multiplicative.ofAdd ε) (pairVec a b) = pairVec (Rfst ε a b) (Rsnd ε a b) := by
  rw [radicalHom_ofAdd, pairActN_pairVec, pairVec_inj]
  constructor
  · funext i
    fin_cases i <;>
      simp [radicalGL_val, Nmat, Rfst, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.one_apply]
  · funext i
    fin_cases i <;>
      simp [dualGLn_radicalGL_val, Nmat, Rsnd, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
        Matrix.one_apply, Matrix.transpose_apply] <;> ring

theorem radicalGL_injective : Function.Injective radicalGL := by
  intro ε ε' h
  have h1 : (1 + Nmat ε : Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1 + Nmat ε' := congrArg Units.val h
  have h2 : Nmat ε = Nmat ε' := add_left_cancel h1
  funext i
  fin_cases i
  · simpa [Nmat] using congrFun (congrFun h2 0) 2
  · simpa [Nmat] using congrFun (congrFun h2 0) 3
  · simpa [Nmat] using congrFun (congrFun h2 1) 2
  · simpa [Nmat] using congrFun (congrFun h2 1) 3

theorem radicalGLHom_injective : Function.Injective radicalGLHom :=
  fun _ _ h => Multiplicative.toAdd.injective (radicalGL_injective h)

theorem radicalHom_injective : Function.Injective radicalHom :=
  pairActN_injective.comp radicalGLHom_injective

theorem radicalGL_single_zero : radicalGL (Pi.single 0 1) = gT02 := Units.ext (by decide)
theorem radicalGL_single_one : radicalGL (Pi.single 1 1) = gT03 := Units.ext (by decide)
theorem radicalGL_single_two : radicalGL (Pi.single 2 1) = gT12 := Units.ext (by decide)
theorem radicalGL_single_three : radicalGL (Pi.single 3 1) = gT13 := Units.ext (by decide)

theorem pairActN_gT02_mem_Rg4 : pairActN 4 gT02 ∈ Rg4 :=
  Subgroup.subset_closure (by simp)

theorem pairActN_gT03_mem_Rg4 : pairActN 4 gT03 ∈ Rg4 :=
  Subgroup.subset_closure (by simp)

theorem pairActN_gT12_mem_Rg4 : pairActN 4 gT12 ∈ Rg4 :=
  Subgroup.subset_closure (by simp)

theorem pairActN_gT13_mem_Rg4 : pairActN 4 gT13 ∈ Rg4 :=
  Subgroup.subset_closure (by simp)

private theorem ofAdd_decomp (ε : Fin 4 → ZMod 2) :
    Multiplicative.ofAdd ε =
      Multiplicative.ofAdd (Pi.single 0 (ε 0) : Fin 4 → ZMod 2) *
        Multiplicative.ofAdd (Pi.single 1 (ε 1) : Fin 4 → ZMod 2) *
        Multiplicative.ofAdd (Pi.single 2 (ε 2) : Fin 4 → ZMod 2) *
        Multiplicative.ofAdd (Pi.single 3 (ε 3) : Fin 4 → ZMod 2) := by
  apply Multiplicative.toAdd.injective
  simp only [toAdd_mul, toAdd_ofAdd]
  funext i
  fin_cases i <;> simp [Pi.single_apply]

private theorem radicalHom_single_mem (i : Fin 4)
    (hi : radicalHom (Multiplicative.ofAdd (Pi.single i 1 : Fin 4 → ZMod 2)) ∈ Rg4)
    (c : ZMod 2) : radicalHom (Multiplicative.ofAdd (Pi.single i c : Fin 4 → ZMod 2)) ∈ Rg4 := by
  have hc : c = 0 ∨ c = 1 := by revert c; decide
  rcases hc with rfl | rfl
  · simp [Pi.single_zero, Rg4.one_mem]
  · exact hi

theorem radicalHom_mem_Rg4 (ε : Fin 4 → ZMod 2) : radicalHom (Multiplicative.ofAdd ε) ∈ Rg4 := by
  rw [ofAdd_decomp ε, map_mul, map_mul, map_mul]
  exact Rg4.mul_mem (Rg4.mul_mem (Rg4.mul_mem
    (radicalHom_single_mem 0 (by rw [radicalHom_ofAdd, radicalGL_single_zero]; exact pairActN_gT02_mem_Rg4) _)
    (radicalHom_single_mem 1 (by rw [radicalHom_ofAdd, radicalGL_single_one]; exact pairActN_gT03_mem_Rg4) _))
    (radicalHom_single_mem 2 (by rw [radicalHom_ofAdd, radicalGL_single_two]; exact pairActN_gT12_mem_Rg4) _))
    (radicalHom_single_mem 3 (by rw [radicalHom_ofAdd, radicalGL_single_three]; exact pairActN_gT13_mem_Rg4) _)

theorem radicalHom_range : radicalHom.range = Rg4 := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    obtain ⟨ε, rfl⟩ := Multiplicative.ofAdd.surjective x
    exact radicalHom_mem_Rg4 ε
  · refine (Subgroup.closure_le _).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact ⟨Multiplicative.ofAdd (Pi.single 0 1), by rw [radicalHom_ofAdd, radicalGL_single_zero]⟩
    · exact ⟨Multiplicative.ofAdd (Pi.single 1 1), by rw [radicalHom_ofAdd, radicalGL_single_one]⟩
    · exact ⟨Multiplicative.ofAdd (Pi.single 2 1), by rw [radicalHom_ofAdd, radicalGL_single_two]⟩
    · exact ⟨Multiplicative.ofAdd (Pi.single 3 1), by rw [radicalHom_ofAdd, radicalGL_single_three]⟩

private theorem mult_fin4_sq (x : Multiplicative (Fin 4 → ZMod 2)) : x ^ 2 = 1 := by
  rw [pow_two]
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, toAdd_one]
  exact add_self_fin4 _

theorem radicalHom_range_isElemAbelian2 : IsElemAbelian2 radicalHom.range := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact (map_mul radicalHom x y).symm.trans
      ((congrArg radicalHom (mul_comm x y)).trans (map_mul radicalHom y x))
  · rintro _ ⟨x, rfl⟩
    exact (map_pow radicalHom x 2).symm.trans
      ((congrArg radicalHom (mult_fin4_sq x)).trans (map_one radicalHom))

theorem card_radicalHom_range : Nat.card radicalHom.range = 16 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective radicalHom_injective).toEquiv,
    Nat.card_eq_fintype_card, Fintype.card_multiplicative]
  simp

end CFSG.ASVolI.ChH
