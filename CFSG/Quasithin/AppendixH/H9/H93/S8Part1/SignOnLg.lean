module

public import CFSG.Quasithin.AppendixH.H9.GLBasics
public import CFSG.Quasithin.AppendixH.H9.ModelBasic
public import CFSG.Quasithin.AppendixH.H9.H93.H93Defs

public section

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

private noncomputable def pairActToMg : GL (Fin 4) (ZMod 2) →* ↥(Mg 4) :=
  (pairActN 4).codRestrict (Mg 4) fun A => Lg_le_Mg (pairActN_mem_Lg A)

theorem sign_psiExt_pairActN (ψ : ↥(Mg 4) ≃* Equiv.Perm (Fin 8)) (A : GL (Fin 4) (ZMod 2)) :
    Equiv.Perm.sign (psiExt ψ (pairActN 4 A)) = 1 := by
  let χ : GL (Fin 4) (ZMod 2) →* ℤˣ :=
    Equiv.Perm.sign.comp (ψ.toMonoidHom.comp pairActToMg)
  have hperf : Group.IsPerfect (GL (Fin 4) (ZMod 2)) := isPerfect_GL_two (by norm_num)
  have hA : A ∈ commutator (GL (Fin 4) (ZMod 2)) := by
    rw [Group.isPerfect_def.mp hperf]
    trivial
  have h : A ∈ χ.ker := Abelianization.commutator_subset_ker χ hA
  rw [psiExt_of_mem ψ (Lg_le_Mg (pairActN_mem_Lg A))]
  exact h

end CFSG.ASVolI.ChH
