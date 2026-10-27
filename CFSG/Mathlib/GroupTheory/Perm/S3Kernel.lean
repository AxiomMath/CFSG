module

public import TauCeti.GroupTheory.Perm.FinThree.Basic

public section

namespace CFSG

open Equiv

theorem injective_of_finRotate_not_mem_ker {H : Type*} [Group H]
    (ρ : Equiv.Perm (Fin 3) →* H)
    (hcnot : (finRotate 3 : Equiv.Perm (Fin 3)) ∉ ρ.ker) :
    Function.Injective ρ := by
  classical
  have hker : ρ.ker.Normal := MonoidHom.normal_ker _
  refine (injective_iff_map_eq_one ρ).mpr ?_
  intro σ hσ
  have hσmem : σ ∈ ρ.ker := MonoidHom.mem_ker.mpr hσ
  rcases Equiv.Perm.fin_three_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · exfalso
    have hconj : (finRotate 3 : Equiv.Perm (Fin 3)) * Equiv.swap 0 1 *
        ((finRotate 3)⁻¹ : Equiv.Perm (Fin 3)) = Equiv.swap 1 2 := by decide +kernel
    have hmem_conj : (Equiv.swap 1 2 : Equiv.Perm (Fin 3)) ∈ ρ.ker := by
      simpa [hconj] using hker.conj_mem (Equiv.swap 0 1) hσmem (finRotate 3)
    have hprod : (Equiv.swap 0 1 : Equiv.Perm (Fin 3)) * Equiv.swap 1 2 = finRotate 3 := by
      decide +kernel
    have hmem_c : (finRotate 3 : Equiv.Perm (Fin 3)) ∈ ρ.ker := by
      simpa [hprod] using mul_mem hσmem hmem_conj
    exact hcnot hmem_c
  · exfalso
    have hconj : (finRotate 3 : Equiv.Perm (Fin 3)) * Equiv.swap 1 2 *
        ((finRotate 3)⁻¹ : Equiv.Perm (Fin 3)) = Equiv.swap 0 2 := by decide +kernel
    have hmem_conj : (Equiv.swap 0 2 : Equiv.Perm (Fin 3)) ∈ ρ.ker := by
      simpa [hconj] using hker.conj_mem (Equiv.swap 1 2) hσmem (finRotate 3)
    have hprod : (Equiv.swap 1 2 : Equiv.Perm (Fin 3)) * Equiv.swap 0 2 = finRotate 3 := by
      decide +kernel
    have hmem_c : (finRotate 3 : Equiv.Perm (Fin 3)) ∈ ρ.ker := by
      simpa [hprod] using mul_mem hσmem hmem_conj
    exact hcnot hmem_c
  · exfalso
    have hconj : (finRotate 3 : Equiv.Perm (Fin 3)) * Equiv.swap 0 2 *
        ((finRotate 3)⁻¹ : Equiv.Perm (Fin 3)) = Equiv.swap 0 1 := by decide +kernel
    have hmem_conj : (Equiv.swap 0 1 : Equiv.Perm (Fin 3)) ∈ ρ.ker := by
      simpa [hconj] using hker.conj_mem (Equiv.swap 0 2) hσmem (finRotate 3)
    have hprod : (Equiv.swap 0 2 : Equiv.Perm (Fin 3)) * Equiv.swap 0 1 = finRotate 3 := by
      decide +kernel
    have hmem_c : (finRotate 3 : Equiv.Perm (Fin 3)) ∈ ρ.ker := by
      simpa [hprod] using mul_mem hσmem hmem_conj
    exact hcnot hmem_c
  · exact absurd hσmem hcnot
  · exfalso
    have hmem_c : (finRotate 3 : Equiv.Perm (Fin 3)) ∈ ρ.ker := by
      have hinv : ((finRotate 3)⁻¹ : Equiv.Perm (Fin 3))⁻¹ ∈ ρ.ker :=
        inv_mem hσmem
      simpa using hinv
    exact hcnot hmem_c

end CFSG

end
