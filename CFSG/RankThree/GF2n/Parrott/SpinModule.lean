module

public import Certificates.Certificate946006

public section

namespace CFSG.RankThree.GF2n.Parrott

theorem Mt_sq : Mt * Mt = 1 := Certificates.certificate946006.Mt_sq

theorem rel_a2 : ∀ e : Fin 8, evalSpinWordV spinRelA2 (basis e) = basis e := by
  intro e
  apply bitmask_injective
  rw [← bitWord_bitmask, bitmask_basis, Certificates.certificate946006.rel_a2 e]

theorem rel_b5 : ∀ e : Fin 8, evalSpinWordV spinRelB5 (basis e) = basis e := by
  intro e
  apply bitmask_injective
  rw [← bitWord_bitmask, bitmask_basis, Certificates.certificate946006.rel_b5 e]

theorem rel_ab9 : ∀ e : Fin 8, evalSpinWordV spinRelAB9 (basis e) = basis e := by
  intro e
  apply bitmask_injective
  rw [← bitWord_bitmask, bitmask_basis, Certificates.certificate946006.rel_ab9 e]

theorem rel_comm3 : ∀ e : Fin 8, evalSpinWordV spinRelComm3 (basis e) = basis e := by
  intro e
  apply bitmask_injective
  rw [← bitWord_bitmask, bitmask_basis, Certificates.certificate946006.rel_comm3 e]

theorem rel_comm_bab2 : ∀ e : Fin 8, evalSpinWordV spinRelCommBab2 (basis e) = basis e := by
  intro e
  apply bitmask_injective
  rw [← bitWord_bitmask, bitmask_basis, Certificates.certificate946006.rel_comm_bab2 e]

end CFSG.RankThree.GF2n.Parrott
