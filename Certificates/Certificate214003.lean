module

public import CFSG.LieType.ChevTwo.OppCl.SmallU33Check
import CFSG.Certificates.Kernel.PermCent.U33Sound
import CFSG.Certificates.Kernel.PermCent.KGrpCSound
import CFSG.GH74.KGroups.U33
import Certificates.Kernel.PermCent.KU33

public section

open CFSG.Certificates.Kernel.PkCV.U33T

namespace Certificates

open CFSG.LieType.ChevTwo.OppCl.U33Fin in
theorem certificate214003 : (checkCenter () = true)
    ∧ (checkExp () = true)
    ∧ (checkF1 () = true)
    ∧ (checkF3 () = true)
    ∧ (checkX5 () = true) := by
  have hmem : ∀ σ ∈ ({CFSG.GH74.KGroups.U33.pa, CFSG.GH74.KGroups.U33.pb} :
      Set (Equiv.Perm (Fin 28))), CFSG.Certificates.Kernel.PkCV.cOf σ ∈
        CFSG.Certificates.Kernel.PkCV.elemsC CFSG.GH74.KGroups.U33.QP := fun σ hσ =>
    (CFSG.Certificates.Kernel.PkCV.KGrp.mem_elemsC _ CFSG.GH74.KGroups.U33.QP_ok _).2 (by
      rw [CFSG.Certificates.Kernel.PkCV.ev_cOf, CFSG.GH74.KGroups.U33.QP_closure]
      exact Subgroup.subset_closure hσ)
  have hconj := fun σ hσ y hy => CFSG.Certificates.Kernel.PkCV.KGrp.conj_mem_elemsC _
    CFSG.GH74.KGroups.U33.QP_ok (hmem σ hσ) (y := y) hy
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [center_eq]
    exact kCenter
  · rw [exp_eq]
    exact kExp
  · rw [f1_eq]
    exact kuF1_of_cls (hconj _ (Set.mem_insert _ _)) (hconj _ (Set.mem_insert_of_mem _ rfl)) kF1C
  · rw [f3_eq]
    exact kuF3_of_cls (hconj _ (Set.mem_insert _ _)) (hconj _ (Set.mem_insert_of_mem _ rfl)) kF3C
  · have hinv := fun σ hσ y hy => CFSG.Certificates.Kernel.PkCV.KGrp.conj_mem_elemsC _
      CFSG.GH74.KGroups.U33.QP_ok ((CFSG.Certificates.Kernel.PkCV.KGrp.mem_elemsC _
        CFSG.GH74.KGroups.U33.QP_ok _).2 (by
          rw [CFSG.Certificates.Kernel.PkCV.ev_inv]
          exact inv_mem ((CFSG.Certificates.Kernel.PkCV.KGrp.mem_elemsC _
            CFSG.GH74.KGroups.U33.QP_ok _).1 (hmem σ hσ)))) (y := y) hy
    rw [x5_eq]
    exact kuX5_of_cls (hconj _ (Set.mem_insert _ _)) (hconj _ (Set.mem_insert_of_mem _ rfl))
      (hinv _ (Set.mem_insert _ _)) (hinv _ (Set.mem_insert_of_mem _ rfl)) kF3C

end Certificates
