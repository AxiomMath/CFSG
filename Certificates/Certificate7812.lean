module

public import CFSG.Milestones.ASVolI.F48.D43.EInputs
public import Certificates.Certificate7804
import CFSG.Certificates.Kernel.Misc.Coset.PGNormal

public section

open CFSG CFSG.ASVolI CFSG.CosetTable CFSG.KC.MiscCoset

namespace Certificates

private def certificate7812_A : List (Fin 18) := (List.finRange 17).map (Fin.succAbove 2)

private theorem certificate7812_rel : ∀ w ∈ burnsideF48d_Ws (),
    w.map (fun l => (Fin.succAbove (2 : Fin 18) l.1, l.2)) ∈ burnsideF48dE_Ws 0 := by
  decide +kernel

private theorem certificate7812_P : ∀ i ∈ subsetOf 17 burnsideF48d_tS1,
    Fin.succAbove (2 : Fin 18) i ∈ subsetOf 18 burnsideF48dE_S1 := by
  decide +kernel

private theorem certificate7812_all : ∀ j : Fin 18, j ∈ certificate7812_A ∨ j = 2 := by
  decide +kernel

private theorem certificate7812_cover :
    ∀ j : Fin 18, j ∈ certificate7812_A ∨ j ∈ subsetOf 18 burnsideF48dE_S1 := by
  decide +kernel

private theorem certificate7812_conj :
    ∀ a ∈ certificate7812_A, (burnsideF48dE_Ws 0).any (conjOK certificate7812_A 2 a) = true := by
  decide +kernel

private theorem certificate7812_cube :
    List.replicate 3 ((2 : Fin 18), true) ∈ burnsideF48dE_Ws 0 := by
  decide +kernel

open CFSG CFSG.ASVolI CFSG.CosetTable in
theorem certificate7812 : (genSub {r : FreeGroup (Fin 18) | r ∈ (burnsideF48dE_Ws 0).map FreeGroup.mk}
      (subsetOf 18 burnsideF48dE_S1)).FiniteIndex ∧
    (genSub {r : FreeGroup (Fin 18) | r ∈ (burnsideF48dE_Ws 0).map FreeGroup.mk}
      (subsetOf 18 burnsideF48dE_S1)).index ≤ 26572 := by
  obtain ⟨h04f, h04⟩ := Certificates.certificate7804
  have := genSub_normal certificate7812_all certificate7812_conj (by norm_num) certificate7812_cube
  obtain ⟨hfi, hle⟩ := index_le_of_hom (pgMap _ certificate7812_rel) _ _ _
    (genSub_le_range _ certificate7812_rel fun j hj => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hj
      exact ⟨i, rfl⟩)
    (genSub_sup_eq_top certificate7812_cover)
    (map_genSub_le _ certificate7812_rel certificate7812_P)
  exact ⟨hfi, hle.trans h04⟩

end Certificates
