module

public import Certificates.Kernel.OPlusFourTwo.Checks
public import CFSG.Certificates.Kernel.OPlusFourTwoSound

public section

namespace Certificates

open CFSG.OPlusFourTwo CFSG.KP.OPlusFourTwo CFSG.KS.OPlusFourTwo

open CFSG.OPlusFourTwo in
theorem certificate7151 :
    (∀ M : Matrix (Fin 4) (Fin 4) (ZMod 2), PreservesQ0 M → M ∈ o4List) ∧
    (∀ M ∈ o4List, PreservesQ0 M) ∧
    o4List.Nodup ∧
    (∀ M ∈ o4List, M ^ 12 = 1) ∧
    (o4List.filter (fun M => M ^ 3 = 1)).length = 9 ∧
    (∀ M ∈ o4List, M ^ 9 = 1 → M ^ 3 = 1) := by
  have h12 := pow_twelve_of_pow12B pow12_ok
  refine ⟨mem_of_treeB vecs_ok tree_ok, preserves_of_soundB vecs_ok sound_ok,
    nodup_of_distinctP distinct_ok, h12, by rw [filter_cube_eq]; exact three_ok, ?_⟩
  intro M hM h9
  have h := h12 M hM
  rwa [(by rfl : (12 : ℕ) = 9 + 3), pow_add, h9, one_mul] at h

end Certificates
