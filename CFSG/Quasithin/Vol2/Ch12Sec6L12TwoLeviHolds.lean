module

public import CFSG.Quasithin.Vol2.Ch12Sec6L12TwoLeviSection
public import CFSG.Quasithin.Vol2.Ch12Sec6L12TwoAlt

public section

namespace CFSG.Quasithin.H13.K1262Two

open CFSG.Open CFSG.Blueprint

private def a6Four : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 4 5, by
    rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

private theorem a6Four_pow_four : a6Four ^ 2 ^ 2 = 1 := by
  apply Subtype.ext
  decide

private theorem a6Four_sq_ne_one : a6Four ^ 2 ≠ 1 := by
  intro h
  have h' := congrArg (fun p : alternatingGroup (Fin 6) => (p : Equiv.Perm (Fin 6)) 0) h
  exact absurd h' (by decide)

theorem leviA6Free_holds :
    LeviA6Free := by
  intro X _ _ t n f hfam hmodel S P hP hNS hTits Y hYP φ hφ
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := isSimpleGroup_alt6
  exact false_of_char2LeviFamily_of_surjective (H := alternatingGroup (Fin 6))
    exists_noncomm_alt6 ⟨a6Four, ⟨2, a6Four_pow_four⟩, a6Four_sq_ne_one⟩
    (by rw [card_alt6]; norm_num) (by rw [card_alt6]; norm_num)
    hfam hmodel S hP hNS hTits hYP φ hφ

end CFSG.Quasithin.H13.K1262Two
