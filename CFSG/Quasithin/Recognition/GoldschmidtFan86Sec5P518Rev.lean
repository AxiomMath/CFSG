module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P518CA

public section

namespace CFSG.Quasithin.Fan86

namespace P518

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P62

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable {L : ZLab Γ G} {T : Track Γ G} {a : ℤ}

theorem xv_rev (T : Track Γ G) (a i : ℤ) : xv T.rev (-a - 12) i = xv T a (10 - i) := by
  show T.line.rev.vert (-a - 12 + 1 + i) = T.line.vert (a + 1 + (10 - i))
  rw [Line.rev_vert]
  congr 1
  ring

theorem zA_rev (L : ZLab Γ G) (T : Track Γ G) (a k : ℤ) :
    zA L T.rev (-a - 12) k = zA L T a (5 - k) := by
  show L.z (xv T.rev (-a - 12) (2 * k)) = L.z (xv T a (2 * (5 - k)))
  rw [xv_rev, show 10 - 2 * k = 2 * (5 - k) by ring]

theorem Ctx.rev (F : FanTree Γ G) (C : Ctx L T a) : Ctx L T.rev (-a - 12) where
  val5 := by
    rw [xv_rev]
    simpa using C.val_even F 5
  fix i := by
    rw [xv_rev, xv_rev]
    have e : (10 : ℤ) - 0 = 2 * 5 := by norm_num
    rw [e]
    exact (zA_fix C 5 (10 - i)).trans (by omega)

theorem EG.rev (F : FanTree Γ G) (H : Lab18 L) (C : Ctx L T a)
    (hb2 : zA L T a 5 • zA L T a 0 • xv T a 9 ≠ zA L T a 0 • xv T a 9) :
    EG L T.rev (-a - 12) :=
  EG.mk' F H (C.rev F) (by simpa [zA_rev, xv_rev] using hb2)

end P518

end CFSG.Quasithin.Fan86
