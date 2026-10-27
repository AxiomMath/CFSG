module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P518ClA
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P518Ctx

public section

namespace CFSG.Quasithin.Fan86

namespace P518

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P62

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable {L : ZLab Γ G} {T : Track Γ G} {a : ℤ}

theorem xv_adj_of (T : Track Γ G) (a : ℤ) {i j : ℤ} (h : j = i + 1) :
    Γ.Adj (xv T a i) (xv T a j) := by
  subst h
  exact xv_adj T a i

theorem xv_ne_of (T : Track Γ G) (a : ℤ) {i j : ℤ} (h : j = i + 2) : xv T a i ≠ xv T a j := by
  subst h
  exact xv_ne T a i

theorem zA_ball_fwd (F : FanTree Γ G) (H : Lab18 L) (C : Ctx L T a) (k : ℤ) :
    zA L T a k ∈ ballStab Γ G 2 (xv T a (2 * k + 4)) :=
  claimA' F H (x0 := xv T a (2 * k)) (x1 := xv T a (2 * k + 1)) (x2 := xv T a (2 * k + 2))
    (x3 := xv T a (2 * k + 3)) (x4 := xv T a (2 * k + 4)) (x5 := xv T a (2 * k + 5))
    (xv_adj T a (2 * k)) (xv_adj_of T a (by ring)) (xv_adj_of T a (by ring))
    (xv_adj_of T a (by ring)) (xv_adj_of T a (by ring))
    (xv_ne_of T a (by ring)) (xv_ne_of T a (by ring)) (xv_ne_of T a (by ring))
    (C.val_even F k) ((zA_fix C k _).2 ⟨by omega, by omega⟩) ((zA_fix C k _).2 ⟨by omega, by omega⟩)
    ((zA_fix C k _).2 ⟨by omega, by omega⟩)

theorem zA_ball_bwd (F : FanTree Γ G) (H : Lab18 L) (C : Ctx L T a) (k : ℤ) :
    zA L T a k ∈ ballStab Γ G 2 (xv T a (2 * k - 4)) :=
  claimA' F H (x0 := xv T a (2 * k)) (x1 := xv T a (2 * k - 1)) (x2 := xv T a (2 * k - 2))
    (x3 := xv T a (2 * k - 3)) (x4 := xv T a (2 * k - 4)) (x5 := xv T a (2 * k - 5))
    (xv_adj_of T a (by ring)).symm (xv_adj_of T a (by ring)).symm (xv_adj_of T a (by ring)).symm
    (xv_adj_of T a (by ring)).symm (xv_adj_of T a (by ring)).symm
    (xv_ne_of T a (by ring)).symm (xv_ne_of T a (by ring)).symm (xv_ne_of T a (by ring)).symm
    (C.val_even F k) ((zA_fix C k _).2 ⟨by omega, by omega⟩) ((zA_fix C k _).2 ⟨by omega, by omega⟩)
    ((zA_fix C k _).2 ⟨by omega, by omega⟩)

theorem EG.mk' (F : FanTree Γ G) (H : Lab18 L) (C : Ctx L T a)
    (hb2 : zA L T a 0 • zA L T a 5 • xv T a 1 ≠ zA L T a 5 • xv T a 1) : EG L T a where
  lab := H
  ctx := C
  hA0 := by simpa using zA_ball_fwd F H C 0
  hA4 := by simpa using zA_ball_bwd F H C 4
  hA5 := by simpa using zA_ball_bwd F H C 5
  hb2 := hb2

end P518

end CFSG.Quasithin.Fan86
