module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P518Fin2
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P518B3a
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P518B3b
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P518B3c

public section

namespace CFSG.Quasithin.Fan86

namespace P518

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P62

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem endgame (F : FanTree Γ G)
    (hb3 : ∀ (L : ZLab Γ G) (T : Track Γ G) (a : ℤ), EG L T a → wE L T a * uE L T a = 1)
    {L : ZLab Γ G} {T : Track Γ G} {a : ℤ} (H : Lab18 L) (C : Ctx L T a) (hT : T.fixer = ⊥)
    (hb2 : zA L T a 0 • zA L T a 5 • xv T a 1 ≠ zA L T a 5 • xv T a 1)
    (hb2' : zA L T a 5 • zA L T a 0 • xv T a 9 ≠ zA L T a 0 • xv T a 9) : False := by
  have E := EG.mk' F H C hb2
  have E' := EG.rev F H C hb2'
  exact b5 F H E hT (b4 F C (hb3 L T a E) (hb3 L T.rev (-a - 12) E'))

theorem b3 (F : FanTree Γ G) (h40 : Fan40 F) {L : ZLab Γ G} {T : Track Γ G} {a : ℤ}
    (E : EG L T a) : wE L T a * uE L T a = 1 :=
  b3_of_ab F E.lab E.ctx (b3a F h40 E) (b3b F h40 E)

end P518

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

end CFSG.Quasithin.Fan86
