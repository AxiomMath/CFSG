module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P518CA

public section

namespace CFSG.Quasithin.Fan86

namespace P518

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P62

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

structure B2Set (F : FanTree Γ G) (L : ZLab Γ G) (T : Track Γ G) (a : ℤ) : Prop where
  h40 : Fan40 F
  h33 : Fan33 F
  hn4 : ¬ LineSingLe Γ G T.line 4
  lab : Lab18 L
  ctx : Ctx L T a

@[expose] def labSpan2 (L : ZLab Γ G) (v : V) : Subgroup G :=
  Subgroup.closure {g | ∃ l, valence Γ l = 5 ∧ Γ.dist v l = 2 ∧ g = L.z l}

@[expose] noncomputable def cIdx (Γ : SimpleGraph V) (x : G) (v : V) : ℕ :=
  (Subgroup.centralizer ({x} : Set G)).relIndex (nbrStab Γ G v)

@[expose] noncomputable def nOrb (T : Track Γ G) (a : ℤ) : ℕ :=
  Set.ncard {w : V | ∃ g ∈ T.subFixer (a + 2) (a + 5), w = g • xv T a 5}

variable {F : FanTree Γ G} {L : ZLab Γ G} {T : Track Γ G} {a : ℤ}

namespace B2Set

theorem val_even (S : B2Set F L T a) (k : ℤ) : valence Γ (xv T a (2 * k)) = 5 :=
  S.ctx.val_even F k

theorem val_odd (S : B2Set F L T a) (k : ℤ) : valence Γ (xv T a (2 * k + 1)) = 3 :=
  S.ctx.val_odd F k

theorem claimA_fwd (S : B2Set F L T a) (k : ℤ) :
    zA L T a k ∈ ballStab Γ G 2 (xv T a (2 * k + 4)) :=
  zA_ball_fwd F S.lab S.ctx k

theorem zA_fix_iff (S : B2Set F L T a) (k i : ℤ) :
    zA L T a k • xv T a i = xv T a i ↔ 2 * k - 6 ≤ i ∧ i ≤ 2 * k + 6 :=
  zA_fix S.ctx k i

end B2Set

end P518

end CFSG.Quasithin.Fan86
