module

public import CFSG.Quasithin.Background.RonanH163Base
public import CFSG.Quasithin.Background.RonanH163Vocab

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH154

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.RonanH143 CFSG.Quasithin.RonanH163
  CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Mathieu.H16Pf

noncomputable abbrev Rc : ↥mog22plus →* MulAut W10 := rho10 mog22plus le_rfl

theorem Rc_toW (σ : ↥mog22plus) {a : Array ℕ} (ha : HasArr (σ : P24) a) (m : ℕ) :
    Rc σ (toW 10 m) = toW 10 (act10 a m) :=
  rho10_toW mog22plus le_rfl σ ha m

theorem Rc_nq2 (u : Fin 32) (m : ℕ) :
    Rc (nq2Elt u) (toW 10 m) = toW 10 (act10 (nq2Arr u) m) :=
  Rc_toW _ (hasArr_nq2 u) m

theorem Rc_g1 (m : ℕ) : Rc g1Elt (toW 10 m) = toW 10 (act10 g1Arr m) :=
  Rc_toW _ hasArr_g1Perm m

theorem Rc_g2 (m : ℕ) : Rc g2Elt (toW 10 m) = toW 10 (act10 g2Arr m) :=
  Rc_toW _ hasArr_g2 m

@[expose] def w1 : List ℕ := [128]

@[expose] def w2 : List ℕ := [78] ++ w1

@[expose] def w6 : List ℕ := [30, 32, 262, 512] ++ w2

@[expose] def w10 : List ℕ := [1, 2, 4, 8] ++ w6

@[expose] def X1 : Subgroup W10 := maskSub 10 w1

@[expose] def X2 : Subgroup W10 := maskSub 10 w2

@[expose] def X6 : Subgroup W10 := maskSub 10 w6

end CFSG.Quasithin.RonanH154
