module

public import CFSG.Quasithin.Background.HMathieuCode
public import CFSG.Quasithin.Background.HMathieuMask

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code

@[expose] def κCCols : List ℕ :=
  [0, 33, 65, 97, 0, 130, 258, 386, 0, 516, 1028, 1540, 0, 8, 8, 8, 0, 16, 16, 16, 0, 31, 31, 31]

@[expose] def liftCCols : List ℕ :=
  [0x11111e, 0x1111e1, 0x111e11, 0x11e111, 0x1e1111, 0xa6c00c, 0x6ca00a, 0x6ac0c0, 0xc6a0a0,
    0xcccc00, 0xaaaa00]

@[expose] def κC22Cols : List ℕ :=
  [0, 16, 32, 48, 0, 65, 129, 193, 0, 258, 514, 770, 0, 4, 4, 4, 0, 8, 8, 8, 0, 15, 15, 15]

@[expose] def lift22Cols : List ℕ :=
  [0xff, 0xf0f, 0xf00f, 0xf000f, 0xa6c00c, 0x7db114, 0x6ac0c0, 0xc6a0a0, 0xcccc00, 0xaaaa00]

theorem κC_cols : ∀ j < 24, κC (bvec 24 (2 ^ j)) = bvec 11 (κCCols.getD j 0) := by
  decide +kernel

theorem liftC_cols : ∀ j < 11, liftC (bvec 11 (2 ^ j)) = bvec 24 (liftCCols.getD j 0) := by
  decide +kernel

theorem κC22_cols : ∀ j < 24, κC22 (bvec 24 (2 ^ j)) = bvec 10 (κC22Cols.getD j 0) := by
  decide +kernel

theorem lift22_cols : ∀ j < 10, lift22 (bvec 10 (2 ^ j)) = bvec 24 (lift22Cols.getD j 0) := by
  decide +kernel

theorem κC_bvec (x : ℕ) : κC (bvec 24 x) = bvec 11 (actM κCCols x) :=
  addHom_bvec κC.toAddMonoidHom κCCols rfl κC_cols x

theorem liftC_bvec (x : ℕ) : liftC (bvec 11 x) = bvec 24 (actM liftCCols x) :=
  addHom_bvec liftC.toAddMonoidHom liftCCols rfl liftC_cols x

theorem κC22_bvec (x : ℕ) : κC22 (bvec 24 x) = bvec 10 (actM κC22Cols x) :=
  addHom_bvec κC22.toAddMonoidHom κC22Cols rfl κC22_cols x

theorem lift22_bvec (x : ℕ) : lift22 (bvec 10 x) = bvec 24 (actM lift22Cols x) :=
  addHom_bvec lift22.toAddMonoidHom lift22Cols rfl lift22_cols x

theorem κCCols_lt : ∀ c ∈ κCCols, c < 2 ^ 11 := by decide

theorem κC22Cols_lt : ∀ c ∈ κC22Cols, c < 2 ^ 10 := by decide

@[expose] def actC11 (a : Array ℕ) (m : ℕ) : ℕ := actM κCCols (permM a (actM liftCCols m))

@[expose] def actC10 (a : Array ℕ) (m : ℕ) : ℕ := actM κC22Cols (permM a (actM lift22Cols m))

theorem xorLin_actC11 (a : Array ℕ) : XorLin (actC11 a) :=
  ((actM_xor _).comp (actM_xor _)).comp (actM_xor _)

theorem xorLin_actC10 (a : Array ℕ) : XorLin (actC10 a) :=
  ((actM_xor _).comp (actM_xor _)).comp (actM_xor _)

theorem actC11_lt (a : Array ℕ) (m : ℕ) : actC11 a m < 2 ^ 11 := actM_lt κCCols_lt _

theorem actC10_lt (a : Array ℕ) (m : ℕ) : actC10 a m < 2 ^ 10 := actM_lt κC22Cols_lt _

theorem rhoC11_toW (Γ : Subgroup (Equiv.Perm (Fin 24))) (hΓ : Γ ≤ AutPerm) (σ : ↥Γ)
    {a : Array ℕ} (ha : HasArr (σ : Equiv.Perm (Fin 24)) a) (m : ℕ) :
    rhoC11 Γ hΓ σ (toW 11 m) = toW 11 (actC11 a m) := by
  have h1 : rhoC11 Γ hΓ σ (toW 11 m) =
      codeCoords.κ (G6.permAct 24 σ (codeCoords.lift (toW 11 m))) := rfl
  have h2 : Multiplicative.toAdd (codeCoords.lift (toW 11 m)) = liftC (bvec 11 m) := rfl
  have h3 : ∀ x, codeCoords.κ x = Multiplicative.ofAdd (κC (Multiplicative.toAdd x)) :=
    fun _ => rfl
  rw [h1, h3, toAdd_permAct, h2, liftC_bvec, permWord_bvec ha, κC_bvec]
  rfl

theorem rhoC10_toW (Γ : Subgroup (Equiv.Perm (Fin 24))) (hΓ : Γ ≤ mog22plus) (σ : ↥Γ)
    {a : Array ℕ} (ha : HasArr (σ : Equiv.Perm (Fin 24)) a) (m : ℕ) :
    rhoC10 Γ hΓ σ (toW 10 m) = toW 10 (actC10 a m) := by
  have h1 : rhoC10 Γ hΓ σ (toW 10 m) =
      code22Coords.κ (G6.permAct 24 σ (code22Coords.lift (toW 10 m))) := rfl
  have h2 : Multiplicative.toAdd (code22Coords.lift (toW 10 m)) = lift22 (bvec 10 m) := rfl
  have h3 : ∀ x, code22Coords.κ x = Multiplicative.ofAdd (κC22 (Multiplicative.toAdd x)) :=
    fun _ => rfl
  rw [h1, h3, toAdd_permAct, h2, lift22_bvec, permWord_bvec ha, κC22_bvec]
  rfl

end CFSG.Quasithin.H.Mathieu
