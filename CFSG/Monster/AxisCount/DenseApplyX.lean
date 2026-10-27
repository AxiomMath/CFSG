module

public import CFSG.Monster.AxisCount.DenseApply
public import CFSG.Monster.B.Rep4371.KeyAct

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.AxisCount

open CFSG.Monster CFSG.Monster.B CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.ScalarKernel CFSG.Monster.Visible CFSG.Monster.Griess CFSG.Monster.B.Rep4371 Matrix

@[expose] def yKey (g : Native.GD) (p : ℕ) : Model.Pauli :=
  Native.fastAct g.tT g.tD (false, (keyOf p).1, (keyOf p).2)

@[expose] def tgtPos (g : Native.GD) (p : ℕ) : ℕ :=
  (Native.mkCtx ()).find (yKey g p).2.1 (yKey g p).2.2

@[expose] def sgPos (g : Native.GD) (p : ℕ) : ℤ := Model.sgnI (yKey g p).1

theorem rep_toC_toD (a d : ℕ) : rep (toC a, toD d) = pauliQ (false, a, d) := rfl

theorem posOf_inj
    {c₁ c₂ : ShortIdx} (h : posOf c₁ = posOf c₂) : c₁ = c₂ :=
  shortEquiv.symm.injective (Fin.ext h)

theorem thetaX_shortOf (P : Pvis) (g : Native.GD)
    (hconj : ∀ y : Model.Pauli, conjQ P (pauliQ y) = pauliQ (Native.fastAct g.tT g.tD y))
    (pp : Fin 98280) :
    ∃ h : IsShortCoord (toC (yKey g pp).2.1, toD (yKey g pp).2.2),
      thetaX P (Pi.single (shortOf pp) 1) =
        ((sgPos g pp : ℤ) : ℚ) •
          (Pi.single ⟨(toC (yKey g pp).2.1, toD (yKey g pp).2.2), h⟩ 1 : SpaceX) := by
  have h1 : conjQ P (rep (shortOf pp).1) = pauliQ (yKey g pp) := by
    have : rep (shortOf pp).1 = pauliQ (false, (keyOf pp).1, (keyOf pp).2) := rep_toC_toD _ _
    rw [this, hconj, yKey]
  have key : ∀ y : Model.Pauli, conjQ P (rep (shortOf pp).1) = pauliQ y →
      ∃ h : IsShortCoord (toC y.2.1, toD y.2.2),
        thetaX P (Pi.single (shortOf pp) 1) =
          ((Model.sgnI y.1 : ℤ) : ℚ) • (Pi.single ⟨(toC y.2.1, toD y.2.2), h⟩ 1 : SpaceX) := by
    intro y h1
    have hshort : IsShortCoord (coordOf (rep (shortOf pp).1)) := by
      rw [coordOf_rep]
      exact (shortOf pp).2
    have h2 : IsShortCoord (coordOf (pauliQ y)) := h1 ▸ isShortCoord_conjQ P hshort
    rw [coordOf_pauliQ] at h2
    refine ⟨h2, ?_⟩
    have h3 : Xlift (pauliQ (false, y.2.1, y.2.2)) =
        Pi.single ⟨(toC y.2.1, toD y.2.2), h2⟩ 1 := by
      have := Xlift_rep ⟨(toC y.2.1, toD y.2.2), h2⟩
      rwa [rep_toC_toD] at this
    rw [thetaX_single, h1, Xlift_pauliQ, h3, sgn_boolZ]
  exact key _ h1

theorem thetaX_shortOf_apply (P : Pvis) (g : Native.GD)
    (hconj : ∀ y : Model.Pauli, conjQ P (pauliQ y) = pauliQ (Native.fastAct g.tT g.tD y))
    (pp : Fin 98280) (c' : ShortIdx) :
    (thetaX P (Pi.single (shortOf pp) 1)) c' =
      if tgtPos g pp = posOf c' then ((sgPos g pp : ℤ) : ℚ) else 0 := by
  obtain ⟨h, h2⟩ := thetaX_shortOf P g hconj pp
  rw [h2, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  have hfind : tgtPos g pp = posOf ⟨(toC (yKey g pp).2.1, toD (yKey g pp).2.2), h⟩ :=
    find_eq_posOf _ _ h
  by_cases hc : c' = ⟨(toC (yKey g pp).2.1, toD (yKey g pp).2.2), h⟩
  · subst hc
    simp [hfind]
  · have : ¬ tgtPos g pp = posOf c' := fun e => hc (posOf_inj (hfind ▸ e).symm)
    simp [hc, this]

theorem xT_eq (g : Native.GD) (p : ℕ) :
    g.xT (Native.mkCtx ()) p = [(tgtPos g p, sgPos g p)] := by
  unfold Native.GD.xT tgtPos sgPos yKey keyOf
  simp [native_sgnI]

theorem sum_map_single_ite (a q : ℕ) (b x : ℤ) :
    ([(a, b)].map fun t => if t.1 = q then t.2 * x else 0).sum = if a = q then b * x else 0 := by
  simp

theorem interpX_applyGD
    (g : Native.GD) (P : Pvis) (hg : GDSpec g P) (v : Native.DVec) :
    interpX (Native.applyGD (Native.mkCtx ()) g v) = thetaX P (interpX v) := by
  funext c'
  have hq := posOf_lt c'
  have hk1 : ¬ 300 + posOf c' < 300 := by omega
  have hk2 : 300 + posOf c' < 98580 := by omega
  have hconj := hg.conj
  have hs : (∑ p ∈ Finset.range 98280,
        (((g.xT (Native.mkCtx ())) p).map
          fun t => if t.1 = posOf c' then t.2 * v.D.getD (300 + p) 0 else 0).sum) =
      ∑ p ∈ Finset.range 98280,
        if tgtPos g p = posOf c' then sgPos g p * v.D.getD (300 + p) 0 else 0 :=
    Finset.sum_congr rfl fun p _ => by
      rw [xT_eq]
      exact sum_map_single_ite _ _ _ _
  have hL : (Native.applyGD (Native.mkCtx ()) g v).D.getD (300 + posOf c') 0 =
      (∑ p ∈ Finset.range 98280,
        if tgtPos g p = posOf c' then sgPos g p * v.D.getD (300 + p) 0 else 0) *
        2 ^ g.eNew := by
    rw [Native.applyGD_getD, ite_eq_right hk1, ite_eq_left hk2,
      show 300 + posOf c' - 300 = posOf c' by omega, Native.scatterAt_getD _ _ _ _ _ hq, hs]
  have hsum : ∀ x : SpaceX, thetaX P x = ∑ c, x c • thetaX P (Pi.single c 1) := fun x => by
    conv_lhs => rw [← (Pi.basisFun ℚ ShortIdx).sum_repr x]
    simp only [map_sum, map_smul, Pi.basisFun_repr, Pi.basisFun_apply]
  have hR : (thetaX P (interpX v)) c' =
      ∑ p ∈ Finset.range 98280,
        ((v.D.getD (300 + p) 0 : ℤ) : ℚ) / 2 ^ v.e *
          (if tgtPos g p = posOf c' then ((sgPos g p : ℤ) : ℚ) else 0) := by
    rw [hsum, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← Equiv.sum_comp shortEquiv, Finset.sum_range]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [shortEquiv_apply, thetaX_shortOf_apply P g hconj p c', interpX, posOf_shortOf]
  rw [hR]
  show ((((Native.applyGD (Native.mkCtx ()) g v).D.getD (300 + posOf c') 0 : ℤ) : ℚ)) /
    2 ^ (Native.applyGD (Native.mkCtx ()) g v).e = _
  rw [hL, Native.applyGD_e]
  push_cast
  rw [Finset.sum_mul, Finset.sum_div]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [pow_add]
  split_ifs
  · field_simp
  · simp

end CFSG.Monster.AxisCount
