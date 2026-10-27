module

public import CFSG.Monster.AxisCount.DenseShort
public import CFSG.Monster.AxisCount.DenseIndex
public import CFSG.Monster.B.Rep4371.Raw

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.AxisCount

open CFSG.Monster CFSG.Monster.B CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.B.Rep4371 Matrix

theorem key_short
    (p : ℕ) (hp : p < 98280) : IsShortCoord (toC (keyOf p).1, toD (keyOf p).2) := by
  by_cases h1 : p < 552
  · have hp2 : p / 2 < 276 := by omega
    obtain ⟨hlt, h24, -⟩ := Native.pairTab_spec (p / 2) hp2
    rw [keyOf_pair p h1]
    generalize Native.pairTab[p / 2]! = t at hlt h24 ⊢
    have hi : t.1 < 24 := lt_trans hlt h24
    have hne : (⟨t.1, hi⟩ : Fin 24) ≠ ⟨t.2, h24⟩ := fun e => by
      have := congrArg Fin.val e
      simp only at this
      omega
    have hlt' : (⟨t.1, hi⟩ : Fin 24) < ⟨t.2, h24⟩ := Fin.mk_lt_mk.2 hlt
    by_cases hpar : p % 2 = 0
    · rw [ite_eq_left hpar]
      have h := isShortCoord_labelElt (.inl ⟨(⟨t.1, hi⟩, ⟨t.2, h24⟩), hlt'⟩ : ShortLabel)
      have e := pauliQ_minus hne
      simp only [labelElt] at h
      rw [← e, coordOf_pauliQ] at h
      exact h
    · rw [ite_eq_right hpar]
      have h := isShortCoord_labelElt (.inr (.inl ⟨(⟨t.1, hi⟩, ⟨t.2, h24⟩), hlt'⟩) : ShortLabel)
      have e := pauliQ_plus hne
      simp only [labelElt] at h
      rw [← e, coordOf_pauliQ] at h
      exact h
  · by_cases h2 : p < 49704
    · have hi : (p - 552) % 24 < 24 := Nat.mod_lt _ (by norm_num)
      have hn : (2 * ((p - 552) / 24)).testBit 0 = false := by simp [Nat.testBit_zero]
      have h := isShortCoord_labelElt (.inr (.inr (.inl (π₀ (toC (2 * ((p - 552) / 24))),
        ⟨(p - 552) % 24, hi⟩))) : ShortLabel)
      have e := pauliQ_odd' (2 * ((p - 552) / 24)) hn ⟨(p - 552) % 24, hi⟩
      simp only [labelElt] at h
      rw [← e, coordOf_pauliQ] at h
      rw [keyOf_odd p (by omega) h2]
      exact h
    · have ho : (p - 49704) / 64 < 759 := by omega
      have hq : (p - 49704) % 64 < 64 := Nat.mod_lt _ (by norm_num)
      have h := short_octG _ _ ho hq
      rw [← pauliQ_octG, coordOf_pauliQ] at h
      rw [keyOf_oct p (by omega) hp]
      exact h

@[expose] noncomputable def shortOf (p : Fin 98280) : ShortIdx :=
  ⟨(toC (keyOf p).1, toD (keyOf p).2), key_short p p.2⟩

theorem shortOf_injective : Function.Injective shortOf := by
  intro p q h
  have h1 := congrArg Subtype.val h
  simp only [shortOf, Prod.mk.injEq] at h1
  have hp := keyOf_lt p p.2
  have hq := keyOf_lt q q.2
  have e1 := toC_inj hp.1 hq.1 h1.1
  have e2 := toD_inj hp.2 hq.2 h1.2
  have : keyOf p = keyOf q := Prod.ext e1 e2
  apply Fin.ext
  rw [← find_keyOf p p.2, ← find_keyOf q q.2, this]

@[expose] noncomputable def shortEquiv : Fin 98280 ≃ ShortIdx :=
  Equiv.ofBijective shortOf ((Fintype.bijective_iff_injective_and_card _).2
    ⟨shortOf_injective, by rw [Fintype.card_fin, card_shortIdx']⟩)

theorem shortEquiv_apply
    (p : Fin 98280) : shortEquiv p = shortOf p := rfl

@[expose] noncomputable def posOf
    (c : ShortIdx) : ℕ := (shortEquiv.symm c : ℕ)

theorem posOf_lt
    (c : ShortIdx) : posOf c < 98280 := (shortEquiv.symm c).2

theorem shortOf_posOf
    (c : ShortIdx) : shortOf ⟨posOf c, posOf_lt c⟩ = c := by
  have := shortEquiv.apply_symm_apply c
  exact this

theorem posOf_shortOf (p : Fin 98280) : posOf (shortOf p) = p := by
  have := shortEquiv.symm_apply_apply p
  rw [shortEquiv_apply] at this
  exact congrArg Fin.val this

theorem find_eq_posOf
    (a' d' : ℕ) (h : IsShortCoord (toC a', toD d')) :
    (Native.mkCtx ()).find a' d' = posOf ⟨(toC a', toD d'), h⟩ := by
  let c : ShortIdx := ⟨(toC a', toD d'), h⟩
  have hq := posOf_lt c
  have hs : ((toC (keyOf (posOf c)).1, toD (keyOf (posOf c)).2) : C × Cocode) =
      (toC a', toD d') := congrArg Subtype.val (shortOf_posOf c)
  rw [Prod.mk.injEq] at hs
  have hk := keyOf_lt (posOf c) hq
  have e1 : (keyOf (posOf c)).1 = a' % 4096 :=
    toC_inj hk.1 (Nat.mod_lt _ (by norm_num)) (by rw [hs.1, toC_mod_4096])
  have e2 : (keyOf (posOf c)).2 = d' % 4096 :=
    toD_inj hk.2 (Nat.mod_lt _ (by norm_num)) (by rw [hs.2, toD_mod_4096])
  have := find_keyOf (posOf c) hq
  rw [← this, e1, e2]
  unfold Native.Ctx.find Native.keyCode
  simp only [Nat.mod_mod]

theorem aIdx_symm_matrix (v : Native.DVec) :
    (Matrix.of fun i j : Fin 24 => (v.D.getD (Native.aIdx i j) 0 : ℚ) / 2 ^ v.e)ᵀ =
      Matrix.of fun i j : Fin 24 => (v.D.getD (Native.aIdx i j) 0 : ℚ) / 2 ^ v.e := by
  ext i j
  simp only [transpose_apply, of_apply]
  rw [Native.aIdx_comm]

@[expose] noncomputable def interpA (v : Native.DVec) : symMat :=
  ⟨Matrix.of fun i j : Fin 24 => (v.D.getD (Native.aIdx i j) 0 : ℚ) / 2 ^ v.e,
    mem_symMat.2 (aIdx_symm_matrix v)⟩

@[expose] noncomputable def interpX (v : Native.DVec) : SpaceX :=
  fun c => (v.D.getD (300 + posOf c) 0 : ℚ) / 2 ^ v.e

@[expose] noncomputable def interpW (v : Native.DVec) : SpaceW :=
  Matrix.of fun (s : SpinIdx) (j : Fin 24) =>
    (v.D.getD (98580 + 24 * rowOf s + j) 0 : ℚ) / 2 ^ v.e

@[expose] noncomputable def interp
    (v : Native.DVec) : SpaceB := (interpA v, interpX v, interpW v)

end CFSG.Monster.AxisCount
