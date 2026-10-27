module

public import CFSG.Monster.AxisCount.DenseCheck
public import CFSG.Monster.B.Rep4371.GlueDefs
public import CFSG.Monster.B.Rep4371.SpinAct

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.AxisCount

open CFSG.Monster CFSG.Monster.B CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.Griess
  CFSG.Monster.Visible CFSG.Monster.B.Rep4371 Matrix

theorem toC_inj {a b : ℕ} (ha : a < 4096) (hb : b < 4096) (h : toC a = toC b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 12
  · have h' := congrArg (fun x => basisC.repr x ⟨i, hi⟩) h
    simp only [repr_toC_apply] at h'
    exact boolZ_injective h'
  · have e : ∀ n : ℕ, n < 4096 → n.testBit i = false := fun n hn =>
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hn
        (by calc 4096 = 2 ^ 12 := by norm_num
              _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [e a ha, e b hb]

theorem toD_inj {a b : ℕ} (ha : a < 4096) (hb : b < 4096) (h : toD a = toD b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 12
  · have h' := congrArg (fun x => pair (basisC ⟨i, hi⟩) x) h
    simp only [pair_basisC_toD] at h'
    exact boolZ_injective h'
  · have e : ∀ n : ℕ, n < 4096 → n.testBit i = false := fun n hn =>
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hn
        (by calc 4096 = 2 ^ 12 := by norm_num
              _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [e a ha, e b hb]

theorem toC_mod_4096 (a : ℕ) : toC (a % 4096) = toC a := by
  refine toC_ext fun j => ?_
  rw [show (4096 : ℕ) = 2 ^ 12 from rfl, Nat.testBit_mod_two_pow, decide_eq_true j.2, Bool.true_and]

theorem toD_mod_4096 (a : ℕ) : toD (a % 4096) = toD a := by
  refine toD_ext fun j => ?_
  rw [show (4096 : ℕ) = 2 ^ 12 from rfl, Nat.testBit_mod_two_pow, decide_eq_true j.2, Bool.true_and]

@[expose] noncomputable def spinOfRow (r : ℕ) : SpinIdx :=
  (boolZ (decide (2048 ≤ r)), π₀ (toC (2 * (r % 2048))))

theorem pi0N_testBit_zero (c : ℕ) : (Model.pi0N c).testBit 0 = false := by
  unfold Model.pi0N
  rw [Nat.testBit_xor]
  cases c.testBit 0 <;> decide

theorem pi0N_even (c : ℕ) : 2 * (Model.pi0N c / 2) = Model.pi0N c := by
  have h := pi0N_testBit_zero c
  rw [Nat.testBit_zero] at h
  simp only [decide_eq_false_iff_not] at h
  omega

theorem toC_two_mul_mod (c : ℕ) : toC (2 * (Model.pi0N c / 2 % 2048)) = toC (Model.pi0N c) := by
  have h1 : 2 * (Model.pi0N c / 2 % 2048) = Model.pi0N c % 4096 := by
    have := pi0N_even c
    omega
  rw [h1, toC_mod_4096]

theorem spinOfRow_rowIdx (η : Bool) (c : ℕ) :
    spinOfRow (Native.rowIdx η c) = (boolZ η, π₀ (toC c)) := by
  have hx : Model.pi0N c / 2 % 2048 < 2048 := Nat.mod_lt _ (by norm_num)
  have hn : Native.pi0N c = Model.pi0N c := by rw [native_pi0N]
  unfold spinOfRow Native.rowIdx
  rw [hn]
  cases η
  · simp only [Bool.false_eq_true, ite_false, zero_add]
    have h1 : decide (2048 ≤ Model.pi0N c / 2 % 2048) = false := by simp; omega
    rw [h1, Nat.mod_eq_of_lt hx, toC_two_mul_mod, π₀_toC_pi0N]
  · simp only [ite_true]
    have h1 : decide (2048 ≤ 2048 + Model.pi0N c / 2 % 2048) = true := by simp
    have h2 : (2048 + Model.pi0N c / 2 % 2048) % 2048 = Model.pi0N c / 2 % 2048 := by omega
    rw [h1, h2, toC_two_mul_mod, π₀_toC_pi0N]


theorem spinOfRow_injective : Function.Injective fun r : Fin 4096 => spinOfRow r := by
  intro r r' h
  simp only [spinOfRow, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have h1' := boolZ_injective h1
  have h3 := congrArg (fun x : C₀ => ((x : C) : Fin 24 → ZMod 2)) h2
  have h4 : toC (2 * (r.val % 2048)) = toC (2 * (r'.val % 2048)) := by
    have e : ∀ k : ℕ, Model.pi0N (2 * k) = 2 * k := fun k => by
      unfold Model.pi0N
      have : (2 * k).testBit 0 = false := by simp [Nat.testBit_zero]
      simp [this]
    apply Subtype.ext
    have h5 := congrArg (fun x : C₀ => (x : C)) h2
    simp only [coe_π₀_toC, e] at h5
    exact congrArg Subtype.val h5
  have h6 := toC_inj (by omega) (by omega) h4
  simp only [decide_eq_decide] at h1'
  apply Fin.ext
  omega

@[expose] noncomputable def spinRowEquiv : Fin 4096 ≃ SpinIdx :=
  Equiv.ofBijective (fun r : Fin 4096 => spinOfRow r)
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨spinOfRow_injective, by
      rw [Fintype.card_fin, card_spinIdx]⟩)

theorem spinRowEquiv_apply (r : Fin 4096) : spinRowEquiv r = spinOfRow r := rfl

@[expose] noncomputable def rowOf (s : SpinIdx) : ℕ := (spinRowEquiv.symm s : ℕ)

theorem rowOf_lt (s : SpinIdx) : rowOf s < 4096 := (spinRowEquiv.symm s).2

theorem spinOfRow_rowOf (s : SpinIdx) : spinOfRow (rowOf s) = s := by
  have := spinRowEquiv.apply_symm_apply s
  rw [spinRowEquiv_apply] at this
  exact this

theorem rowOf_spinOfRow {r : ℕ} (hr : r < 4096) : rowOf (spinOfRow r) = r := by
  have := spinRowEquiv.symm_apply_apply ⟨r, hr⟩
  rw [spinRowEquiv_apply] at this
  exact congrArg Fin.val this

@[expose] noncomputable def eRow (r : ℕ) : SpinIdx → ℚ :=
  if r < 4096 then Pi.single (spinOfRow r) 1 else 0

theorem eRow_apply (r : ℕ) (s : SpinIdx) :
    eRow r s = if r < 4096 ∧ r = rowOf s then 1 else 0 := by
  unfold eRow
  by_cases hr : r < 4096
  · simp only [hr, ite_eq_left, Pi.single_apply, true_and]
    by_cases h : r = rowOf s
    · subst h
      simp [spinOfRow_rowOf]
    · have : s ≠ spinOfRow r := fun e => h (by rw [e, rowOf_spinOfRow hr])
      simp [h, this]
  · simp [hr]

theorem Evec_eq_eRow (η : Bool) (c : ℕ) : Evec η c = eRow (Native.rowIdx η c) := by
  have hlt : Native.rowIdx η c < 4096 := by
    unfold Native.rowIdx
    have : Native.pi0N c / 2 % 2048 < 2048 := Nat.mod_lt _ (by norm_num)
    cases η <;> simp <;> omega
  rw [eRow, ite_eq_left hlt, spinOfRow_rowIdx, Evec, E]


@[expose] def keyOf (p : ℕ) : ℕ × ℕ := (Native.mkCtx ()).keys[p]!

theorem keyOf_lt
    (p : ℕ) (hp : p < 98280) : (keyOf p).1 < 4096 ∧ (keyOf p).2 < 4096 :=
  ⟨(Native.ctx_key_spec p hp).1, (Native.ctx_key_spec p hp).2.1⟩

theorem find_keyOf (p : ℕ) (hp : p < 98280) :
    (Native.mkCtx ()).find (keyOf p).1 (keyOf p).2 = p := (Native.ctx_key_spec p hp).2.2

theorem mkCtx_keys : (Native.mkCtx ()).keys = Native.mkKeys (Native.thetaTab ()) := rfl

theorem mkCtx_th : (Native.mkCtx ()).th = Native.thetaTab () := rfl

theorem mkCtx_tau : (Native.mkCtx ()).tau = Native.mkTauTab () := rfl

theorem keyOf_eq (p : ℕ) (hp : p < 98280) : keyOf p = Native.keyAt (Native.thetaTab ()) p := by
  unfold keyOf
  rw [mkCtx_keys]
  unfold Native.mkKeys
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_map,
    Array.getElem?_range]
  simp [hp]

theorem thetaTab_get (a : ℕ) (ha : a < 4096) : (Native.thetaTab ())[a]! = Model.thetaN a := by
  unfold Native.thetaTab
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_map,
    Array.getElem?_range]
  simp [ha, native_thetaN]

theorem keyOf_pair (p : ℕ) (hp : p < 552) :
    keyOf p = ((if p % 2 = 0 then 0 else 63), Model.dualN (2 ^ (Native.pairTab[p / 2]!).1 |||
      2 ^ (Native.pairTab[p / 2]!).2)) := by
  rw [keyOf_eq p (by omega)]
  unfold Native.keyAt
  simp [hp, native_dualN]

theorem keyOf_odd (p : ℕ) (h1 : 552 ≤ p) (h2 : p < 49704) :
    keyOf p = (Model.oddCode (2 * ((p - 552) / 24)) ((p - 552) % 24),
      Model.thetaN (Model.oddCode (2 * ((p - 552) / 24)) ((p - 552) % 24)) ^^^
        Model.dualN (2 ^ ((p - 552) % 24))) := by
  have hlt := (keyOf_lt p (by omega)).1
  rw [keyOf_eq p (by omega)] at hlt ⊢
  unfold Native.keyAt at hlt ⊢
  have hn : ¬ p < 552 := by omega
  simp only [hn, h2, ite_false, ite_eq_left] at hlt ⊢
  rw [thetaTab_get _ hlt]
  simp [native_oddCode, native_dualN]

theorem keyOf_oct (p : ℕ) (h1 : 49704 ≤ p) (h2 : p < 98280) :
    keyOf p = (Native.octCodeG Native.octTab[(p - 49704) / 64]! Native.evenTab[(p - 49704) % 64]!,
      Model.thetaN (Native.octCodeG Native.octTab[(p - 49704) / 64]!
        Native.evenTab[(p - 49704) % 64]!) ^^^
        Model.dualN (Native.spreadG (Model.wordN Native.octTab[(p - 49704) / 64]!)
          Native.evenTab[(p - 49704) % 64]!)) := by
  have hlt := (keyOf_lt p h2).1
  rw [keyOf_eq p h2] at hlt ⊢
  unfold Native.keyAt at hlt ⊢
  have hn : ¬ p < 552 := by omega
  have hn2 : ¬ p < 49704 := by omega
  simp only [hn, hn2, ite_false] at hlt ⊢
  rw [thetaTab_get _ hlt]
  simp [native_dualN, native_wordN]

end CFSG.Monster.AxisCount
