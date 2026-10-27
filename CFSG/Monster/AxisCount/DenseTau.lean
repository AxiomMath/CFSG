module

public import CFSG.Monster.AxisCount.DenseTauSum
public import CFSG.Monster.AxisCount.DenseOct
public import CFSG.Monster.AxisCount.DenseXi

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.AxisCount

open CFSG.Monster CFSG.Monster.B CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.B.Rep4371 Matrix

theorem tauTab_w (t : ℕ) (ht : t < 2048) :
    (Native.mkTauTab ()).w[t]! = Native.wordN (2 * t) := by
  simp only [Native.mkTauTab]
  rw [Native.getElem!_eq_getD_gen, Native.getD_ofFn _ _ ht]

theorem tauTab_pb (t : ℕ) (ht : t < 2048) :
    (Native.mkTauTab ()).pb[t]! = Native.pN (2 * t) := by
  simp only [Native.mkTauTab]
  rw [Native.getElem!_eq_getD_gen, Native.getD_ofFn _ _ ht]

theorem tauTab_S (k : ℕ) (hk : k < 4096) :
    (Native.mkTauTab ()).S[k]! =
      Native.octSign Native.evenTab[k / 64]! Native.evenTab[k % 64]! := by
  simp only [Native.mkTauTab]
  rw [Native.getElem!_eq_getD_gen, Native.getD_ofFn _ _ hk]

@[expose] noncomputable def cc (t : ℕ) : C₀ := π₀ (toC (2 * t))

theorem pi0N_two_mul (t : ℕ) : Model.pi0N (2 * t) = 2 * t := by
  unfold Model.pi0N
  have : (2 * t).testBit 0 = false := by simp [Nat.testBit_zero]
  simp [this]

theorem coe_cc (t : ℕ) : ((cc t : C₀) : C) = toC (2 * t) := by
  rw [cc, coe_π₀_toC, pi0N_two_mul]

theorem zmod2_cases' : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

theorem sgn_mul_self_zmod (x : ZMod 2) : sgn x * sgn x = 1 := by
  rcases zmod2_cases' x with rfl | rfl <;> norm_num [sgn]

theorem sgn_cc (t i : ℕ) (hi : i < 24) :
    sgn (((cc t : C) : Fin 24 → ZMod 2) (finOf i)) =
      ((Native.sgnI ((Native.wordN (2 * t)).testBit i) : ℤ) : ℚ) := by
  rw [coe_cc, coe_toC_apply, finOf_val i hi, sgn_boolZ, native_sgnI, native_wordN]

theorem sgn_P_cc (t : ℕ) :
    sgn (P ((cc t : C) : Fin 24 → ZMod 2)) = ((Native.sgnI (Native.pN (2 * t)) : ℤ) : ℚ) := by
  rw [coe_cc, P_toC, sgn_boolZ, native_sgnI, native_pN]

theorem spinOfRow_lo (t : ℕ) (ht : t < 2048) : spinOfRow t = (0, cc t) := by
  have h1 : decide (2048 ≤ t) = false := by simp; omega
  unfold spinOfRow cc
  rw [h1, Nat.mod_eq_of_lt ht]
  rfl

theorem spinOfRow_hi (t : ℕ) (ht : t < 2048) : spinOfRow (2048 + t) = (1, cc t) := by
  have h1 : decide (2048 ≤ 2048 + t) = true := by simp
  have h2 : (2048 + t) % 2048 = t := by omega
  unfold spinOfRow cc
  rw [h1, h2]
  rfl

theorem fbasis_odd0 (t i : ℕ) (ht : t < 2048) (hi : i < 24) :
    fbasis (852 + 24 * t + i) = tbasis (.inr (.inr (.inl (cc t, finOf i, 0)))) := by
  have h1 : 852 + 24 * t + i = 300 + (552 + 24 * t + i) := by omega
  rw [h1, fbasis_X _ (by omega), xvec, tbasis_odd_zero]
  have hn : (2 * t).testBit 0 = false := by simp [Nat.testBit_zero]
  have e := pauliQ_odd' (2 * t) hn (finOf i)
  have hk := keyOf_odd (552 + 24 * t + i) (by omega) (by omega)
  have e1 : (552 + 24 * t + i - 552) / 24 = t := by omega
  have e2 : (552 + 24 * t + i - 552) % 24 = i := by omega
  rw [e1, e2] at hk
  rw [hk]
  have : pauliQ (false, Model.oddCode (2 * t) i,
      Model.thetaN (Model.oddCode (2 * t) i) ^^^ Model.dualN (2 ^ i)) = rOdd (cc t) (finOf i) := by
    have := e
    rw [finOf_val i hi] at this
    exact this
  exact congrArg (fun r => inX (Xlift r)) this

theorem sgnI_mul_self (b : Bool) :
    ((Native.sgnI b : ℤ) : ℚ) * ((Native.sgnI b : ℤ) : ℚ) = 1 := by
  cases b <;> norm_num [Native.sgnI]

theorem tbasis_odd1 (t i : ℕ) (ht : t < 2048) (hi : i < 24) :
    tbasis (.inr (.inr (.inl (cc t, finOf i, 1)))) =
      ((Native.sgnI ((Native.wordN (2 * t)).testBit i) : ℤ) : ℚ) •
        fbasis (98580 + 24 * (2048 + t) + i) := by
  rw [tbasis_odd_one, fbasis_W _ _ hi, wvecB, spinOfRow_hi t ht, sgn_cc t i hi]
  simp only [smul_inW]
  rfl

theorem tbasis_odd2 (t i : ℕ) (ht : t < 2048) (hi : i < 24) :
    tbasis (.inr (.inr (.inl (cc t, finOf i, 2)))) =
      ((Native.sgnI (Native.pN (2 * t)) : ℤ) : ℚ) • fbasis (98580 + 24 * t + i) := by
  rw [tbasis_odd_two, fbasis_W _ _ hi, wvecB, spinOfRow_lo t ht, sgn_P_cc t]
  simp only [smul_inW]
  rfl

theorem fbasis_Whi (t i : ℕ) (ht : t < 2048) (hi : i < 24) :
    fbasis (98580 + 24 * (2048 + t) + i) =
      ((Native.sgnI ((Native.wordN (2 * t)).testBit i) : ℤ) : ℚ) •
        tbasis (.inr (.inr (.inl (cc t, finOf i, 1)))) := by
  rw [tbasis_odd1 t i ht hi, smul_smul, sgnI_mul_self, one_smul]

theorem fbasis_Wlo (t i : ℕ) (ht : t < 2048) (hi : i < 24) :
    fbasis (98580 + 24 * t + i) =
      ((Native.sgnI (Native.pN (2 * t)) : ℤ) : ℚ) •
        tbasis (.inr (.inr (.inl (cc t, finOf i, 2)))) := by
  rw [tbasis_odd2 t i ht hi, smul_smul, sgnI_mul_self, one_smul]

theorem tauImg_single {p a : ℕ} {n : ℤ} (h : tauL p = [(a, n)]) :
    tauImg p = (n : ℚ) • fbasis a := by
  rw [tauImg, h]
  simp

theorem tauL_odd (t i : ℕ) (ht : t < 2048) (hi : i < 24) :
    tauL (852 + 24 * t + i) = [(98580 + 24 * (2048 + t) + i,
      8 * Native.sgnI ((Native.wordN (2 * t)).testBit i))] := by
  have e1 : (852 + 24 * t + i - 852) / 24 = t := by omega
  have e2 : (852 + 24 * t + i - 852) % 24 = i := by omega
  unfold tauL Native.tauT
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_left (by omega), e1, e2, mkCtx_tau, tauTab_w t ht]
  rw [mul_comm (2048 + t) 24]

theorem tauL_Wlo (t i : ℕ) (ht : t < 2048) (hi : i < 24) :
    tauL (98580 + 24 * t + i) =
      [(852 + 24 * t + i, 8 * Native.sgnI (Native.pN (2 * t)))] := by
  have e1 : (98580 + 24 * t + i - 98580) / 24 = t := by omega
  have e2 : (98580 + 24 * t + i - 98580) % 24 = i := by omega
  unfold tauL Native.tauT
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega), e1, e2, mkCtx_tau,
    tauTab_pb t ht]

theorem tauL_Whi (t i : ℕ) (ht : t < 2048) (hi : i < 24) :
    tauL (98580 + 24 * (2048 + t) + i) =
      [(98580 + 24 * t + i, 8 * Native.sgnI ((Native.wordN (2 * t)).testBit i) *
        Native.sgnI (Native.pN (2 * t)))] := by
  have e1 : (98580 + 24 * (2048 + t) + i - 98580) / 24 = 2048 + t := by omega
  have e2 : (98580 + 24 * (2048 + t) + i - 98580) % 24 = i := by omega
  have e3 : 2048 + t - 2048 = t := by omega
  unfold tauL Native.tauT
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), e1, e2, e3,
    mkCtx_tau, tauTab_w t ht, tauTab_pb t ht, mul_comm 24 t]

theorem tauBasis_odd (t i : ℕ) (ht : t < 2048) (hi : i < 24) :
    tauB (fbasis (852 + 24 * t + i)) = (1 / 8 : ℚ) • tauImg (852 + 24 * t + i) := by
  have e0 : (0 : Fin 3) + 1 = 1 := rfl
  rw [fbasis_odd0 t i ht hi, tauB_odd (cc t) (finOf i) 0, e0, tbasis_odd1 t i ht hi,
    tauImg_single (tauL_odd t i ht hi), smul_smul]
  refine congrArg (· • fbasis (98580 + 24 * (2048 + t) + i)) ?_
  push_cast
  ring

theorem tauBasis_Whi (t i : ℕ) (ht : t < 2048) (hi : i < 24) :
    tauB (fbasis (98580 + 24 * (2048 + t) + i)) =
      (1 / 8 : ℚ) • tauImg (98580 + 24 * (2048 + t) + i) := by
  have e2 : (1 : Fin 3) + 1 = 2 := rfl
  rw [fbasis_Whi t i ht hi, map_smul, tauB_odd (cc t) (finOf i) 1, e2, tbasis_odd2 t i ht hi,
    tauImg_single (tauL_Whi t i ht hi), smul_smul, smul_smul]
  refine congrArg (· • fbasis (98580 + 24 * t + i)) ?_
  push_cast
  ring

theorem tauBasis_Wlo (t i : ℕ) (ht : t < 2048) (hi : i < 24) :
    tauB (fbasis (98580 + 24 * t + i)) = (1 / 8 : ℚ) • tauImg (98580 + 24 * t + i) := by
  have e0 : (2 : Fin 3) + 1 = 0 := rfl
  rw [fbasis_Wlo t i ht hi, map_smul, tauB_odd (cc t) (finOf i) 2, e0, ← fbasis_odd0 t i ht hi,
    tauImg_single (tauL_Wlo t i ht hi), smul_smul]
  refine congrArg (· • fbasis (852 + 24 * t + i)) ?_
  push_cast
  ring

theorem tauImg_two {p : ℕ} {a₁ a₂ : ℕ} {n₁ n₂ : ℤ} (h : tauL p = [(a₁, n₁), (a₂, n₂)]) :
    tauImg p = (n₁ : ℚ) • fbasis a₁ + (n₂ : ℚ) • fbasis a₂ := by
  rw [tauImg, h]
  simp

theorem tauImg_three {p : ℕ} {a₁ a₂ a₃ : ℕ} {n₁ n₂ n₃ : ℤ}
    (h : tauL p = [(a₁, n₁), (a₂, n₂), (a₃, n₃)]) :
    tauImg p = (n₁ : ℚ) • fbasis a₁ + (n₂ : ℚ) • fbasis a₂ + (n₃ : ℚ) • fbasis a₃ := by
  rw [tauImg, h]
  simp [add_assoc]

theorem tauBasis_diag (p : ℕ) (hp : p < 24) :
    tauB (fbasis p) = (1 / 8 : ℚ) • tauImg p := by
  have hz : zOf p = s(finOf p, finOf p) := by
    unfold zOf Native.aPos
    rw [ite_eq_left hp]
  have hf : fbasis p = tbasis (.inl (finOf p)) := by
    rw [fbasis_A p (by omega), avec, hz, tbasis_diag]
  have hL : tauL p = [(p, 8)] := by
    unfold tauL Native.tauT
    rw [ite_eq_left hp]
  rw [tauImg_single hL, hf, tauB_diag]
  push_cast
  module

theorem inX_sub (a b : SpaceX) : inX a - inX b = inX (a - b) := by
  simp [Prod.mk_sub_mk]

theorem inX_add (a b : SpaceX) : inX a + inX b = inX (a + b) := by
  simp [Prod.mk_add_mk]

theorem tauL_pairA (tp : ℕ) (h : tp < 276) :
    tauL (24 + tp) = [(300 + 2 * tp, 8), (300 + 2 * tp + 1, -8)] := by
  unfold tauL Native.tauT
  rw [ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel_left]

theorem tauL_pairX (tp : ℕ) (h : tp < 276) :
    tauL (300 + 2 * tp) = [(24 + tp, 4), (300 + 2 * tp, 4), (300 + 2 * tp + 1, 4)] := by
  have e1 : (300 + 2 * tp - 300) / 2 = tp := by omega
  have e2 : (300 + 2 * tp - 300) % 2 = 0 := by omega
  unfold tauL Native.tauT
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
    e1]

theorem tauL_pairXp (tp : ℕ) (h : tp < 276) :
    tauL (300 + 2 * tp + 1) = [(24 + tp, 4), (300 + 2 * tp, -4), (300 + 2 * tp + 1, -4)] := by
  have e1 : (300 + 2 * tp + 1 - 300) / 2 = tp := by omega
  have e2 : ¬ (300 + 2 * tp + 1 - 300) % 2 = 0 := by omega
  unfold tauL Native.tauT
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_right e2, e1]

@[expose] def ltpAux (a b : ℕ) (h1 : a < b) (h2 : b < 24) : LtPair :=
  ⟨(⟨a, lt_trans h1 h2⟩, ⟨b, h2⟩), Fin.mk_lt_mk.2 h1⟩

theorem pairData (tp : ℕ) (h : tp < 276) :
    ∃ (a b : ℕ), a < b ∧ b < 24 ∧ Native.pairTab[tp]! = (a, b) := by
  obtain ⟨h1, h2, -⟩ := Native.pairTab_spec tp h
  exact ⟨_, _, h1, h2, Prod.mk.eta.symm⟩

section PairAux

variable {tp a b : ℕ} (h1 : a < b) (h2 : b < 24) (htp : tp < 276)
  (hab : Native.pairTab[tp]! = (a, b))

include hab h1 h2 htp

theorem fbasis_pair0_aux : fbasis (24 + tp) = tbasis (.inr (.inl (ltpAux a b h1 h2, 0))) := by
  have hz : zOf (24 + tp) = s((ltpAux a b h1 h2).1.1, (ltpAux a b h1 h2).1.2) := by
    unfold zOf Native.aPos
    rw [ite_eq_right (by omega), Nat.add_sub_cancel_left, hab]
    exact congrArg₂ (fun x y => s(x, y)) (Fin.ext (finOf_val _ (lt_trans h1 h2)))
      (Fin.ext (finOf_val _ h2))
  rw [fbasis_A _ (by omega), avec, hz, tbasis_pair_zero]

theorem xvec_minus_aux :
    xvec (2 * tp) = inX (Xlift (rMinus (ltpAux a b h1 h2).1.1 (ltpAux a b h1 h2).1.2)) := by
  have hne : (ltpAux a b h1 h2).1.1 ≠ (ltpAux a b h1 h2).1.2 := fun e => by
    have := congrArg Fin.val e
    simp only [ltpAux] at this
    omega
  have hk := keyOf_pair (2 * tp) (by omega)
  rw [ite_eq_left (by omega), show 2 * tp / 2 = tp by omega, hab] at hk
  have e := pauliQ_minus hne
  unfold xvec
  rw [hk]
  exact congrArg (fun r => inX (Xlift r)) e

theorem xvec_plus_aux :
    xvec (2 * tp + 1) = inX (Xlift (rPlus (ltpAux a b h1 h2).1.1 (ltpAux a b h1 h2).1.2)) := by
  have hne : (ltpAux a b h1 h2).1.1 ≠ (ltpAux a b h1 h2).1.2 := fun e => by
    have := congrArg Fin.val e
    simp only [ltpAux] at this
    omega
  have hk := keyOf_pair (2 * tp + 1) (by omega)
  rw [ite_eq_right (by omega), show (2 * tp + 1) / 2 = tp by omega, hab] at hk
  have e := pauliQ_plus hne
  unfold xvec
  rw [hk]
  exact congrArg (fun r => inX (Xlift r)) e

omit h1 h2 hab in
theorem fbasis_X_even : fbasis (300 + 2 * tp) = xvec (2 * tp) := fbasis_X (2 * tp) (by omega)

omit h1 h2 hab in
theorem fbasis_X_odd : fbasis (300 + 2 * tp + 1) = xvec (2 * tp + 1) :=
  fbasis_X (2 * tp + 1) (by omega)

theorem tbasis_pair1_aux :
    tbasis (.inr (.inl (ltpAux a b h1 h2, 1))) = fbasis (300 + 2 * tp) - fbasis (300 + 2 * tp + 1) := by
  rw [tbasis_pair_one, fbasis_X_even htp, fbasis_X_odd htp,
    xvec_minus_aux h1 h2 htp hab, xvec_plus_aux h1 h2 htp hab, inX_sub]

theorem tbasis_pair2_aux :
    tbasis (.inr (.inl (ltpAux a b h1 h2, 2))) = fbasis (300 + 2 * tp) + fbasis (300 + 2 * tp + 1) := by
  rw [tbasis_pair_two, fbasis_X_even htp, fbasis_X_odd htp,
    xvec_minus_aux h1 h2 htp hab, xvec_plus_aux h1 h2 htp hab, inX_add]

theorem tauBasis_pairA_aux : tauB (fbasis (24 + tp)) = (1 / 8 : ℚ) • tauImg (24 + tp) := by
  have e0 : (0 : Fin 3) + 1 = 1 := rfl
  rw [fbasis_pair0_aux h1 h2 htp hab, tauB_pair (ltpAux a b h1 h2) 0, e0,
    tbasis_pair1_aux h1 h2 htp hab, tauImg_two (tauL_pairA tp htp)]
  push_cast
  module

theorem tauBasis_pairX_aux : tauB (fbasis (300 + 2 * tp)) = (1 / 8 : ℚ) • tauImg (300 + 2 * tp) := by
  have e1 : (1 : Fin 3) + 1 = 2 := rfl
  have e2 : (2 : Fin 3) + 1 = 0 := rfl
  have hx : fbasis (300 + 2 * tp) = (1 / 2 : ℚ) •
      (tbasis (.inr (.inl (ltpAux a b h1 h2, 1))) + tbasis (.inr (.inl (ltpAux a b h1 h2, 2)))) := by
    rw [tbasis_pair1_aux h1 h2 htp hab, tbasis_pair2_aux h1 h2 htp hab]
    module
  rw [hx, map_smul, map_add, tauB_pair (ltpAux a b h1 h2) 1, tauB_pair (ltpAux a b h1 h2) 2, e1, e2,
    tauImg_three (tauL_pairX tp htp), tbasis_pair2_aux h1 h2 htp hab, ← fbasis_pair0_aux h1 h2 htp hab]
  push_cast
  module

theorem tauBasis_pairXp_aux :
    tauB (fbasis (300 + 2 * tp + 1)) = (1 / 8 : ℚ) • tauImg (300 + 2 * tp + 1) := by
  have e1 : (1 : Fin 3) + 1 = 2 := rfl
  have e2 : (2 : Fin 3) + 1 = 0 := rfl
  have hx : fbasis (300 + 2 * tp + 1) = (1 / 2 : ℚ) •
      (tbasis (.inr (.inl (ltpAux a b h1 h2, 2))) - tbasis (.inr (.inl (ltpAux a b h1 h2, 1)))) := by
    rw [tbasis_pair1_aux h1 h2 htp hab, tbasis_pair2_aux h1 h2 htp hab]
    module
  rw [hx, map_smul, map_sub, tauB_pair (ltpAux a b h1 h2) 1, tauB_pair (ltpAux a b h1 h2) 2, e1, e2,
    tauImg_three (tauL_pairXp tp htp), tbasis_pair2_aux h1 h2 htp hab,
    ← fbasis_pair0_aux h1 h2 htp hab]
  push_cast
  module

end PairAux

theorem tauBasis_pairA (tp : ℕ) (h : tp < 276) :
    tauB (fbasis (24 + tp)) = (1 / 8 : ℚ) • tauImg (24 + tp) := by
  obtain ⟨a, b, h1, h2, hab⟩ := pairData tp h
  exact tauBasis_pairA_aux h1 h2 h hab

theorem tauBasis_pairX (tp : ℕ) (h : tp < 276) :
    tauB (fbasis (300 + 2 * tp)) = (1 / 8 : ℚ) • tauImg (300 + 2 * tp) := by
  obtain ⟨a, b, h1, h2, hab⟩ := pairData tp h
  exact tauBasis_pairX_aux h1 h2 h hab

theorem tauBasis_pairXp (tp : ℕ) (h : tp < 276) :
    tauB (fbasis (300 + 2 * tp + 1)) = (1 / 8 : ℚ) • tauImg (300 + 2 * tp + 1) := by
  obtain ⟨a, b, h1, h2, hab⟩ := pairData tp h
  exact tauBasis_pairXp_aux h1 h2 h hab

theorem fbasis_oct (o q : ℕ) (ho : o < 759) (hq : q < 64) :
    fbasis (50004 + 64 * o + q) = tbasis (.inr (.inr (.inr ⟨octW o ho, octCls o ho q⟩))) := by
  have hp : 50004 + 64 * o + q = 300 + (49704 + 64 * o + q) := by ring
  rw [hp, fbasis_X _ (by omega)]
  have hk := keyOf_oct (49704 + 64 * o + q) (by omega) (by omega)
  have e1 : (49704 + 64 * o + q - 49704) / 64 = o := by omega
  have e2 : (49704 + 64 * o + q - 49704) % 64 = q := by omega
  rw [e1, e2] at hk
  have hl := evenTab_lt q hq
  have hsub := octSetG_subset o ho _ (by omega : Native.evenTab[q]! < 256)
  have hev := octSetG_even o ho q hq
  unfold octCls
  rw [tbasis_oct_cls hsub hev]
  unfold xvec
  rw [hk]
  exact congrArg (fun r => inX (Xlift r)) (pauliQ_octG Native.octTab[o]! Native.evenTab[q]!)

theorem tauL_oct (o q : ℕ) (ho : o < 759) (hq : q < 64) :
    tauL (50004 + 64 * o + q) = (List.range 64).map fun q' =>
      (50004 + 64 * o + q', Native.octSign Native.evenTab[q]! Native.evenTab[q']!) := by
  have e1 : (50004 + 64 * o + q - 50004) / 64 = o := by omega
  have e2 : (50004 + 64 * o + q - 50004) % 64 = q := by omega
  unfold tauL Native.tauT
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_left (by omega), e1, e2, mkCtx_tau]
  refine List.map_congr_left fun q' hq' => ?_
  have hq'' := List.mem_range.1 hq'
  have h1 : q * 64 + q' < 4096 := by omega
  have e3 : (q * 64 + q') / 64 = q := by omega
  have e4 : (q * 64 + q') % 64 = q' := by omega
  have := tauTab_S (q * 64 + q') h1
  rw [e3, e4] at this
  rw [this, mul_comm o 64]

theorem tauBasis_oct (o q : ℕ) (ho : o < 759) (hq : q < 64) :
    tauB (fbasis (50004 + 64 * o + q)) = (1 / 8 : ℚ) • tauImg (50004 + 64 * o + q) := by
  rw [fbasis_oct o q ho hq, tauB_oct, ← Equiv.sum_comp (Equiv.ofBijective _ (octCls_bijective o ho))]
  rw [tauImg, tauL_oct o q ho hq, List.map_map, sum_map_range, Finset.smul_sum, Finset.sum_range]
  refine Finset.sum_congr rfl fun q' _ => ?_
  have h1 := octHD_octCls o ho q q' hq q'.2
  simp only [Equiv.ofBijective_apply, Function.comp_apply]
  rw [h1, fbasis_oct o q' ho q'.2, smul_smul]
  refine congrArg (· • tbasis (.inr (.inr (.inr ⟨octW o ho, octCls o ho q'⟩)))) ?_
  ring

theorem tauBasis : TauBasis := by
  intro p hp
  by_cases h1 : p < 24
  · exact tauBasis_diag p h1
  by_cases h2 : p < 300
  · obtain ⟨tp, htp⟩ : ∃ tp, p = 24 + tp := ⟨p - 24, by omega⟩
    subst htp
    exact tauBasis_pairA tp (by omega)
  by_cases h3 : p < 852
  · obtain ⟨tp, htp | htp⟩ := Nat.even_or_odd' (p - 300)
    · have e : p = 300 + 2 * tp := by omega
      subst e
      exact tauBasis_pairX tp (by omega)
    · have e : p = 300 + 2 * tp + 1 := by omega
      subst e
      exact tauBasis_pairXp tp (by omega)
  by_cases h4 : p < 50004
  · have e : p = 852 + 24 * ((p - 852) / 24) + (p - 852) % 24 := by omega
    rw [e]
    exact tauBasis_odd _ _ (by omega) (by omega)
  by_cases h5 : p < 98580
  · have e : p = 50004 + 64 * ((p - 50004) / 64) + (p - 50004) % 64 := by omega
    rw [e]
    exact tauBasis_oct _ _ (by omega) (by omega)
  by_cases h6 : p < 98580 + 24 * 2048
  · have e : p = 98580 + 24 * ((p - 98580) / 24) + (p - 98580) % 24 := by omega
    rw [e]
    exact tauBasis_Wlo _ _ (by omega) (by omega)
  · have e : p = 98580 + 24 * (2048 + ((p - 98580) / 24 - 2048)) + (p - 98580) % 24 := by omega
    rw [e]
    exact tauBasis_Whi _ _ (by omega) (by omega)

theorem interp_applyTau (v : Native.DVec) :
    interp (Native.applyTau (Native.mkCtx ()) v) = tauB (interp v) :=
  interp_applyTau_of tauBasis v

end CFSG.Monster.AxisCount
