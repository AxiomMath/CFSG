module

public import CFSG.Monster.AxisCount.DenseGD

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.AxisCount

open CFSG.Monster CFSG.Monster.B CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.ScalarKernel CFSG.Monster.Lifts CFSG.Monster.Visible CFSG.Monster.Xi
  CFSG.Monster.Griess CFSG.Monster.B.Rep4371 Matrix

theorem monoRows_get (rm : Bool → ℕ → Bool × Bool × ℕ) (r : ℕ) (hr : r < 4096) :
    (Native.monoRows rm)[r]! =
      [(Native.rowIdx (rm (Native.rowEta r) (Native.rowC r)).2.1
          (rm (Native.rowEta r) (Native.rowC r)).2.2,
        Native.sgnI (rm (Native.rowEta r) (Native.rowC r)).1)] := by
  unfold Native.monoRows
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_map,
    Array.getElem?_range]
  simp [hr]

theorem row_mono (S : Matrix SpinIdx SpinIdx ℚ) (rm : Bool → ℕ → Bool × Bool × ℕ)
    (hrm : ∀ η c, Evec η c ᵥ* S = sgn (boolZ (rm η c).1) • Evec (rm η c).2.1 (rm η c).2.2)
    (r : ℕ) (hr : r < 4096) :
    (Pi.single (spinOfRow r) (1 : ℚ) : SpinIdx → ℚ) ᵥ* S =
      (((Native.monoRows rm)[r]!).map fun t => ((t.2 : ℚ) / 2 ^ (0 : ℕ)) • eRow t.1).sum := by
  rw [monoRows_get rm r hr]
  have h1 : (Pi.single (spinOfRow r) (1 : ℚ) : SpinIdx → ℚ) =
      Evec (Native.rowEta r) (Native.rowC r) := rfl
  rw [h1, hrm]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, pow_zero,
    div_one, ← Evec_eq_eRow, sgn_boolZ]
  rfl

theorem idG_getD (i j : Fin 24) : Native.idG.getD (i * 24 + j) 0 = if i = j then 1 else 0 := by
  have h : (i : ℕ) * 24 + j < 576 := by omega
  have e1 : ((i : ℕ) * 24 + j) / 24 = i := by omega
  have e2 : ((i : ℕ) * 24 + j) % 24 = j := by omega
  unfold Native.idG
  rw [Native.getD_ofFn _ _ h]
  simp only [e1, e2]
  by_cases hij : i = j
  · subst hij
    simp
  · have : ¬ (i : ℕ) = j := fun e => hij (Fin.ext e)
    simp [hij, this]

theorem gdSpec_rho_aux (q : Model.Pauli) :
    GDSpec ⟨0, Native.idG, Native.tabT (Native.conjPauliN q), Native.tabD (Native.conjPauliN q), 0,
      Native.monoRows (Native.ePauliN q)⟩ (rhoPair (pauliQ q)) := by
  refine ⟨fun i j => ?_, fun y => ?_, fun r hr => ?_⟩
  · show mat (1 : latticeO) i j = _
    rw [mat_one, idG_getD, Matrix.one_apply]
    split_ifs <;> simp
  · have hf : ∀ y, conjQ (rhoPair (pauliQ q)) (pauliQ y) = pauliQ (Native.conjPauliN q y) := by
      intro y
      rw [native_conjPauliN]
      exact conjQ_rhoPair_toQ q y
    exact fastAct_conj _ _ hf y
  · refine row_mono _ _ (fun η c => ?_) r hr
    rw [native_ePauliN]
    exact (congrArg (fun M => Evec η c ᵥ* M) (qmatR_toSC_eq q)).trans (Evec_vecMul_qmatR q η c)

theorem gdSpec_rho (q : Model.Pauli) :
    GDSpec (Native.GD.ofGen (Native.mkCtx ()) (.rho q)) (rhoPair (pauliQ q)) :=
  gdSpec_rho_aux q

theorem xorSum_congr (f g : ℕ → Bool) (n : ℕ) (h : ∀ k < n, f k = g k) :
    Native.xorSum f n = Native.xorSum g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Native.xorSum]
    rw [ih fun k hk => h k (by omega), h n (by omega)]

theorem betaTab_get (p : Array ℕ) (i j : ℕ) (hi : i < 12) (hj : j < 12) :
    (Native.betaTab p)[12 * i + j]! = Native.betaPN p i j := by
  have h : 12 * i + j < 144 := by omega
  rw [Native.getElem!_eq_getD_gen, Native.betaTab, Native.getD_ofFn _ _ h]
  simp only [show (12 * i + j) / 12 = i by omega, show (12 * i + j) % 12 = j by omega]

theorem kappaT_eq (p : Array ℕ) (a : ℕ) :
    Native.kappaT (Native.betaTab p) a = Native.kappaN p a := by
  unfold Native.kappaT Native.kappaN
  refine xorSum_congr _ _ 12 fun i hi => xorSum_congr _ _ 12 fun j hj => ?_
  rw [betaTab_get p i j hi hj]

theorem ePermT_eq (p : Array ℕ) : Native.ePermT p (Native.betaTab p) = Native.ePermN p := by
  funext η c
  unfold Native.ePermT Native.ePermN
  simp only [kappaT_eq]

theorem packN_lt (f : ℕ → Bool) (n : ℕ) : Native.packN f n < 2 ^ n := by
  induction n with
  | zero => simp [Native.packN]
  | succ n ih =>
    simp only [Native.packN]
    refine Nat.or_lt_two_pow (lt_trans ih (Nat.pow_lt_pow_right (by norm_num) (by omega))) ?_
    split_ifs
    · exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    · positivity

theorem permCN_lt (p : Array ℕ) (a : ℕ) : Native.permCN p a < 4096 := by
  unfold Native.permCN Native.coeffN
  exact packN_lt _ 12

theorem thetaTab_get_native (a : ℕ) (ha : a < 4096) :
    (Native.thetaTab ())[a]! = Native.thetaN a := by
  unfold Native.thetaTab
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_map,
    Array.getElem?_range]
  simp [ha]

theorem map_range_congr {α : Type} (n : ℕ) (f g : ℕ → α) (h : ∀ a < n, f a = g a) :
    (Array.range n).map f = (Array.range n).map g := by
  apply Array.ext
  · simp
  · intro i h1 h2
    simp only [Array.getElem_map, Array.getElem_range]
    exact h i (by simpa using h1)

theorem tabTPerm_eq (p : Array ℕ) :
    Native.tabTPerm p (Native.betaTab p) (Native.thetaTab ()) = Native.tabT (Native.conjPermN p) := by
  unfold Native.tabTPerm Native.tabT
  refine map_range_congr 4096 _ _ fun a ha => ?_
  show (Native.kappaT (Native.betaTab p) a, Native.permCN p a,
      (Native.thetaTab ())[Native.permCN p a]! ^^^ Native.permDN p (Native.thetaTab ())[a]!) =
    (false ^^ Native.kappaN p a, Native.permCN p a,
      Native.thetaN (Native.permCN p a) ^^^ Native.permDN p (Native.thetaN a ^^^ 0))
  rw [thetaTab_get_native _ (permCN_lt p a), thetaTab_get_native a ha, kappaT_eq, Nat.xor_zero,
    Bool.false_xor]

theorem tabDPerm_eq (p : Array ℕ) :
    Native.tabDPerm p (Native.thetaTab ()) = Native.tabD (Native.conjPermN p) := by
  unfold Native.tabDPerm Native.tabD
  refine map_range_congr 4096 _ _ fun d hd => ?_
  show (false ^^ Native.kappaN p 0, Native.permCN p 0,
      (Native.thetaTab ())[Native.permCN p 0]! ^^^ Native.permDN p ((Native.thetaTab ())[0]! ^^^ d)) =
    (false ^^ Native.kappaN p 0, Native.permCN p 0,
      Native.thetaN (Native.permCN p 0) ^^^ Native.permDN p (Native.thetaN 0 ^^^ d))
  rw [thetaTab_get_native _ (permCN_lt p 0), thetaTab_get_native 0 (by norm_num)]

theorem ofGen_perm (arr : Array ℕ) :
    Native.GD.ofGen (Native.mkCtx ()) (.perm arr) =
      ⟨0, Native.permG arr, Native.tabT (Native.conjPermN arr), Native.tabD (Native.conjPermN arr), 0,
        Native.monoRows (Native.ePermN arr)⟩ := by
  show (⟨0, Native.permG arr, Native.tabTPerm arr (Native.betaTab arr) (Native.mkCtx ()).th,
    Native.tabDPerm arr (Native.mkCtx ()).th, 0,
    Native.monoRows (Native.ePermT arr (Native.betaTab arr))⟩ : Native.GD) = _
  rw [mkCtx_th, tabTPerm_eq, tabDPerm_eq, ePermT_eq]

@[expose] noncomputable def permPairOf (p : AutPerm) : Pvis := ⟨(sU p, PO p), sU_PO_mem_Pvis p⟩

theorem Pmat_apply (p : Equiv.Perm (Fin 24)) (i j : Fin 24) :
    Pmat p i j = if p i = j then 1 else 0 := by
  have h := congrFun ((single_one_vecMul i (Pmat p)).symm.trans (single_vecMul_Pmat p i)) j
  simp only [Matrix.row_apply, Pi.single_apply] at h
  rw [h]
  by_cases hh : p i = j
  · simp [hh]
  · have : ¬ j = p i := fun e => hh e.symm
    simp [hh, this]

theorem permG_getD (arr : Array ℕ) (i j : Fin 24) :
    (Native.permG arr).getD (i * 24 + j) 0 = if arr[(i : ℕ)]! = j then 1 else 0 := by
  have h : (i : ℕ) * 24 + j < 576 := by omega
  have e1 : ((i : ℕ) * 24 + j) / 24 = i := by omega
  have e2 : ((i : ℕ) * 24 + j) % 24 = j := by omega
  unfold Native.permG
  rw [Native.getD_ofFn _ _ h]
  simp only [e1, e2]

theorem gdSpec_perm_aux (arr : Array ℕ) (p : AutPerm) (hp : RepPerm p arr) :
    GDSpec ⟨0, Native.permG arr, Native.tabT (Native.conjPermN arr), Native.tabD (Native.conjPermN arr),
      0, Native.monoRows (Native.ePermN arr)⟩ (permPairOf p) := by
  refine ⟨fun i j => ?_, fun y => ?_, fun r hr => ?_⟩
  · show Pmat (p : Equiv.Perm (Fin 24)) i j = _
    rw [permG_getD, Pmat_apply]
    have hi : arr[(i : ℕ)]! = (((p : Equiv.Perm (Fin 24)) i : Fin 24) : ℕ) := (hp i).symm
    have key : (arr[(i : ℕ)]! = j) ↔ (p : Equiv.Perm (Fin 24)) i = j := by
      rw [hi]
      exact ⟨fun e => Fin.ext e, fun e => congrArg Fin.val e⟩
    by_cases hij : (p : Equiv.Perm (Fin 24)) i = j
    · rw [ite_eq_left hij, ite_eq_left (key.2 hij)]
      simp
    · rw [ite_eq_right hij, ite_eq_right (fun e => hij (key.1 e))]
      simp
  · have hf : ∀ y, conjQ (permPairOf p) (pauliQ y) = pauliQ (Native.conjPermN arr y) := by
      intro y
      rw [native_conjPermN]
      exact conjQ_perm_toQ p hp y
    exact fastAct_conj _ _ hf y
  · refine row_mono _ _ (fun η c => ?_) r hr
    rw [native_ePermN]
    exact Evec_vecMul_smat p hp η c

theorem gdSpec_perm (arr : Array ℕ) (p : AutPerm) (hp : RepPerm p arr) :
    GDSpec (Native.GD.ofGen (Native.mkCtx ()) (.perm arr)) (permPairOf p) := by
  rw [ofGen_perm]
  exact gdSpec_perm_aux arr p hp

theorem signG_getD (a : ℕ) (i j : Fin 24) :
    (Native.signG a).getD (i * 24 + j) 0 =
      if i = j then Model.sgnI ((Model.wordN a).testBit j) else 0 := by
  have h : (i : ℕ) * 24 + j < 576 := by omega
  have e1 : ((i : ℕ) * 24 + j) / 24 = i := by omega
  have e2 : ((i : ℕ) * 24 + j) % 24 = j := by omega
  unfold Native.signG
  rw [Native.getD_ofFn _ _ h]
  simp only [e1, e2, native_sgnI, native_wordN]
  by_cases hij : i = j
  · subst hij
    simp
  · have : ¬ (i : ℕ) = j := fun e => hij (Fin.ext e)
    simp [hij, this]

theorem gdSpec_sign_aux (a : ℕ) :
    GDSpec ⟨0, Native.signG a, Native.tabT (Native.conjYN a), Native.tabD (Native.conjYN a), 0,
      Native.monoRows (Native.eYN a)⟩ (signPair a) := by
  refine ⟨fun i j => ?_, fun y => ?_, fun r hr => ?_⟩
  · show mat (gO (toC a)) i j = _
    rw [mat_gO, signG_getD, gmat, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      simp [coe_toC_apply, sgn_boolZ]
    · simp [hij]
  · have hf : ∀ y, conjQ (signPair a) (pauliQ y) = pauliQ (Native.conjYN a y) := by
      intro y
      rw [native_conjYN]
      exact conjQ_sign_toQ a y
    exact fastAct_conj _ _ hf y
  · refine row_mono _ _ (fun η c => ?_) r hr
    rw [native_eYN]
    exact Evec_vecMul_Ymat a η c

theorem gdSpec_sign (a : ℕ) :
    GDSpec (Native.GD.ofGen (Native.mkCtx ()) (.sign a)) (signPair a) :=
  gdSpec_sign_aux a

end CFSG.Monster.AxisCount
