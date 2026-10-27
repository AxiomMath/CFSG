module

public import CFSG.Monster.Existence.ELevelDef
public import CFSG.Monster.B.TwoA.Census.CosetEnumBits

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.B CFSG.Monster.B.Short
  CFSG.Monster.B.Rep4371 CFSG.Monster.VisCert CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel
  CFSG.Monster.B.TwoA.Census

@[expose] noncomputable def vecX (x : ℕ) : L2 := phi0 (toC x, toD (x >>> 12))

@[expose] def bX (x y : ℕ) : Bool := Model.pairN x (y >>> 12) ^^ Model.pairN y (x >>> 12)

theorem vecX_xor (x y : ℕ) : vecX (x ^^^ y) = vecX x + vecX y := by
  unfold vecX
  rw [Nat.shiftRight_xor_distrib, toC_xor, toD_xor]
  exact phi0.map_add (toC x, toD (x >>> 12)) (toC y, toD (y >>> 12))

theorem vecX_zero : vecX 0 = 0 := by
  unfold vecX
  rw [Nat.zero_shiftRight, toC_zero, toD_zero]
  exact phi0.map_zero

theorem bL_vecX (x y : ℕ) : bL (vecX x) (vecX y) = boolZ (bX x y) := by
  unfold vecX bX
  rw [bL_phi0, boolZ_xor, pair_toC_toD, pair_toC_toD]

theorem toC_mod_4096 (a : ℕ) : toC (a % 4096) = toC a :=
  toC_ext fun j => by
    rw [show (4096 : ℕ) = 2 ^ 12 from rfl, Nat.testBit_mod_two_pow, decide_eq_true j.2,
      Bool.true_and]

theorem toD_mod_4096 (a : ℕ) : toD (a % 4096) = toD a :=
  toD_ext fun j => by
    rw [show (4096 : ℕ) = 2 ^ 12 from rfl, Nat.testBit_mod_two_pow, decide_eq_true j.2,
      Bool.true_and]

@[expose] def packP (y : Model.Pauli) : ℕ := y.2.1 % 4096 + 4096 * (y.2.2 % 4096)

theorem testBit_add_mul_4096 (a e j : ℕ) (hj : j < 12) :
    (a % 4096 + 4096 * e).testBit j = a.testBit j := by
  simp only [Nat.testBit_eq_decide_div_mod_eq]
  interval_cases j <;> simp <;> omega

theorem shiftRight_add_mul_4096 (a e : ℕ) : (a % 4096 + 4096 * e) >>> 12 = e := by
  rw [Nat.shiftRight_eq_div_pow]
  have : (2 : ℕ) ^ 12 = 4096 := by norm_num
  rw [this]
  omega

theorem vecX_packP (y : Model.Pauli) : vecX (packP y) = phi0 (toC y.2.1, toD y.2.2) := by
  unfold vecX packP
  rw [shiftRight_add_mul_4096, toD_mod_4096]
  have h : toC (y.2.1 % 4096 + 4096 * (y.2.2 % 4096)) = toC y.2.1 :=
    toC_ext fun j => testBit_add_mul_4096 _ _ _ j.2
  rw [h]

@[expose] def pauliOf (x : ℕ) : Model.Pauli := (false, x, x >>> 12)

theorem coordOf_pauliQ (y : Model.Pauli) : coordOf (pauliQ y) = (toC y.2.1, toD y.2.2) :=
  Griess.coordOf_spinEquiv _

theorem phi0_coordOf_pauliOf (x : ℕ) : phi0 (coordOf (pauliQ (pauliOf x))) = vecX x := by
  rw [coordOf_pauliQ]
  rfl

@[expose] def actP (tt td : Array Model.Pauli) (x : ℕ) : Model.Pauli :=
  Model.Pauli.mul tt[x % 4096]! td[(x >>> 12) % 4096]!

@[expose] def kapX (tt td : Array Model.Pauli) (x : ℕ) : ℕ := packP (actP tt td x)

@[expose] def csX (tt td : Array Model.Pauli) (x : ℕ) : Bool := (actP tt td x).1

theorem conjQ_pauliOf
    (i x : ℕ) :
    conjQ (cosetPair i) (pauliQ (pauliOf x)) = pauliQ (actP (tT i) (tD i) x) := by
  have e0 : pauliQ (pauliOf x) = pauliQ (false, 0, 0) * pauliQ (false, x % 2 ^ 12, 0) *
      pauliQ (false, 0, (x >>> 12) % 2 ^ 12) := by
    rw [pauliQ_mod_a false x 0, pauliQ_mod_d false 0 (x >>> 12)]
    exact pauliQ_split false x (x >>> 12)
  have h1 : conjQ (cosetPair i) (pauliQ (false, x % 2 ^ 12, 0)) =
      pauliQ ((tT i)[x % 2 ^ 12]!) := by
    rw [conjQ_cosetPair, tT_get i (Nat.mod_lt _ (by norm_num))]
  have h2 : conjQ (cosetPair i) (pauliQ (false, 0, (x >>> 12) % 2 ^ 12)) =
      pauliQ ((tD i)[(x >>> 12) % 2 ^ 12]!) := by
    rw [conjQ_cosetPair, tD_get i (Nat.mod_lt _ (by norm_num))]
  rw [e0, map_mul, map_mul]
  simp only [pauliQ_false_zero, map_one, one_mul, h1, h2]
  rw [← pauliQ_mul]
  rfl

theorem modTwoEnd_vecX
    (i x : ℕ) :
    modTwoEnd (cosetPair i).1.2 (vecX x) = vecX (kapX (tT i) (tD i) x) := by
  have h := phi0_conjQ (cosetPair i) (pauliQ (pauliOf x))
  rw [conjQ_pauliOf, phi0_coordOf_pauliOf, coordOf_pauliQ] at h
  rw [← h, kapX, vecX_packP]

@[expose] def MX (tt td : Array Model.Pauli) (x : ℕ) : ℕ := x ^^^ kapX tt td x

theorem vecX_MX
    (i x : ℕ) :
    vecX (MX (tT i) (tD i) x) =
      (modTwoEnd (cosetPair i).1.2 - 1 : Module.End (ZMod 2) L2) (vecX x) := by
  rw [MX, vecX_xor, ← modTwoEnd_vecX, LinearMap.sub_apply, Module.End.one_apply, sub_eq_add_neg,
    ZModModule.neg_eq_self, add_comm]

@[expose] def rankPts (i : ℕ) : List ℕ × List ℕ :=
  if i = 1 then ([1, 4, 64, 128, 256], [4, 1, 128, 64, 512])
  else if i = 2 then ([1, 2, 4, 8, 16], [2, 322, 387, 130, 66])
  else ([1, 2, 4, 8, 16], [66, 448, 64, 129, 320])

@[expose] def rankOKT (tt td : Array Model.Pauli) (i : ℕ) : Bool :=
  let pts := rankPts i
  (List.range 5).all fun m => (List.range 5).all fun j =>
    bX (pts.2.getD m 0) (MX tt td (pts.1.getD j 0)) == decide (m = j)

@[expose] def rankOK (i : ℕ) : Bool := rankOKT (tT i) (tD i) i

theorem rankLB
    {i : ℕ} (h : rankOK i = true) :
    5 ≤ Module.finrank (ZMod 2)
      (LinearMap.range (modTwoEnd (cosetPair i).1.2 - 1 : Module.End (ZMod 2) L2)) := by
  set N : Module.End (ZMod 2) L2 := modTwoEnd (cosetPair i).1.2 - 1 with hN
  let y : Fin 5 → L2 := fun j => vecX (MX (tT i) (tD i) ((rankPts i).1.getD j 0))
  let z : Fin 5 → L2 := fun m => vecX ((rankPts i).2.getD m 0)
  have hyN : ∀ j, y j ∈ LinearMap.range N := fun j => ⟨_, (vecX_MX i _).symm⟩
  have hpair : ∀ m j : Fin 5, bL (z m) (y j) = if m = j then 1 else 0 := by
    intro m j
    have h1 := List.all_eq_true.1 h (m : ℕ) (List.mem_range.2 m.2)
    have h2 := List.all_eq_true.1 h1 (j : ℕ) (List.mem_range.2 j.2)
    rw [beq_iff_eq] at h2
    change bL (vecX _) (vecX _) = _
    rw [bL_vecX, h2, boolZ_decide]
    simp only [Fin.ext_iff]
  have hli : LinearIndependent (ZMod 2) y := by
    rw [Fintype.linearIndependent_iff]
    intro g hg m
    have := congrArg (bL (z m)) hg
    rw [map_sum, map_zero] at this
    simp only [map_smul, hpair, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true] at this
    exact this
  have hli' : LinearIndependent (ZMod 2) (fun j => (⟨y j, hyN j⟩ : LinearMap.range N)) :=
    LinearIndependent.of_comp (LinearMap.range N).subtype hli
  simpa using hli'.fintype_card_le_finrank

theorem finrank_range_conj (g : GLV) (N : Module.End (ZMod 2) L2) :
    Module.finrank (ZMod 2) (LinearMap.range ((g : Module.End (ZMod 2) L2) * N *
      ((g⁻¹ : GLV) : Module.End (ZMod 2) L2))) = Module.finrank (ZMod 2) (LinearMap.range N) := by
  have hb : LinearMap.range (((g⁻¹ : GLV) : Module.End (ZMod 2) L2)) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    exact ⟨(g : Module.End (ZMod 2) L2) y, by
      rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel]
      rfl⟩
  rw [mul_assoc, Module.End.mul_eq_comp, Module.End.mul_eq_comp, LinearMap.range_comp,
    LinearMap.range_comp_of_range_eq_top _ hb]
  exact (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) L2 g).finrank_map_eq _

theorem rankSpec_of_check
    (hok : ∀ i ∈ ({1, 2, 6} : Finset ℕ), rankOK i = true) : RankSpec := by
  intro u hu huu hu1
  obtain ⟨i, hi, g, -, hgi⟩ := exists_conj_three hu huu hu1
  have h1 := rankLB (hok i hi)
  have hmono : ((monoN i : GLV) : Module.End (ZMod 2) L2) = modTwoEnd (cosetPair i).1.2 := rfl
  have hu' : (u : Module.End (ZMod 2) L2) - 1 = (g : Module.End (ZMod 2) L2) *
      (modTwoEnd (cosetPair i).1.2 - 1) * ((g⁻¹ : GLV) : Module.End (ZMod 2) L2) := by
    have hgg : (g : Module.End (ZMod 2) L2) * ((g⁻¹ : GLV) : Module.End (ZMod 2) L2) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel]
      rfl
    rw [← hgi, Units.val_mul, Units.val_mul, hmono, mul_sub, sub_mul, mul_one, mul_assoc, hgg]
  rw [hu', finrank_range_conj]
  exact h1

end CFSG.Monster.Existence
