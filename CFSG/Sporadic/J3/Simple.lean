module

public import CFSG.Sporadic.J3.Prim

public section

namespace CFSG.Sporadic.J3

open Native CFSG.Sporadic.Th CFSG.Perm CFSG.Perm.Native
open CFSG.Sporadic.Th.Native (ap)

variable {D : Data} {c : ℕ} (hF : Facts D c)
include hF

theorem val_val_a : (((a D : J D) : GL (Fin 80) (ZMod 2)) : Matrix (Fin 80) (Fin 80) (ZMod 2)) =
    mA D := a_val hF.powA

theorem val_val_b : (((b D : J D) : GL (Fin 80) (ZMod 2)) : Matrix (Fin 80) (Fin 80) (ZMod 2)) =
    mB D := b_val hF.powB

omit hF in
theorem eq_one_of_val_val {g : J D}
    (h : ((g : GL (Fin 80) (ZMod 2)) : Matrix (Fin 80) (Fin 80) (ZMod 2)) = 1) : g = 1 := by
  apply Subtype.ext
  apply Units.ext
  exact h

theorem a_sq : a D ^ 2 = 1 := by
  apply eq_one_of_val_val
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, val_val_a hF]
  exact mA_sq hF.powA

theorem b_cube : b D ^ 3 = 1 := by
  apply eq_one_of_val_val
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, val_val_b hF]
  exact mB_cube hF.powB

theorem ab_pow : (a D * b D) ^ 19 = 1 := by
  apply eq_one_of_val_val
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Subgroup.coe_mul, Units.val_mul, val_val_a hF,
    val_val_b hF]
  have := congrArg (rowsMatrix 80) hF.powAB
  rwa [rowsMatrix_powRows, rowsMatrix_mulRows, rowsMatrix_idRows, rowsMatrix_rowsA,
    rowsMatrix_rowsB] at this

omit hF in
theorem ne_one_of_moves {g : J D} {T : CFSG.Sporadic.Th.Native.Table} (hT : Rep D.n T g)
    {p : ℕ} (hp : p < D.n) (h : ap T p ≠ p) : g ≠ 1 := by
  rintro rfl
  apply h
  rw [hT p hp, idx_one]

theorem orderOf_a : orderOf (a D) = 2 :=
  orderOf_eq_prime (a_sq hF) (ne_one_of_moves (rep_a hF.orbitFacts) hF.n_pos hF.a0)

theorem orderOf_b : orderOf (b D) = 3 :=
  orderOf_eq_prime (b_cube hF) (ne_one_of_moves (rep_b hF.orbitFacts) hF.n_pos hF.b0)

theorem orderOf_ab : orderOf (a D * b D) = 19 := by
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  refine orderOf_eq_prime (ab_pow hF) ?_
  intro h
  have hb : b D = (a D)⁻¹ := eq_inv_of_mul_eq_one_right h
  have ha : (a D)⁻¹ = a D := by rw [inv_eq_iff_mul_eq_one, ← pow_two, a_sq hF]
  rw [ha] at hb
  have h2 : b D ^ 2 = 1 := by rw [hb, a_sq hF]
  have h3 := orderOf_dvd_of_pow_eq_one h2
  rw [orderOf_b hF] at h3
  norm_num at h3

theorem trees_size_eq {l : ℕ} (hl : l < D.base.size) : D.trees[l]!.pts.size = D.orbSizes[l]! := by
  have h := congrArg (fun L : List ℕ => L[l]?) hF.sizes
  have hl' : l < D.trees.size := by rw [(chainOK_parts hF.chain).2.2.1]; exact hl
  simp only [orbitSizes, List.getElem?_map, Array.getElem?_toList,
    Array.getElem?_eq_getElem hl', Option.map_some] at h
  rw [getElem!_pos D.trees l hl', getElem!_def, ← h]

theorem card_J : Nat.card (J D) = ∏ l ∈ Finset.Ico 0 D.base.size, D.orbSizes[l]! := by
  rw [← Subgroup.card_top (G := J D), ← lvl_zero hF, card_lvl hF (Nat.zero_le _)]
  exact Finset.prod_congr rfl fun l hl => trees_size_eq hF (Finset.mem_Ico.1 hl).2

theorem coprime_ab : Nat.Coprime (orderOf (a D)) (orderOf (b D)) := by
  rw [orderOf_a hF, orderOf_b hF]; norm_num

theorem coprime_stab (hprod : Nat.Coprime 19 (∏ l ∈ Finset.Ico 1 D.base.size, D.orbSizes[l]!)) :
    Nat.Coprime (orderOf (a D * b D))
      (Nat.card (MulAction.stabilizer (J D) (root D hF.n_pos))) := by
  rw [orderOf_ab hF, card_stabilizer_root hF,
    Finset.prod_congr rfl fun l hl => trees_size_eq hF (Finset.mem_Ico.1 hl).2]
  exact hprod

omit hF in
theorem two_le_card (hn2 : 2 ≤ D.n) : 2 ≤ Nat.card (Fin D.n) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hn2

theorem isSimpleGroup_J (horb : D.orbSizes[0]! = D.n) (hn2 : 2 ≤ D.n)
    (hprod : Nat.Coprime 19 (∏ l ∈ Finset.Ico 1 D.base.size, D.orbSizes[l]!)) :
    IsSimpleGroup (J D) :=
  have := faithful hF
  have := isPreprimitive hF horb
  isSimpleGroup_of_primitive_coprime_orders (Ω := Fin D.n) (two_le_card hn2) (a D) (b D)
    (closure_ab D) (root D hF.n_pos) (coprime_ab hF) (coprime_stab hF hprod)

theorem isSimpleGroup_seedUnits (horb : D.orbSizes[0]! = D.n) (hn2 : 2 ≤ D.n)
    (hprod : Nat.Coprime 19 (∏ l ∈ Finset.Ico 1 D.base.size, D.orbSizes[l]!)) :
    IsSimpleGroup (CFSG.Blueprint.NativeSporadic.seedMonoid 2 80 1 D.seedA D.seedB)ˣ :=
  @MulEquiv.isSimpleGroup _ _ _ _ (isSimpleGroup_J hF horb hn2 hprod) (seedEquiv hF.powA hF.powB)

theorem card_seedUnits :
    Nat.card (CFSG.Blueprint.NativeSporadic.seedMonoid 2 80 1 D.seedA D.seedB)ˣ =
      ∏ l ∈ Finset.Ico 0 D.base.size, D.orbSizes[l]! := by
  rw [Nat.card_congr (seedEquiv hF.powA hF.powB).toEquiv, card_J hF]

end CFSG.Sporadic.J3
