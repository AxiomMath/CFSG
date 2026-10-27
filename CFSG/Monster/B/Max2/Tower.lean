module

public import Certificates.Data.CFSGNative.MonsterB.Max2Tower
public meta import Certificates.Data.CFSGNative.MonsterB.Max2Tower
public import CFSG.Monster.Code.Bits
public import CFSG.Monster.B.Gen.OrbitChain
public import Certificates.Certificate3049
public import CFSG.Certificates.Kernel.Spor.RawSound
public import Mathlib

public section

namespace CFSG.Monster.B.Max2

open Native Matrix CFSG.Monster.Code

theorem towerCheck_eq_true : towerCheck = true :=
  Certificates.certificate3049

@[expose] def decMat (rows : Array ℕ) : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  Matrix.of fun i j => bvec 22 rows[(i : ℕ)]! j

theorem bvec_actGo (rows : Array ℕ) (v : ℕ) :
    ∀ m acc, bvec 22 (VisCert.Native.actGo rows v m acc) =
      bvec 22 acc + ∑ i ∈ Finset.range m, if v.testBit i then bvec 22 rows[i]! else 0
  | 0, acc => by simp [VisCert.Native.actGo]
  | m + 1, acc => by
    rw [VisCert.Native.actGo, bvec_actGo rows v m, Finset.sum_range_succ]
    by_cases h : v.testBit m = true
    · rw [ite_eq_left h, ite_eq_left h, bvec_xor]
      abel
    · rw [ite_eq_right h, ite_eq_right h, add_zero]

theorem bvec_act22 (rows : Array ℕ) (v : ℕ) :
    bvec 22 (act22 rows v) = bvec 22 v ᵥ* decMat rows := by
  rw [act22, bvec_actGo, bvec_zero, zero_add]
  funext j
  rw [Finset.sum_apply, Finset.sum_range (fun i => (if v.testBit i then bvec 22 rows[i]! else 0) j)]
  simp only [vecMul, dotProduct, decMat, of_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [bvec_apply]
  split_ifs <;> simp

theorem getElem!_range_map {f : ℕ → ℕ} {i : ℕ} (hi : i < 22) :
    ((Array.range 22).map f)[i]! = f i := by
  rw [getElem!_pos ((Array.range 22).map f) i (by simpa using hi)]
  simp

theorem decMat_mul22 (A B : Array ℕ) : decMat (mul22 A B) = decMat A * decMat B := by
  ext i j
  rw [decMat, of_apply, mul22, getElem!_range_map i.isLt, bvec_act22, mul_apply]
  simp only [vecMul, dotProduct, decMat, of_apply]

theorem decMat_id22 : decMat id22 = 1 := by
  ext i j
  rw [decMat, of_apply, id22, getElem!_range_map i.isLt, bvec_apply, one_apply,
    Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : i = j
  · subst h
    simp
  · have h' : (i : ℕ) ≠ j := fun e => h (Fin.ext e)
    simp [h, h']

theorem decMat_eq_of_eq22 {A B : Array ℕ} (h : eq22 A B = true) : decMat A = decMat B := by
  simp only [eq22, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  ext i j
  rw [decMat, decMat, of_apply, of_apply, h.2 i i.isLt]

theorem bvec_injective22 {a b : ℕ} (ha : a < 2 ^ 22) (hb : b < 2 ^ 22) (h : bvec 22 a = bvec 22 b) :
    a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 22
  · have := congrFun h ⟨i, hi⟩
    simp only [bvec_apply] at this
    cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num)
      (by omega))), Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb (Nat.pow_le_pow_right
      (by norm_num) (by omega)))]

theorem tower_parts :
    sizesOK = true ∧ gensOK = true ∧ nodesOK = true ∧ levelsOK = true ∧ shapeOK = true := by
  have h := towerCheck_eq_true
  simp only [towerCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem size_nodeMats : (nodeMats ()).size = dagSize := by
  have h := tower_parts.1
  simp only [sizesOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem nodeOK_of_lt {j : ℕ} (hj : j < dagSize) : nodeOK
    (towerDag ()) (nodeMats ()) j = true := by
  have h := tower_parts.2.2.1
  simp only [nodesOK, List.all_eq_true, List.mem_range] at h
  exact h j hj

theorem levelOK_of_lt {i : ℕ} (hi : i < 6) : levelOK
    (towerPointsAll ()) (nodeMats ()) i = true := by
  have h := tower_parts.2.2.2.1
  simp only [levelsOK, List.all_eq_true, List.mem_range] at h
  exact h i hi

theorem gens_parts :
    eq22 (mul22 r1Rows (inv22 r1Rows)) id22 = true ∧ eq22 (mul22 (inv22 r1Rows) r1Rows) id22 = true ∧
    eq22 (mul22 r2Rows (inv22 r2Rows)) id22 = true ∧ eq22 (mul22 (inv22 r2Rows) r2Rows) id22 = true := by
  have h := tower_parts.2.1
  simp only [gensOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem lengths_eq : towerLevels.toList.map (·.2) =
    [2300, 1408, 840, 216, 36, 2] := by
  have h := tower_parts.2.2.2.2
  simp only [shapeOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

@[irreducible, expose] noncomputable def R1u : GL (Fin 22) (ZMod 2)
    where
  val := decMat r1Rows
  inv := decMat (inv22 r1Rows)
  val_inv := by rw [← decMat_mul22, decMat_eq_of_eq22 gens_parts.1, decMat_id22]
  inv_val := by rw [← decMat_mul22, decMat_eq_of_eq22 gens_parts.2.1, decMat_id22]

@[irreducible, expose] noncomputable def R2u : GL (Fin 22) (ZMod 2)
    where
  val := decMat r2Rows
  inv := decMat (inv22 r2Rows)
  val_inv := by rw [← decMat_mul22, decMat_eq_of_eq22 gens_parts.2.2.1, decMat_id22]
  inv_val := by rw [← decMat_mul22, decMat_eq_of_eq22 gens_parts.2.2.2, decMat_id22]

theorem coe_R1u :
    ((R1u : GL (Fin 22) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2)) =
    decMat r1Rows := by
  unfold R1u
  rfl

theorem coe_R2u :
    ((R2u : GL (Fin 22) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2)) =
    decMat r2Rows := by
  unfold R2u
  rfl

@[irreducible, expose] def dagE (j : ℕ) : Int × ℕ := (towerDag ())[j]!

theorem dagE_eq (j : ℕ) : dagE j = (towerDag ())[j]! := by
  unfold dagE
  rfl

@[expose] noncomputable def nodeEltF (D : ℕ → Int × ℕ) (j : ℕ) : GL
    (Fin 22) (ZMod 2) :=
  if (D j).1 = -2 then 1
  else if (D j).1 = -3 then R1u
  else if (D j).1 = -4 then R2u
  else if (D j).1 = -1 then
    (if _hb : (D j).2 < j then (nodeEltF D (D j).2)⁻¹ else 1)
  else if _hab : (D j).1.toNat < j ∧ (D j).2 < j then
    nodeEltF D (D j).1.toNat * nodeEltF D (D j).2
  else 1
termination_by j
decreasing_by all_goals omega

@[expose] noncomputable def nodeElt (j : ℕ) : GL (Fin 22) (ZMod 2) :=
    nodeEltF dagE j

theorem nodeEltF_mem (D : ℕ → Int × ℕ) (j : ℕ) :
    nodeEltF D j ∈ Subgroup.closure ({R1u, R2u} : Set (GL (Fin 22) (ZMod 2))) := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  rw [nodeEltF]
  split_ifs with h2 h3 h4 h1 hb hab
  · exact Subgroup.one_mem _
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  · exact Subgroup.inv_mem _ (ih _ hb)
  · exact Subgroup.one_mem _
  · exact Subgroup.mul_mem _ (ih _ hab.1) (ih _ hab.2)
  · exact Subgroup.one_mem _

theorem nodeElt_mem (j : ℕ) :
    nodeElt j ∈ Subgroup.closure ({R1u, R2u} : Set (GL (Fin 22) (ZMod 2))) :=
  nodeEltF_mem dagE j

theorem decMat_nodeMats (j : ℕ) (hj : j < dagSize) :
    decMat ((nodeMats ())[j]!) =
      ((nodeEltF dagE j : GL (Fin 22) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2)) := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  have hok := nodeOK_of_lt hj
  simp only [nodeOK, ← dagE_eq] at hok
  rw [nodeEltF]
  split_ifs at hok ⊢ with h2 h3 h4 h1 hb hab
  · rw [decMat_eq_of_eq22 hok, decMat_id22, Units.val_one]
  · rw [decMat_eq_of_eq22 hok, coe_R1u]
  · rw [decMat_eq_of_eq22 hok, coe_R2u]
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    have hprod := decMat_eq_of_eq22 hok.2
    rw [decMat_mul22, decMat_id22, ih _ hb (by omega)] at hprod
    calc decMat ((nodeMats ())[j]!)
        = ((nodeEltF dagE (dagE j).2)⁻¹ : GL (Fin 22) (ZMod 2)) *
            ((nodeEltF dagE (dagE j).2 : GL (Fin 22) (ZMod 2)) * decMat ((nodeMats ())[j]!)) := by
          rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = ((nodeEltF dagE (dagE j).2)⁻¹ : GL (Fin 22) (ZMod 2)) := by rw [hprod, mul_one]
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    exact absurd hok.1 hb
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    rw [decMat_eq_of_eq22 hok.2, decMat_mul22, Units.val_mul, ih _ hab.1 (by omega),
      ih _ hab.2 (by omega)]
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    exact absurd ⟨hok.1.1.2, hok.1.2⟩ hab

@[reducible, expose] noncomputable def rowMulAction :
    MulAction (GL (Fin 22) (ZMod 2)) (Fin 22 → ZMod 2) where
  smul g v := v ᵥ* ((g⁻¹ : GL (Fin 22) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2))
  one_smul v := by
    change v ᵥ* (((1 : GL (Fin 22) (ZMod 2))⁻¹ : GL (Fin 22) (ZMod 2)) :
      Matrix (Fin 22) (Fin 22) (ZMod 2)) = v
    rw [inv_one, Units.val_one, vecMul_one]
  mul_smul g h v := by
    change v ᵥ* (((g * h)⁻¹ : GL (Fin 22) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2)) =
      (v ᵥ* ((h⁻¹ : GL (Fin 22) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2))) ᵥ*
        ((g⁻¹ : GL (Fin 22) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2))
    rw [_root_.mul_inv_rev, Units.val_mul, vecMul_vecMul]

theorem vecMul_nodeElt {w : ℕ} (hw : w < dagSize) (c : ℕ) :
    bvec 22 c ᵥ* ((nodeEltF dagE w : GL (Fin 22) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2)) =
      bvec 22 (act22 ((nodeMats ())[w]!) c) := by
  rw [bvec_act22, decMat_nodeMats w hw]

theorem level_facts {i : ℕ} (hi : i < 6) :
    (levelPoints (towerPointsAll ()) i).length = (towerLevels[i]!).2 ∧
      (towerLevels[i]!).1 < 2 ^ 22 ∧ ((levelPoints (towerPointsAll ()) i).map (·.1)).Nodup ∧
      ∀ p ∈ levelPoints (towerPointsAll ()) i, p.1 < 2 ^ 22 ∧ p.2 < (nodeMats ()).size ∧
        act22 ((nodeMats ())[p.2]!) (towerLevels[i]!).1 = p.1 ∧
        ∀ k < i, act22 ((nodeMats ())[p.2]!) (towerLevels[k]!).1 = (towerLevels[k]!).1 := by
  have h := levelOK_of_lt hi
  simp only [levelOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨hlen, hbi⟩, hnd⟩, hpts⟩ := h
  refine ⟨hlen, hbi, hnd, fun p hp => ?_⟩
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hpts p hp
  exact ⟨h1, h2, h3, h4⟩

@[expose] noncomputable def levelSet (i : ℕ) : Finset (Fin 22 → ZMod 2) :=
  ((levelPoints (towerPointsAll ()) i).map fun p => bvec 22 p.1).toFinset

@[expose] noncomputable def levelBase (i : ℕ) : Fin 22 → ZMod 2 := bvec 22 (towerLevels[i]!).1

theorem card_levelSet {i : ℕ} (hi : i < 6) : (levelSet i).card =
    (towerLevels[i]!).2 := by
  obtain ⟨hlen, -, hnd, hpts⟩ := level_facts hi
  rw [levelSet, List.toFinset_card_of_nodup, List.length_map, hlen]
  rw [show ((levelPoints (towerPointsAll ()) i).map fun p => bvec 22 p.1) =
      ((levelPoints (towerPointsAll ()) i).map (·.1)).map (bvec 22) by
    rw [List.map_map]
    rfl]
  refine hnd.map_on fun x hx y hy hxy => ?_
  simp only [List.mem_map] at hx hy
  obtain ⟨px, hpx, rfl⟩ := hx
  obtain ⟨py, hpy, rfl⟩ := hy
  exact bvec_injective22 (hpts px hpx).1 (hpts py hpy).1 hxy

theorem prod_card_levelSet : ∏ i ∈ Finset.range 6, (levelSet i).card
    = 42305421312000 := by
  rw [Finset.prod_congr rfl fun i hi => card_levelSet (Finset.mem_range.1 hi)]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero]
  have h := lengths_eq
  simp only [towerLevels] at h ⊢
  decide

theorem levelSet_reach {i : ℕ} (hi : i < 6) {p : Fin 22 → ZMod 2}
    (hp : p ∈ levelSet i) :
    ∃ w < dagSize, (∀ k < i, levelBase k ᵥ* ((nodeEltF dagE w : GL (Fin 22) (ZMod 2)) :
        Matrix (Fin 22) (Fin 22) (ZMod 2)) = levelBase k) ∧
      levelBase i ᵥ* ((nodeEltF dagE w : GL (Fin 22) (ZMod 2)) :
        Matrix (Fin 22) (Fin 22) (ZMod 2)) = p := by
  obtain ⟨-, -, -, hpts⟩ := level_facts hi
  simp only [levelSet, List.mem_toFinset, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  obtain ⟨-, hq2, hqb, hqk⟩ := hpts q hq
  have hw : q.2 < dagSize := size_nodeMats ▸ hq2
  refine ⟨q.2, hw, fun k hk => ?_, ?_⟩
  · rw [levelBase, vecMul_nodeElt hw, hqk k hk]
  · rw [levelBase, vecMul_nodeElt hw, hqb]

theorem card_closure_R12_ge :
    42305421312000 ≤ Nat.card (Subgroup.closure ({R1u, R2u} : Set (GL (Fin 22) (ZMod 2)))) := by
  let _ : MulAction (GL (Fin 22) (ZMod 2)) (Fin 22 → ZMod 2) := rowMulAction
  rw [← prod_card_levelSet]
  refine card_ge_prod_of_chain levelBase levelSet 6 fun i hi p hp => ?_
  obtain ⟨w, -, hfix, hmap⟩ := levelSet_reach hi hp
  refine ⟨⟨(nodeEltF dagE w)⁻¹, Subgroup.inv_mem _ (nodeEltF_mem dagE w)⟩, fun k hk => ?_, ?_⟩
  · change levelBase k ᵥ* ((((nodeEltF dagE w)⁻¹)⁻¹ : GL (Fin 22) (ZMod 2)) :
      Matrix (Fin 22) (Fin 22) (ZMod 2)) = levelBase k
    rw [inv_inv]
    exact hfix k hk
  · change levelBase i ᵥ* ((((nodeEltF dagE w)⁻¹)⁻¹ : GL (Fin 22) (ZMod 2)) :
      Matrix (Fin 22) (Fin 22) (ZMod 2)) = p
    rw [inv_inv]
    exact hmap

end CFSG.Monster.B.Max2
