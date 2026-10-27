module

public import CFSG.Monster.B.Fischer.Fi22Faithful
public import CFSG.Monster.B.Fischer.Fi22OrderCheck
public import CFSG.Certificates.NativeValidSchreier

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Fischer

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem fi22OrigArrs_get {k : ℕ} (hk : k < 2) : fi22OrigArrs[k]! = fi22ChainGen k := by
  rw [fi22OrigArrs, getElem!_pos _ k (by simp [hk]), Array.getElem_ofFn]

theorem fi22WordArrs_get {j : ℕ} (hj : j < 19) : fi22WordArrs[j]! = fi22Derivation j := by
  rw [fi22WordArrs, getElem!_pos _ j (by simp [hj]), Array.getElem_ofFn]

theorem fi22ChainArrays :
    ChainArrays fi22Chain fi22OrigArrs fi22StrongArrs fi22BaseArr
    fi22WordArrs where
  orig_size := by simp [fi22OrigArrs]; rfl
  strong_size := by simp [fi22StrongArrs]; rfl
  base_size := rfl
  orig k := by
    have hk : (k : ℕ) < 2 := k.2
    rw [fi22OrigArrs_get hk, fi22Chain_original_get]
    exact rep_fi22Gen hk
  strong j := by
    have hj : (j : ℕ) < 19 := j.2
    rw [fi22Chain_strong_get]
    exact rep_fi22Strong hj
  base_val i := by
    have hi : (i : ℕ) < 6 := i.2
    change (((#v[0, 1, 2, 3, 6, 4] : Vector (Fin 3510) 6).get ⟨i, hi⟩ : Fin 3510) : ℕ) =
      fi22BaseArr[(i : ℕ)]!
    obtain ⟨i, hi⟩ := i
    revert i
    decide
  deriv j hj := by
    have hj' : (j : ℕ) < 19 := j.2
    rw [fi22WordArrs_get hj']
    rfl

theorem fi22Chain_valid :
    ValidSchreier fi22Chain ∧ ∀ i : Fin fi22Chain.baseCount,
    fi22Chain.orbitSize i = ((rawLevels 3510 fi22StrongArrs fi22BaseArr)[(i : ℕ)]!).pts.size :=
  validSchreier_of_chainOK fi22ChainArrays (by norm_num) fi22Order_check.1

theorem fi22Chain_orbitSizes :
    (List.finRange fi22Chain.baseCount).map fi22Chain.orbitSize = [3510, 2816, 567, 720, 8, 2] := by
  have h := fi22Order_check.2
  rw [rawOrbitSizes] at h
  rw [← h]
  apply List.ext_getElem
  · simp [rawLevels, fi22BaseArr, fi22ChainBase]
    rfl
  · intro k h1 h2
    have hk : k < (rawLevels 3510 fi22StrongArrs fi22BaseArr).size := by simpa using h2
    simp only [List.getElem_map, List.getElem_finRange, Array.getElem_toList]
    rw [fi22Chain_valid.2]
    show ((rawLevels 3510 fi22StrongArrs fi22BaseArr)[k]!).pts.size = _
    rw [getElem!_pos _ k hk]

theorem fi22Chain_orbitSize
    (i : Fin fi22Chain.baseCount) :
    fi22Chain.orbitSize i = [3510, 2816, 567, 720, 8, 2][(i : ℕ)]! := by
  rw [← fi22Chain_orbitSizes]
  rw [getElem!_pos _ (i : ℕ) (by simp)]
  simp

theorem card_fi22P :
    Nat.card fi22P = 64561751654400 := by
  have h := (RawSchreierDatum.schreier_chain_order fi22Chain fi22Chain_valid.1).2.2.1
  rw [fi22P, h]
  simp only [← RawSchreierDatum.orbitSize_eq_card, fi22Chain_orbitSize]
  rfl

theorem fi22P_orbit_zero :
    MulAction.orbit fi22P (0 : Fin 3510) = Set.univ := by
  show MulAction.orbit fi22Chain.originalSubgroup (0 : Fin 3510) = Set.univ
  have h0 : (0 : ℕ) < fi22Chain.baseCount := by decide
  have horb := RawSchreierDatum.orbitPoints_eq_orbit fi22Chain ⟨0, h0⟩
  rw [RawSchreierDatum.levelSubgroup_zero_eq_original fi22Chain fi22Chain_valid.1] at horb
  have hcard : Nat.card (fi22Chain.orbitPoints ⟨0, h0⟩) = 3510 := by
    rw [← RawSchreierDatum.orbitSize_eq_card, fi22Chain_orbitSize]
    rfl
  rw [horb, show fi22Chain.base.get ⟨0, h0⟩ = 0 from rfl] at hcard
  refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ (Set.toFinite _)
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin, ← Nat.card_coe_set_eq, hcard]

theorem fi22P_transitive :
    MulAction.IsPretransitive fi22P (Fin 3510) := by
  refine ⟨fun x y => ?_⟩
  have hx : x ∈ MulAction.orbit fi22P (0 : Fin 3510) := by rw [fi22P_orbit_zero]; trivial
  have hy : y ∈ MulAction.orbit fi22P (0 : Fin 3510) := by rw [fi22P_orbit_zero]; trivial
  obtain ⟨g, rfl⟩ := hx
  obtain ⟨h, rfl⟩ := hy
  exact ⟨h * g⁻¹, by rw [mul_smul, inv_smul_smul]⟩

theorem card_fi22P_stabilizer :
    Nat.card (MulAction.stabilizer fi22P (0 : Fin 3510)) = 18393661440 := by
  have h1 := MulAction.index_stabilizer fi22P (0 : Fin 3510)
  have h2 := (MulAction.stabilizer fi22P (0 : Fin 3510)).card_mul_index
  rw [h1, fi22P_orbit_zero, Set.ncard_univ, Nat.card_fin, card_fi22P] at h2
  have h3 : Nat.card (MulAction.stabilizer fi22P (0 : Fin 3510)) * 3510 = 18393661440 * 3510 := by
    rw [h2]
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h3

theorem rep_powA {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) :
    ∀ e, Rep n (powA n t e) (g ^ e)
  | 0 => by rw [pow_zero]; exact rep_idA
  | e + 1 => by rw [pow_succ']; exact rep_compA ht (rep_powA ht e)

theorem orderOf_of_check {n p : ℕ} [Fact p.Prime] {t : Array ℕ} {g : Equiv.Perm (Fin n)}
    (ht : Rep n t g) (hp : eqA n (powA n t p) (idA n) = true) (h1 : eqA n t (idA n) = false) :
    orderOf g = p := by
  refine orderOf_eq_prime ((eqA_iff (rep_powA ht p) rep_idA).1 hp) fun hg => ?_
  rw [← Bool.not_eq_true, eqA_iff ht rep_idA] at h1
  exact h1 hg

instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

instance fact_prime_eleven : Fact (Nat.Prime 11) := ⟨by norm_num⟩

instance fact_prime_thirteen : Fact (Nat.Prime 13) := ⟨by norm_num⟩

theorem rep_fi22Gen01 :
    Rep 3510 (compA 3510 (fi22ChainGen 0) (fi22ChainGen 1)) (fi22GenPerm 0 * fi22GenPerm 1) :=
  rep_compA (rep_fi22Gen (by norm_num)) (rep_fi22Gen (by norm_num))

theorem orderOf_a0 :
    orderOf (fi22GenPerm 0) = 2 :=
  orderOf_of_check (rep_fi22Gen (by norm_num)) fi22Orders_check.1 fi22Orders_check.2.1

theorem orderOf_a1 :
    orderOf (fi22GenPerm 1) = 13 :=
  orderOf_of_check (rep_fi22Gen (by norm_num)) fi22Orders_check.2.2.1 fi22Orders_check.2.2.2.1

theorem orderOf_a0a1 :
    orderOf (fi22GenPerm 0 * fi22GenPerm 1) = 11 :=
  orderOf_of_check rep_fi22Gen01 fi22Orders_check.2.2.2.2.1 fi22Orders_check.2.2.2.2.2

theorem fi22C0_mul_C1 :
    fi22C0 * fi22C1 = fi22GenPerm 1 := by
  have h2 : fi22GenPerm 0 * fi22GenPerm 0 = 1 := by
    rw [← pow_two, ← orderOf_a0, pow_orderOf_eq_one]
  rw [fi22C0, fi22C1, ← mul_assoc, h2, one_mul]

theorem fi22P_eq_closure_C : Subgroup.closure {fi22C0, fi22C1} = fi22P := by
  rw [fi22P_eq]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact Subgroup.subset_closure ⟨0, rfl⟩
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨0, rfl⟩)
        (Subgroup.subset_closure ⟨1, rfl⟩)
  · rw [Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    fin_cases k
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · have : fi22GenPerm 1 = fi22C0⁻¹ * fi22C1 := by
        rw [fi22C0, fi22C1, inv_mul_cancel_left]
      change fi22GenPerm 1 ∈ _
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure (Set.mem_insert _ _)))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))

theorem Fi22_order_coprime_generators :
    ValidSchreier fi22Chain ∧ fi22Chain.base.toList.map Fin.val = [0, 1, 2, 3, 6, 4] ∧
    (List.finRange fi22Chain.baseCount).map fi22Chain.orbitSize = [3510, 2816, 567, 720, 8, 2] ∧
    Nat.card fi22P = 64561751654400 ∧ MulAction.IsPretransitive fi22P (Fin 3510) ∧
    Nat.card (MulAction.stabilizer fi22P (0 : Fin 3510)) = 18393661440 ∧
    orderOf (fi22GenPerm 0) = 2 ∧ orderOf (fi22GenPerm 1) = 13 ∧
    orderOf (fi22GenPerm 0 * fi22GenPerm 1) = 11 ∧
    Subgroup.closure {fi22C0, fi22C1} = fi22P ∧
    orderOf fi22C0 = 2 ∧ orderOf fi22C1 = 11 ∧ orderOf (fi22C0 * fi22C1) = 13 ∧
    Nat.gcd (orderOf fi22C0) (orderOf fi22C1) = 1 ∧
    Nat.gcd (orderOf (fi22C0 * fi22C1)) (Nat.card (MulAction.stabilizer fi22P (0 : Fin 3510))) = 1 ∧
    Nat.card Blueprint.NativeSporadic.Fi22 = 64561751654400 := by
  have hc0 : orderOf fi22C0 = 2 := orderOf_a0
  have hc1 : orderOf fi22C1 = 11 := orderOf_a0a1
  have hc01 : orderOf (fi22C0 * fi22C1) = 13 := by rw [fi22C0_mul_C1, orderOf_a1]
  refine ⟨fi22Chain_valid.1, fi22Chain_base, fi22Chain_orbitSizes, card_fi22P, fi22P_transitive,
    card_fi22P_stabilizer, orderOf_a0, orderOf_a1, orderOf_a0a1, fi22P_eq_closure_C, hc0, hc1,
    hc01, by rw [hc0, hc1]; norm_num, by rw [hc01, card_fi22P_stabilizer]; norm_num, ?_⟩
  rw [Nat.card_congr fi22PermEquiv.toEquiv, card_fi22P]

end CFSG.Monster.B.Fischer
