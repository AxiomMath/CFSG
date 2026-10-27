module

public import CFSG.Sporadic.Co2Cert.Faithful
public import CFSG.Sporadic.Co2Cert.OrderCheck
public import CFSG.Monster.B.Mathieu.SylowSound
public import CFSG.Certificates.NativeSchreierCard

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Cert

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Mathieu

theorem co2Q_chainArrays :
    ChainArrays co2Q co2OrigArrs co2StrongArrs co2BaseArr co2WordArrs :=
  co2Q_records.2.2

theorem co2Qc_chainArrays :
    ChainArrays co2Qc co2cOrigArrs co2cStrongArrs co2cBaseArr co2cWordArrs :=
  co2Qc_records.2.2

theorem co2Q_valid :
    ValidSchreier co2Q ∧ ∀ i : Fin co2Q.baseCount,
    co2Q.orbitSize i = ((rawLevels 2300 co2StrongArrs co2BaseArr)[(i : ℕ)]!).pts.size :=
  validSchreier_of_chainOK co2Q_chainArrays (by norm_num) co2Chain_check.1

theorem co2Qc_valid :
    ValidSchreier co2Qc ∧ ∀ i : Fin co2Qc.baseCount,
    co2Qc.orbitSize i = ((rawLevels 2300 co2cStrongArrs co2cBaseArr)[(i : ℕ)]!).pts.size :=
  validSchreier_of_chainOK co2Qc_chainArrays (by norm_num) co2cChain_check.1

theorem co2Q_baseCount : co2Q.baseCount = 6 := by
  change co2BaseArr.size = 6
  rw [co2BaseArr_eq]
  rfl

theorem co2Qc_baseCount : co2Qc.baseCount = 6 := by
  change co2cBaseArr.size = 6
  rw [co2cBaseArr_eq]
  rfl

theorem orbitSizes_of_check {Q : RawSchreierDatum 2300} {S : Array (Array ℕ)} {base : Array ℕ}
    (hb : Q.baseCount = base.size)
    (hsz : ∀ i : Fin Q.baseCount, Q.orbitSize i = ((rawLevels 2300 S base)[(i : ℕ)]!).pts.size) :
    (List.finRange Q.baseCount).map Q.orbitSize = rawOrbitSizes 2300 S base := by
  rw [rawOrbitSizes]
  apply List.ext_getElem
  · simp [rawLevels, hb]
  · intro k h1 h2
    have hk : k < (rawLevels 2300 S base).size := by simpa using h2
    simp only [List.getElem_map, List.getElem_finRange, Array.getElem_toList]
    rw [hsz]
    show ((rawLevels 2300 S base)[k]!).pts.size = _
    rw [getElem!_pos _ k hk]

theorem co2Q_orbitSizes :
    (List.finRange co2Q.baseCount).map co2Q.orbitSize = [2300, 1408, 567, 192, 30, 4] := by
  rw [orbitSizes_of_check (Q := co2Q) (S := co2StrongArrs) (base := co2BaseArr) rfl
    co2Q_valid.2, co2Chain_check.2]

theorem co2Q_orbitSize
    (i : Fin co2Q.baseCount) :
    co2Q.orbitSize i = [2300, 1408, 567, 192, 30, 4][(i : ℕ)]! := by
  rw [← co2Q_orbitSizes]
  rw [getElem!_pos _ (i : ℕ) (by simp)]
  simp

theorem co2Qc_orbitSizes :
    (List.finRange co2Qc.baseCount).map co2Qc.orbitSize = [2300, 1408, 567, 192, 30, 4] := by
  rw [orbitSizes_of_check (Q := co2Qc) (S := co2cStrongArrs) (base := co2cBaseArr) rfl
    co2Qc_valid.2, co2cChain_check.2]

theorem rawOfArrays_base_toList {n : ℕ} {O S : Array (Array ℕ)} {base : Array ℕ}
    {W : Array (List ℤ)} {hn : 1 ≤ n} {hle : O.size ≤ S.size}
    {hlt : ∀ i < base.size, base[i]! < n} {hnd : base.toList.Nodup} :
    (rawOfArrays n O S base W hn hle hlt hnd).base.toList.map Fin.val = base.toList := by
  change (Vector.ofFn fun i : Fin base.size =>
    (⟨base[(i : ℕ)]!, hlt i i.2⟩ : Fin n)).toList.map Fin.val = base.toList
  rw [Vector.toList_ofFn]
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [List.getElem_map, List.getElem_ofFn, Array.getElem_toList]
  exact getElem!_pos base k (by simpa using h2)

theorem co2Q_base :
    co2Q.base.toList.map Fin.val = [0, 1, 2, 3, 5, 4] := by
  have h : co2Q.base.toList.map Fin.val = co2BaseArr.toList := rawOfArrays_base_toList
  rw [h, co2BaseArr_eq]

theorem co2Qc_base :
    co2Qc.base.toList.map Fin.val = [0, 1, 3, 2, 5, 4] := by
  have h : co2Qc.base.toList.map Fin.val = co2cBaseArr.toList := rawOfArrays_base_toList
  rw [h, co2cBaseArr_eq]

theorem card_co2P :
    Nat.card co2P = 42305421312000 := by
  rw [← co2Q_originalSubgroup,
    card_originalSubgroup_of_chainOK co2Q_chainArrays (by norm_num) co2Chain_check.1,
    co2Chain_check.2]
  rfl

theorem card_co2Pc :
    Nat.card co2Pc = 42305421312000 := by
  rw [← co2Qc_originalSubgroup,
    card_originalSubgroup_of_chainOK co2Qc_chainArrays (by norm_num) co2cChain_check.1,
    co2cChain_check.2]
  rfl

theorem co2P_orbit_zero :
    MulAction.orbit co2P (0 : Fin 2300) = Set.univ := by
  rw [← co2Q_originalSubgroup]
  have h0 : (0 : ℕ) < co2Q.baseCount := by rw [co2Q_baseCount]; norm_num
  have horb := RawSchreierDatum.orbitPoints_eq_orbit co2Q ⟨0, h0⟩
  rw [RawSchreierDatum.levelSubgroup_zero_eq_original co2Q co2Q_valid.1] at horb
  have hb0 : co2Q.base.get ⟨0, h0⟩ = 0 := by
    apply Fin.ext
    have hv : ((co2Q.base.get ⟨0, h0⟩ : Fin 2300) : ℕ) = co2BaseArr[0]! :=
      rawOfArrays_base_get (n := 2300) (O := co2OrigArrs) (S := co2StrongArrs)
        (W := co2WordArrs) ⟨0, h0⟩
    rw [hv, co2BaseArr_eq]
    rfl
  have hcard : Nat.card (co2Q.orbitPoints ⟨0, h0⟩) = 2300 := by
    rw [← RawSchreierDatum.orbitSize_eq_card, co2Q_orbitSize]
    rfl
  rw [horb, hb0] at hcard
  refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ (Set.toFinite _)
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin, ← Nat.card_coe_set_eq, hcard]

theorem co2P_transitive :
    MulAction.IsPretransitive co2P (Fin 2300) := by
  refine ⟨fun x y => ?_⟩
  have hx : x ∈ MulAction.orbit co2P (0 : Fin 2300) := by rw [co2P_orbit_zero]; trivial
  have hy : y ∈ MulAction.orbit co2P (0 : Fin 2300) := by rw [co2P_orbit_zero]; trivial
  obtain ⟨g, rfl⟩ := hx
  obtain ⟨h, rfl⟩ := hy
  exact ⟨h * g⁻¹, by rw [mul_smul, inv_smul_smul]⟩

theorem card_co2P_stabilizer :
    Nat.card (MulAction.stabilizer co2P (0 : Fin 2300)) = 18393661440 := by
  have h1 := MulAction.index_stabilizer co2P (0 : Fin 2300)
  have h2 := (MulAction.stabilizer co2P (0 : Fin 2300)).card_mul_index
  rw [h1, co2P_orbit_zero, Set.ncard_univ, Nat.card_fin, card_co2P] at h2
  have h3 : Nat.card (MulAction.stabilizer co2P (0 : Fin 2300)) * 2300 =
      18393661440 * 2300 := by
    rw [h2]
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h3

theorem rep_co2Gen_inv {k : ℕ} (hk : k < 2) :
    Rep 2300 (invCand 2300 co2OrigArrs[k]!) (co2Gen k)⁻¹ :=
  rep_inv_of_isInvA (rep_co2Gen hk) (co2Shape.chain.orig_inv hk)

theorem rep_co2W : Rep 2300 co2WArr co2W := by
  rw [co2W_eq, show (co2Gen 0)⁻¹ * co2Gen 1 * co2Gen 1 * co2Gen 0 * co2Gen 1 * (co2Gen 0)⁻¹ =
    (co2Gen 0)⁻¹ * (co2Gen 1 * (co2Gen 1 * (co2Gen 0 * (co2Gen 1 * (co2Gen 0)⁻¹)))) by
      simp only [mul_assoc]]
  exact rep_compA (rep_co2Gen_inv (by norm_num)) (rep_compA (rep_co2Gen (by norm_num))
    (rep_compA (rep_co2Gen (by norm_num)) (rep_compA (rep_co2Gen (by norm_num))
      (rep_compA (rep_co2Gen (by norm_num)) (rep_co2Gen_inv (by norm_num))))))

theorem co2cGen_zero :
    co2cGen 0 = co2Gen 0 :=
  eq_of_eqA (rep_co2cGen (by norm_num)) (rep_co2Gen (by norm_num)) co2Conj_check.2.1

theorem co2cGen_one :
    co2cGen 1 = co2W⁻¹ * co2Gen 1 * co2W := by
  have hwi := rep_inv_of_isInvA rep_co2W co2Conj_check.1
  rw [mul_assoc]
  exact eq_of_eqA (rep_co2cGen (by norm_num))
    (rep_compA hwi (rep_compA (rep_co2Gen (by norm_num)) rep_co2W)) co2Conj_check.2.2.1

theorem co2W_mem : co2W ∈ co2P := by
  rw [co2W_eq]
  have h0 : co2Gen 0 ∈ co2P := Subgroup.subset_closure (Set.mem_insert _ _)
  have h1 : co2Gen 1 ∈ co2P := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (inv_mem h0) h1) h1) h0) h1) (inv_mem h0)

theorem co2Pc_le : co2Pc ≤ co2P := by
  rw [co2Pc, Subgroup.closure_le]
  have h1 : co2Gen 1 ∈ co2P := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  rintro _ (rfl | rfl)
  · rw [co2cGen_zero]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  · rw [co2cGen_one]
    exact mul_mem (mul_mem (inv_mem co2W_mem) h1) co2W_mem

theorem co2Pc_eq : co2Pc = co2P :=
  Subgroup.eq_of_le_of_card_ge co2Pc_le (by rw [card_co2P, card_co2Pc])

theorem orderOf_of_rep {p : ℕ} [hp : Fact p.Prime] {t : Array ℕ} {g : Equiv.Perm (Fin 2300)}
    (ht : Rep 2300 t g) (h1 : eqA 2300 (powArr 2300 t p) (idA 2300) = true)
    (h2 : eqA 2300 t (idA 2300) = false) : orderOf g = p := by
  refine orderOf_eq_prime ((eqA_iff (rep_powArr ht p) rep_idA).1 h1) fun hg => ?_
  rw [← Bool.not_eq_true, eqA_iff ht rep_idA] at h2
  exact h2 hg

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

instance fact_prime_twentythree : Fact (Nat.Prime 23) := ⟨by norm_num⟩

theorem orderOf_co2cGen_zero :
    orderOf (co2cGen 0) = 2 :=
  orderOf_of_rep (rep_co2cGen (by norm_num)) co2Conj_check.2.2.2.1 co2Conj_check.2.2.2.2.1

theorem orderOf_co2cGen_one :
    orderOf (co2cGen 1) = 5 :=
  orderOf_of_rep (rep_co2cGen (by norm_num)) co2Conj_check.2.2.2.2.2.1
    co2Conj_check.2.2.2.2.2.2.1

theorem orderOf_co2cGen_mul :
    orderOf (co2cGen 0 * co2cGen 1) = 23 :=
  orderOf_of_rep (rep_compA (rep_co2cGen (by norm_num)) (rep_co2cGen (by norm_num)))
    co2Conj_check.2.2.2.2.2.2.2.1 co2Conj_check.2.2.2.2.2.2.2.2

theorem natCard_Co2 :
    Nat.card Blueprint.NativeSporadic.Co2 = 42305421312000 := by
  rw [Nat.card_congr co2PermEquiv.toEquiv, card_co2P]

theorem fam_co2_order_coprime_generators :
    ValidSchreier co2Q ∧ ValidSchreier co2Qc ∧
    co2Q.base.toList.map Fin.val = [0, 1, 2, 3, 5, 4] ∧
    co2Qc.base.toList.map Fin.val = [0, 1, 3, 2, 5, 4] ∧
    (List.finRange co2Q.baseCount).map co2Q.orbitSize = [2300, 1408, 567, 192, 30, 4] ∧
    (List.finRange co2Qc.baseCount).map co2Qc.orbitSize = [2300, 1408, 567, 192, 30, 4] ∧
    co2cGen 0 = co2Gen 0 ∧ co2cGen 1 = co2W⁻¹ * co2Gen 1 * co2W ∧ co2Pc = co2P ∧
    Nat.card co2P = 42305421312000 ∧ MulAction.IsPretransitive co2P (Fin 2300) ∧
    Nat.card (MulAction.stabilizer co2P (0 : Fin 2300)) = 18393661440 ∧
    orderOf (co2cGen 0) = 2 ∧ orderOf (co2cGen 1) = 5 ∧ orderOf (co2cGen 0 * co2cGen 1) = 23 ∧
    Nat.gcd (orderOf (co2cGen 0)) (orderOf (co2cGen 1)) = 1 ∧
    Nat.gcd (orderOf (co2cGen 0 * co2cGen 1))
      (Nat.card (MulAction.stabilizer co2P (0 : Fin 2300))) = 1 ∧
    Nat.card Blueprint.NativeSporadic.Co2 = 42305421312000 := by
  refine ⟨co2Q_valid.1, co2Qc_valid.1, co2Q_base, co2Qc_base, co2Q_orbitSizes, co2Qc_orbitSizes,
    co2cGen_zero, co2cGen_one, co2Pc_eq, card_co2P, co2P_transitive, card_co2P_stabilizer,
    orderOf_co2cGen_zero, orderOf_co2cGen_one, orderOf_co2cGen_mul, ?_, ?_, ?_⟩
  · rw [orderOf_co2cGen_zero, orderOf_co2cGen_one]
    norm_num
  · rw [orderOf_co2cGen_mul, card_co2P_stabilizer]
    norm_num
  · exact natCard_Co2

end CFSG.Sporadic.Co2Cert
