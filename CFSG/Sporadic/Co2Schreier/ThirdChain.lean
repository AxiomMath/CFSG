
module

public import CFSG.Sporadic.Co2Schreier.ThirdChainBase

public import CFSG.Sporadic.Co2Schreier.ThirdCheck
public import CFSG.Sporadic.Co2Schreier.Chains
public import CFSG.Sporadic.Co2Cert.Order
public import CFSG.Sporadic.Co2Schreier.ThirdCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.WitCheck
public meta import CFSG.Sporadic.Co2Schreier.SylowCheck
public meta import CFSG.Sporadic.Co2Schreier.CoreCheck
public meta import CFSG.Sporadic.Co2Cert.FaithfulCheck
public import CFSG.Sporadic.Co2Cert.CheckInputs
public import CFSG.Sporadic.Co2Cert.OrderCheckInputs

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert

theorem thirdFacts : ThirdFacts := by
  have h := third_check
  simp only [thirdCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem thB_size : thB.size = 13 := beq_iff_eq.1 thirdFacts.base_size

theorem thB_lt {j : ℕ} (hj : j < 13) : thB[j]! < 2300 := by
  have := allLt_iff.1 thirdFacts.base_lt j hj
  simpa using this

theorem thL_size : thL.size = 13 := beq_iff_eq.1 thirdFacts.L_size

theorem tsz_list :
    (List.range 13).map tsz = [2300, 891, 896, 96, 30, 1, 4, 1, 1, 1, 1, 1, 2] := by
  have h := beq_iff_eq.1 thirdFacts.sizes
  rw [← h]
  apply List.ext_getElem
  · simp [thL_size]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, Array.getElem_toList, tsz]
    rw [getElem!_pos thL i (by rw [thL_size]; simpa using h1)]

theorem tsz_eq {j : ℕ} (hj : j < 13) :
    tsz j = [2300, 891, 896, 96, 30, 1, 4, 1, 1, 1, 1, 1, 2].getD j 0 := by
  rw [← tsz_list, List.getD_eq_getElem _ _ (by simpa using hj)]
  simp

theorem tsz_pos {j : ℕ} (hj : j < 13) : 0 < tsz j := by
  rw [tsz_eq hj]
  interval_cases j <;> decide

theorem prod_tsz :
    ∏ j ∈ Finset.range 13, tsz j = 42305421312000 := by
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, tsz_eq (by norm_num : 0 < 13),
    tsz_eq (by norm_num : 1 < 13), tsz_eq (by norm_num : 2 < 13), tsz_eq (by norm_num : 3 < 13),
    tsz_eq (by norm_num : 4 < 13), tsz_eq (by norm_num : 5 < 13), tsz_eq (by norm_num : 6 < 13),
    tsz_eq (by norm_num : 7 < 13), tsz_eq (by norm_num : 8 < 13), tsz_eq (by norm_num : 9 < 13),
    tsz_eq (by norm_num : 10 < 13), tsz_eq (by norm_num : 11 < 13),
    tsz_eq (by norm_num : 12 < 13)]
  decide

theorem thFacts_tr {j k : ℕ} (hj : j < 13) (hk : k < tsz j) :
    isInvA 2300 thL[j]!.tr[k]! (invCand 2300 thL[j]!.tr[k]!) = true ∧
      fixesFirst thB thL[j]!.tr[k]! j = true ∧
      siftA 2300 (rawLevels 2300 co2StrongArrs co2BaseArr) co2BaseArr 0 thL[j]!.tr[k]! = true ∧
      ∀ k' < k, (thL[j]!.tr[k]!)[thB[j]!]! ≠ (thL[j]!.tr[k']!)[thB[j]!]! := by
  have h := allLt_iff.1 thirdFacts.tr j hj
  rw [Bool.and_eq_true] at h
  have h2 := allLt_iff.1 h.2 k hk
  simp only [Bool.and_eq_true] at h2
  obtain ⟨⟨⟨h3, h4⟩, h5⟩, h6⟩ := h2
  refine ⟨h3, h4, h5, fun k' hk' => ?_⟩
  have := allLt_iff.1 h6 k' hk'
  simpa using this

theorem thFacts_zero
    {j : ℕ} (hj : j < 13) : eqA 2300 thL[j]!.tr[0]! (idA 2300) = true := by
  have h := allLt_iff.1 thirdFacts.tr j hj
  rw [Bool.and_eq_true] at h
  exact h.1

theorem bpt_val
    {j : ℕ} (hj : j < 13) : (bpt j : ℕ) = thB[j]! := Nat.mod_eq_of_lt (thB_lt hj)

theorem rep_thT
    {j k : ℕ} (hj : j < 13) (hk : k < tsz j) : Rep 2300 thL[j]!.tr[k]! (thT j k) :=
  (rep_permOfArr (thFacts_tr hj hk).1).1

theorem thT_mem
    {j k : ℕ} (hj : j < 13) (hk : k < tsz j) : thT j k ∈ co2P := by
  rw [← co2Q_originalSubgroup]
  exact (siftA_iff_mem_originalSubgroup co2Q_chainArrays (by norm_num) co2Chain_check.1
    (rep_thT hj hk)).1 (thFacts_tr hj hk).2.2.1

theorem rep_apply_bpt
    {t : Array ℕ} {g : Equiv.Perm (Fin 2300)} (ht : Rep 2300 t g) {j : ℕ}
    (hj : j < 13) : (g (bpt j) : ℕ) = t[thB[j]!]! := by
  rw [← bpt_val hj]
  exact (ht (bpt j)).symm

theorem thT_fix
    {j k i : ℕ} (hj : j < 13) (hk : k < tsz j) (hi : i < j) :
    thT j k (bpt i) = bpt i := by
  apply Fin.ext
  rw [rep_apply_bpt (rep_thT hj hk) (j := i) (by omega), bpt_val (j := i) (by omega)]
  have := allLt_iff.1 (thFacts_tr hj hk).2.1 i hi
  simpa using this

theorem thT_inj
    {j k k' : ℕ} (hj : j < 13) (hk : k < tsz j) (hk' : k' < tsz j)
    (h : thT j k (bpt j) = thT j k' (bpt j)) : k = k' := by
  have h' := congrArg Fin.val h
  rw [rep_apply_bpt (rep_thT hj hk) hj, rep_apply_bpt (rep_thT hj hk') hj] at h'
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact (thFacts_tr hj hk').2.2.2 k hlt h'.symm
  · exact (thFacts_tr hj hk).2.2.2 k' hlt h'

theorem thT_zero {j : ℕ} (hj : j < 13) : thT j 0 = 1 :=
  eq_of_eqA (rep_thT hj (tsz_pos hj)) rep_idA (thFacts_zero hj)

theorem thT_mem_stabB
    {j k : ℕ} (hj : j < 13) (hk : k < tsz j) : thT j k ∈ stabB j :=
  ⟨thT_mem hj hk, fun _ hi => thT_fix hj hk hi⟩

@[expose] def phiB
    (j : ℕ) (hj : j < 13) : Fin (tsz j) × stabB (j + 1) → stabB j :=
  fun x => ⟨thT j x.1 * x.2, (stabB j).mul_mem (thT_mem_stabB hj x.1.2) (stabB_succ_le j x.2.2)⟩

theorem phiB_injective
    {j : ℕ} (hj : j < 13) : Function.Injective (phiB j hj) := by
  rintro ⟨k, s⟩ ⟨k', s'⟩ h
  have h1 : thT j k * (s : Equiv.Perm (Fin 2300)) = thT j k' * s' := congrArg Subtype.val h
  have hs : (s : Equiv.Perm (Fin 2300)) (bpt j) = bpt j := s.2.2 j (by omega)
  have hs' : (s' : Equiv.Perm (Fin 2300)) (bpt j) = bpt j := s'.2.2 j (by omega)
  have h2 := congrArg (fun g : Equiv.Perm (Fin 2300) => g (bpt j)) h1
  simp only [Equiv.Perm.mul_apply, hs, hs'] at h2
  have hkk : k = k' := Fin.ext (thT_inj hj k.2 k'.2 h2)
  subst hkk
  have : (s : Equiv.Perm (Fin 2300)) = s' := mul_left_cancel h1
  exact Prod.ext rfl (Subtype.ext this)

theorem card_stabB_le
    {j : ℕ} (hj : j < 13) :
    tsz j * Nat.card (stabB (j + 1)) ≤ Nat.card (stabB j) := by
  have h := Nat.card_le_card_of_injective _ (phiB_injective hj)
  rwa [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin] at h

theorem card_stabB
    {j : ℕ} (hj : j ≤ 13) :
    Nat.card (stabB j) = ∏ i ∈ Finset.Ico j 13, tsz i := by
  refine chain_card_eq (c := fun j => Nat.card (stabB j)) (t := tsz) (n := 13)
    (fun j hj => card_stabB_le hj) Nat.card_pos (fun j hj => tsz_pos hj) ?_ j hj
  exact le_of_eq (by rw [stabB_zero, card_co2P, prod_tsz])

theorem stabB_thirteen :
    stabB 13 = ⊥ := by
  rw [← Subgroup.card_eq_one, card_stabB le_rfl, Finset.Ico_self, Finset.prod_empty]

theorem card_stabB_succ
    {j : ℕ} (hj : j < 13) :
    Nat.card (stabB j) = tsz j * Nat.card (stabB (j + 1)) := by
  rw [card_stabB hj.le, card_stabB (j := j + 1) (by omega), Finset.prod_eq_prod_Ico_succ_bot hj]

theorem phiB_bijective
    {j : ℕ} (hj : j < 13) : Function.Bijective (phiB j hj) := by
  refine (Nat.bijective_iff_injective_and_card _).2 ⟨phiB_injective hj, ?_⟩
  rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin, card_stabB_succ hj]

theorem exists_thT_inv_mul_mem
    {j : ℕ} (hj : j < 13) {s : Equiv.Perm (Fin 2300)}
    (hs : s ∈ stabB j) : ∃ k < tsz j, (thT j k)⁻¹ * s ∈ stabB (j + 1) := by
  obtain ⟨⟨k, s'⟩, h⟩ := (phiB_bijective hj).2 ⟨s, hs⟩
  have h1 : thT j k * (s' : Equiv.Perm (Fin 2300)) = s := congrArg Subtype.val h
  refine ⟨k, k.2, ?_⟩
  rw [← h1, inv_mul_cancel_left]
  exact s'.2

theorem prodFrom_mem
    {k : ℕ → ℕ} : ∀ (f j : ℕ), j + f = 13 →
    (∀ i, j ≤ i → i < 13 → k i < tsz i) → prodFrom k f j ∈ stabB j
  | 0, j, hj, _ => by
    rw [prodFrom]
    exact (stabB j).one_mem
  | f + 1, j, hj, hk => by
    rw [prodFrom]
    exact (stabB j).mul_mem (thT_mem_stabB (by omega) (hk j le_rfl (by omega)))
      (stabB_succ_le j (prodFrom_mem f (j + 1) (by omega) fun i hi hi' => hk i (by omega) hi'))

theorem exists_prodFrom :
    ∀ (f j : ℕ), j + f = 13 → ∀ s ∈ stabB j,
    ∃ k : ℕ → ℕ, (∀ i, j ≤ i → i < 13 → k i < tsz i) ∧ s = prodFrom k f j
  | 0, j, hj, s, hs => by
    have h13 : j = 13 := by omega
    subst h13
    rw [stabB_thirteen, Subgroup.mem_bot] at hs
    exact ⟨fun _ => 0, fun i hi hi' => by omega, by rw [hs, prodFrom]⟩
  | f + 1, j, hj, s, hs => by
    obtain ⟨k0, hk0, hs'⟩ := exists_thT_inv_mul_mem (by omega) hs
    obtain ⟨k', hk', he⟩ := exists_prodFrom f (j + 1) (by omega) _ hs'
    refine ⟨Function.update k' j k0, fun i hi hi' => ?_, ?_⟩
    · rcases eq_or_lt_of_le hi with rfl | hlt
      · rw [Function.update_self]
        exact hk0
      · rw [Function.update_of_ne (by omega)]
        exact hk' i hlt hi'
    · rw [prodFrom, Function.update_self, prodFrom_congr f (j + 1) (k' := k')
        fun i hi => Function.update_of_ne (by omega) _ _, ← he, mul_inv_cancel_left]

theorem prodFrom_inj :
    ∀ (f j : ℕ), j + f = 13 → ∀ (k k' : ℕ → ℕ),
    (∀ i, j ≤ i → i < 13 → k i < tsz i) → (∀ i, j ≤ i → i < 13 → k' i < tsz i) →
    prodFrom k f j = prodFrom k' f j → ∀ i, j ≤ i → i < 13 → k i = k' i
  | 0, j, hj, _, _, _, _, _, i, hi, hi' => by omega
  | f + 1, j, hj, k, k', hk, hk', h, i, hi, hi' => by
    rw [prodFrom, prodFrom] at h
    have hm := prodFrom_mem f (j + 1) (by omega) fun i hi hi' => hk i (by omega) hi'
    have hm' := prodFrom_mem f (j + 1) (by omega) fun i hi hi' => hk' i (by omega) hi'
    have h2 := congrArg (fun g : Equiv.Perm (Fin 2300) => g (bpt j)) h
    simp only [Equiv.Perm.mul_apply, hm.2 j (by omega), hm'.2 j (by omega)] at h2
    have hkj : k j = k' j := thT_inj (by omega) (hk j le_rfl (by omega))
      (hk' j le_rfl (by omega)) h2
    rcases eq_or_lt_of_le hi with rfl | hlt
    · exact hkj
    · rw [hkj] at h
      exact prodFrom_inj f (j + 1) (by omega) k k' (fun i hi hi' => hk i (by omega) hi')
        (fun i hi hi' => hk' i (by omega) hi') (mul_left_cancel h) i hlt hi'

end CFSG.Sporadic.Co2Schreier
