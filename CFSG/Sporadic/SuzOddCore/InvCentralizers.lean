module

public import CFSG.Sporadic.SuzOddCore.InvChainCheck0
public import CFSG.Sporadic.SuzOddCore.InvChainCheck1
public import CFSG.Sporadic.SuzOddCore.InvChainCheck2
public import CFSG.Sporadic.SuzOddCore.InvChainCheck3
public import CFSG.Sporadic.SuzOddCore.InvTCheck
public import CFSG.Sporadic.SuzOddCore.InvGraphBound

public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] def centT (t : Equiv.Perm (Fin 1782)) : Subgroup (Equiv.Perm (Fin 1782)) :=
  Subgroup.centralizer {t} ⊓ suzT

@[expose] def centM (t : Equiv.Perm (Fin 1782)) : Subgroup (Equiv.Perm (Fin 1782)) :=
  Subgroup.centralizer {t} ⊓ suzM

theorem invRun_inv {i k : ℕ} (hi : i < 4) (hk : k < invRunCount i) :
    isInvA 1782 (invRun i k) (invCand 1782 (invRun i k)) = true :=
  (Bool.and_eq_true_iff.1 (invArrays_check.2.1 i hi k hk)).2

theorem invRunCount_ge (i : ℕ) : invOddStart i ≤ invRunCount i := by
  simp only [invRunCount]
  omega

theorem invFullGenArrs_get {i k : ℕ} (hk : k < (invFullGenArrs i).size) :
    (invFullGenArrs i)[k]! = invRun i (1 + k) := by
  rw [getElem!_pos _ k hk]
  simp [invFullGenArrs]

theorem invFullStrongArrs_get {i k : ℕ} (hk : k < (invFullStrongArrs i).size) :
    (invFullStrongArrs i)[k]! = invRun i (1 + invFullGenCounts.getD i 0 + k) := by
  rw [getElem!_pos _ k hk]
  simp [invFullStrongArrs]

theorem invInnerGenArrs_get {i k : ℕ} (hk : k < (invInnerGenArrs i).size) :
    (invInnerGenArrs i)[k]! = invRun i (invInnerStart i + k) := by
  rw [getElem!_pos _ k hk]
  simp [invInnerGenArrs]

theorem invInnerStrongArrs_get {i k : ℕ} (hk : k < (invInnerStrongArrs i).size) :
    (invInnerStrongArrs i)[k]! = invRun i (invInnerStart i + invInnerGenCounts.getD i 0 + k) := by
  rw [getElem!_pos _ k hk]
  simp [invInnerStrongArrs]

theorem invFullBase_vals {i : ℕ} (hi : i < 4) :
    ((invFullBase i).map Fin.val).toArray = (invFullBases.getD i []).toArray := by
  interval_cases i <;> rfl

theorem invInnerBase_vals {i : ℕ} (hi : i < 4) :
    ((invInnerBase i).map Fin.val).toArray = (invInnerBases.getD i []).toArray := by
  interval_cases i <;> rfl

theorem invFullChain_arrays {i : ℕ} (hi : i < 4) :
    ChainArrays (invFullChain i) (invFullGenArrs i) (invFullStrongArrs i)
      (invFullBases.getD i []).toArray (invFullDerivs i) := by
  rw [← invFullBase_vals hi]
  refine chainArrays_rawOfArrays (fun k hk => ?_) (fun j hj => ?_)
  · rw [invFullGenArrs_get hk]
    refine invRun_inv hi ?_
    have : k < invFullGenCounts.getD i 0 := by simpa [invFullGenArrs] using hk
    have h2 := invRunCount_ge i
    simp only [invOddStart, invInnerStart] at h2
    omega
  · rw [invFullStrongArrs_get hj]
    refine invRun_inv hi ?_
    have : j < invFullStrongCounts.getD i 0 := by simpa [invFullStrongArrs] using hj
    have h2 := invRunCount_ge i
    simp only [invOddStart, invInnerStart] at h2
    omega

theorem invInnerChain_arrays {i : ℕ} (hi : i < 4) :
    ChainArrays (invInnerChain i) (invInnerGenArrs i) (invInnerStrongArrs i)
      (invInnerBases.getD i []).toArray (invInnerDerivs i) := by
  rw [← invInnerBase_vals hi]
  refine chainArrays_rawOfArrays (fun k hk => ?_) (fun j hj => ?_)
  · rw [invInnerGenArrs_get hk]
    refine invRun_inv hi ?_
    have : k < invInnerGenCounts.getD i 0 := by simpa [invInnerGenArrs] using hk
    have h2 := invRunCount_ge i
    simp only [invOddStart] at h2
    omega
  · rw [invInnerStrongArrs_get hj]
    refine invRun_inv hi ?_
    have : j < invInnerStrongCounts.getD i 0 := by simpa [invInnerStrongArrs] using hj
    have h2 := invRunCount_ge i
    simp only [invOddStart] at h2
    omega

theorem invChain_check
    {i : ℕ} (hi : i < 4) :
    rawChainOK 1782 (invFullGenArrs i) (invFullStrongArrs i) (invFullBases.getD i []).toArray
      (invFullDerivs i) 4 = true ∧
    (rawOrbitSizes 1782 (invFullStrongArrs i) (invFullBases.getD i []).toArray).prod =
      invFullOrders.getD i 0 ∧
    rawChainOK 1782 (invInnerGenArrs i) (invInnerStrongArrs i) (invInnerBases.getD i []).toArray
      (invInnerDerivs i) 4 = true ∧
    (rawOrbitSizes 1782 (invInnerStrongArrs i) (invInnerBases.getD i []).toArray).prod =
      invInnerOrders.getD i 0 := by
  interval_cases i
  · exact invChain_check_0
  · exact invChain_check_1
  · exact invChain_check_2
  · exact invChain_check_3

theorem invChains_valid
    {i : ℕ} (hi : i < 4) :
    ValidSchreier (invFullChain i) ∧ ValidSchreier (invInnerChain i) :=
  ⟨(validSchreier_of_chainOK (invFullChain_arrays hi) (by norm_num) (invChain_check hi).1).1,
    (validSchreier_of_chainOK (invInnerChain_arrays hi) (by norm_num)
      (invChain_check hi).2.2.1).1⟩

theorem card_invD
    {i : ℕ} (hi : i < 4) : Nat.card (invD i) = invFullOrders.getD i 0 := by
  rw [invD, card_originalSubgroup_of_chainOK (invFullChain_arrays hi) (by norm_num)
    (invChain_check hi).1, (invChain_check hi).2.1]

theorem card_invE
    {i : ℕ} (hi : i < 4) : Nat.card (invE i) = invInnerOrders.getD i 0 := by
  rw [invE, card_originalSubgroup_of_chainOK (invInnerChain_arrays hi) (by norm_num)
    (invChain_check hi).2.2.1, (invChain_check hi).2.2.2]

theorem suzInv_sq
    {i : ℕ} (hi : i < 4) : suzInv i * suzInv i = 1 :=
  eq_of_eqA (rep_compA (rep_suzInv hi) (rep_suzInv hi)) rep_idA (invT_check.1 i hi).1

theorem suzInv_ne_one
    {i : ℕ} (hi : i < 4) : suzInv i ≠ 1 := by
  intro h
  have := (eqA_iff (rep_suzInv hi) rep_idA).2 h
  rw [(invT_check.1 i hi).2.1] at this
  exact Bool.false_ne_true this

theorem orderOf_suzInv
    {i : ℕ} (hi : i < 4) : orderOf (suzInv i) = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact suzInv_sq hi) (suzInv_ne_one hi)

theorem suzInv_inv
    {i : ℕ} (hi : i < 4) : (suzInv i)⁻¹ = suzInv i := by
  rw [inv_eq_iff_mul_eq_one, suzInv_sq hi]

theorem fixedCount_eq {t : Array ℕ} {T : Equiv.Perm (Fin 1782)} (ht : Rep 1782 t T) :
    fixedCount t = (Finset.univ.filter fun x : Fin 1782 => T x = x).card := by
  rw [fixedCount]
  apply congrArg Finset.card
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [ht x]
  exact ⟨fun h => Fin.ext h, fun h => by rw [h]⟩

theorem suzInv_fixed
    {i : ℕ} (hi : i < 4) :
    (Finset.univ.filter fun x : Fin 1782 => suzInv i x = x).card = invFixedCounts.getD i 0 := by
  rw [← fixedCount_eq (rep_suzInv hi)]
  exact (invT_check.1 i hi).2.2

theorem inM_iff
    {g : Array ℕ} {G : Equiv.Perm (Fin 1782)} (hG : Rep 1782 g G) :
    inM g = true ↔ G ∈ suzM := mem_suzM_iff_siftA hG

theorem commutesA_iff {g t : Array ℕ} {G T : Equiv.Perm (Fin 1782)} (hG : Rep 1782 g G)
    (hT : Rep 1782 t T) : commutesA g t = true ↔ G * T = T * G :=
  eqA_iff (rep_compA hG hT) (rep_compA hT hG)

theorem invD_le_centT
    {i : ℕ} (hi : i < 4) : invD i ≤ centT (suzInv i) := by
  rw [invD, RawSchreierDatum.originalSubgroup, Subgroup.closure_le]
  intro g hg
  obtain ⟨k, rfl⟩ := (schreier_vector_mem_toList_iff_get _ g).1 hg
  have hrep := (invFullChain_arrays hi).orig k
  have hk : (k : ℕ) < invFullGenCounts.getD i 0 := by
    have := k.2
    change (k : ℕ) < (invFullGenArrs i).size at this
    simpa [invFullGenArrs] using this
  obtain ⟨hmem, hcomm⟩ := invT_check.2.2.2.2.2.1 i hi k hk
  refine ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, ?_⟩
  · exact (commutesA_iff hrep (rep_suzInv hi)).1 hcomm
  · change (invFullChain i).original.get k ∈ suzT
    rw [mem_suzT_iff]
    rcases hmem with h | h
    · exact Or.inl ((inM_iff hrep).1 h)
    · exact Or.inr ((inM_iff (rep_compA rep_v hrep)).1 h)

theorem invE_le_centM
    {i : ℕ} (hi : i < 4) : invE i ≤ centM (suzInv i) := by
  rw [invE, RawSchreierDatum.originalSubgroup, Subgroup.closure_le]
  intro g hg
  obtain ⟨k, rfl⟩ := (schreier_vector_mem_toList_iff_get _ g).1 hg
  have hrep := (invInnerChain_arrays hi).orig k
  have hk : (k : ℕ) < invInnerGenCounts.getD i 0 := by
    have := k.2
    change (k : ℕ) < (invInnerGenArrs i).size at this
    simpa [invInnerGenArrs] using this
  obtain ⟨hmem, hcomm⟩ := invT_check.2.2.2.2.2.2.2 i hi k hk
  exact ⟨Subgroup.mem_centralizer_singleton_iff.2
    ((commutesA_iff hrep (rep_suzInv hi)).1 hcomm), (inM_iff hrep).1 hmem⟩

theorem invD_eq_centT
    {i : ℕ} (hi : i < 4) : invD i = centT (suzInv i) := by
  refine Subgroup.eq_of_le_of_card_ge (invD_le_centT hi) ?_
  rw [card_invD hi]
  have := card_centralizer_le hi
  rw [show invGraphBounds = invFullOrders from rfl] at this
  exact this

theorem centM_eq
    {i : ℕ} (hi : i < 4) : centM (suzInv i) = invD i ⊓ suzM := by
  rw [invD_eq_centT hi, centT, centM, inf_assoc, inf_eq_right.2 suzM_le_suzT]

theorem invD_not_le_M
    {i : ℕ} (hi : i < 4) : ¬ invD i ≤ suzM := by
  intro hle
  obtain ⟨k, hk, hkM⟩ := invT_check.2.2.2.2.2.2.1 i hi
  have hk' : k < (invFullChain i).originalCount := by
    change k < (invFullGenArrs i).size
    simpa [invFullGenArrs] using hk
  have hrep := (invFullChain_arrays hi).orig ⟨k, hk'⟩
  have hmem : (invFullChain i).original.get ⟨k, hk'⟩ ∈ invD i :=
    Subgroup.subset_closure (schreier_vector_get_mem_toList _ _)
  have := (inM_iff hrep).2 (hle hmem)
  rw [hkM] at this
  exact Bool.false_ne_true this

theorem card_invD_inf_M_le
    {i : ℕ} (hi : i < 4) :
    2 * Nat.card (invD i ⊓ suzM : Subgroup (Equiv.Perm (Fin 1782))) ≤ Nat.card (invD i) := by
  have h := ((invD i ⊓ suzM).subgroupOf (invD i)).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h
  have hne : ((invD i ⊓ suzM).subgroupOf (invD i)).index ≠ 1 := by
    rw [Ne, Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top]
    intro hle
    exact invD_not_le_M hi (hle.trans inf_le_right)
  have hpos : ((invD i ⊓ suzM).subgroupOf (invD i)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rw [← h]
  have : 2 ≤ ((invD i ⊓ suzM).subgroupOf (invD i)).index := by omega
  calc 2 * Nat.card (invD i ⊓ suzM : Subgroup (Equiv.Perm (Fin 1782)))
      ≤ ((invD i ⊓ suzM).subgroupOf (invD i)).index *
        Nat.card (invD i ⊓ suzM : Subgroup (Equiv.Perm (Fin 1782))) :=
        Nat.mul_le_mul_right _ this
    _ = _ := by ring

theorem invE_eq_centM
    {i : ℕ} (hi : i < 4) : invE i = centM (suzInv i) := by
  refine Subgroup.eq_of_le_of_card_ge (invE_le_centM hi) ?_
  rw [centM_eq hi]
  have h1 := card_invD_inf_M_le hi
  rw [card_invD hi] at h1
  rw [card_invE hi]
  interval_cases i <;> norm_num [invFullOrders, invInnerOrders] at h1 ⊢ <;> omega

theorem invE_le_invD
    {i : ℕ} (hi : i < 4) : invE i ≤ invD i := by
  rw [invE_eq_centM hi, centM_eq hi]
  exact inf_le_left

theorem invE_index
    {i : ℕ} (hi : i < 4) : ((invE i).subgroupOf (invD i)).index = 2 := by
  have h := ((invE i).subgroupOf (invD i)).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (invE_le_invD hi)).toEquiv, card_invE hi,
    card_invD hi] at h
  interval_cases i <;> norm_num [invFullOrders, invInnerOrders] at h <;> omega

end CFSG.Sporadic.SuzOddCore
