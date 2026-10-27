module

public import CFSG.Sporadic.Schreier.Co3CentralizerCheck
public import CFSG.Sporadic.Schreier.Co3StabIt
public import CFSG.LocalAnalysis.ComponentInitial.AutomorphismRealization

public noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.Co3.Native CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

theorem co3_centralizer_mk_eq {G : Type*} [Group G] {H : Subgroup G} {x : G} (hx : x ∈ H) :
    Subgroup.centralizer {(⟨x, hx⟩ : H)} = (Subgroup.centralizer {x}).subgroupOf H := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf,
    Subgroup.mem_centralizer_singleton_iff, Subtype.ext_iff]
  rfl

theorem co3MArrs_size : co3MArrs.size = 14 := co3Field276_size' 6 rfl

theorem co3M1Arrs_size : co3M1Arrs.size = 11 := co3Field276_size' 7 rfl

theorem co3MArrs_inv : ∀ j < co3MArrs.size,
    isInvA 276 co3MArrs[j]! (rawInvs 276 co3MArrs)[j]! = true := by
  intro j hj
  rw [rawInvs, co3_getElem!_map hj]
  exact isInvA_co3Field276 (f := 6) (by norm_num) hj

theorem co3M1Arrs_inv : ∀ j < co3M1Arrs.size,
    isInvA 276 co3M1Arrs[j]! (rawInvs 276 co3M1Arrs)[j]! = true := by
  intro j hj
  rw [rawInvs, co3_getElem!_map hj]
  exact isInvA_co3Field276 (f := 7) (by norm_num) hj

theorem co3MArrays :
    ChainArrays co3MChain (co3MArrs.extract 0 co3MGenCount) co3MArrs
    co3MBaseArr (wordsArr co3MGenCount co3MStrongCount co3MDerivations) :=
  chainArrays_ofArrays co3MArrs_inv

theorem co3M1Arrays :
    ChainArrays co3M1Chain (co3M1Arrs.extract 0 co3M1GenCount) co3M1Arrs
    co3M1BaseArr (wordsArr co3M1GenCount co3M1StrongCount co3M1Derivations) :=
  chainArrays_ofArrays co3M1Arrs_inv

theorem rep_co3MArr
    {k : ℕ} (hk : k < 14) : Rep 276 co3MArrs[k]! (permOfArr 276 co3MArrs[k]!) :=
  (rep_permOfArr (co3MArrs_inv k (by rw [co3MArrs_size]; exact hk))).1

theorem rep_co3M1Arr {k : ℕ} (hk : k < 11) :
    Rep 276 co3M1Arrs[k]! (permOfArr 276 co3M1Arrs[k]!) :=
  (rep_permOfArr (co3M1Arrs_inv k (by rw [co3M1Arrs_size]; exact hk))).1

theorem co3M_eq :
    co3M = Subgroup.closure (Set.range fun k : Fin 7 => permOfArr 276 co3MArrs[(k : ℕ)]!) := by
  rw [co3M, co3MChain, ofArrays_originalSubgroup]
  rfl

theorem co3M1_eq :
    co3M1 = Subgroup.closure (Set.range fun k : Fin 6 => permOfArr 276 co3M1Arrs[(k : ℕ)]!) := by
  rw [co3M1, co3M1Chain, ofArrays_originalSubgroup]
  rfl

theorem card_co3M :
    Nat.card co3M = 2903040 := by
  rw [co3M, card_originalSubgroup_of_chainOK co3MArrays (by norm_num) co3MChain_check.1,
    co3MChain_check.2]
  rfl

theorem card_co3M1 :
    Nat.card co3M1 = 190080 := by
  rw [co3M1, card_originalSubgroup_of_chainOK co3M1Arrays (by norm_num) co3M1Chain_check.1,
    co3M1Chain_check.2]
  rfl

theorem co3M_le_P :
    co3M ≤ co3P := by
  rw [co3M_eq, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  exact mem_co3P_of_sift (rep_co3MArr (by omega)) (co3Centralizer_check.1 k k.2).1

theorem co3M1_le_P :
    co3M1 ≤ co3P := by
  rw [co3M1_eq, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  exact mem_co3P_of_sift (rep_co3M1Arr (by omega)) (co3Centralizer_check.2.1 k k.2).1

theorem rep_co3Tt : Rep 276 co3TtArr co3Tt :=
  (rep_permOfArr (isInvA_co3Field276 (f := 3) (k := 0) (by norm_num)
    (by rw [co3Field276_size]; decide))).1

theorem co3M_le_centralizer :
    co3M ≤ Subgroup.centralizer {co3Z} := by
  rw [co3M_eq, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  exact eq_of_eqA (rep_compA (rep_co3MArr (by omega)) rep_co3Z)
    (rep_compA rep_co3Z (rep_co3MArr (by omega))) (co3Centralizer_check.1 k k.2).2

theorem co3M1_le_centralizer :
    co3M1 ≤ Subgroup.centralizer {co3Tt} := by
  rw [co3M1_eq, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  exact eq_of_eqA (rep_compA (rep_co3M1Arr (by omega)) rep_co3Tt)
    (rep_compA rep_co3Tt (rep_co3M1Arr (by omega))) (co3Centralizer_check.2.1 k k.2).2

theorem mem_co3M_of_sift
    {g : Array ℕ} {G : Equiv.Perm (Fin 276)} (hG : Rep 276 g G)
    (h : siftA 276 co3MLevels co3MBaseArr 0 g = true) : G ∈ co3M :=
  (siftA_iff_mem_originalSubgroup co3MArrays (by norm_num) co3MChain_check.1 hG).1 h

theorem co3Tt_mem_T :
    co3Tt ∈ co3T :=
  mem_co3T_of_sift rep_co3Tt co3Centralizer_check.2.2.2.2.1

theorem co3Tt_mem_M : co3Tt ∈ co3M :=
  mem_co3M_of_sift rep_co3Tt co3Centralizer_check.2.2.2.2.2.1

theorem co3Tt_mem_P :
    co3Tt ∈ co3P := co3T_le_P co3Tt_mem_T

theorem co3Tt_mul_self :
    co3Tt * co3Tt = 1 :=
  eq_of_eqA (rep_compA rep_co3Tt rep_co3Tt) rep_idA co3Centralizer_check.2.2.1

theorem co3Tt_ne_one : co3Tt ≠ 1 := by
  intro h
  have h1 := co3Centralizer_check.2.2.2.1
  rw [← Bool.not_eq_true, eqA_iff rep_co3Tt rep_idA] at h1
  exact h1 h

theorem orderOf_co3Tt :
    orderOf co3Tt = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [sq, co3Tt_mul_self]) co3Tt_ne_one

theorem co3Iz_fixed :
    finSet 276 co3IzNat = {p : Fin 276 | co3Z p = p} := by
  rw [← co3Centralizer_check.2.2.2.2.2.2.1, finSet_fixedList rep_co3Z]

theorem co3It_fixed :
    finSet 276 co3ItNat = {p : Fin 276 | co3Tt p = p} := by
  rw [← co3Centralizer_check.2.2.2.2.2.2.2, finSet_fixedList rep_co3Tt]

theorem co3Iz_spec
    (p : Fin 276) : (p : ℕ) ∈ co3IzNat ↔ co3Z p = p := by
  have := congrArg (fun s : Set (Fin 276) => p ∈ s) co3Iz_fixed
  simpa [finSet] using this

theorem co3It_spec
    (p : Fin 276) : (p : ℕ) ∈ co3ItNat ↔ co3Tt p = p := by
  have := congrArg (fun s : Set (Fin 276) => p ∈ s) co3It_fixed
  simpa [finSet] using this

theorem keysSortedOK_nodup {sets : Array (List ℕ)} (h : keysSortedOK sets = true) :
    sets.toList.Nodup := by
  have hchain : ∀ l : List ℕ, strictlyIncreasing l = true → l.Pairwise (· < ·) := by
    intro l hl
    rw [← List.isChain_iff_pairwise]
    induction l with
    | nil => exact List.IsChain.nil
    | cons a l ih =>
      cases l with
      | nil => exact List.IsChain.singleton a
      | cons b l =>
        simp only [strictlyIncreasing, Bool.and_eq_true, decide_eq_true_eq] at hl
        exact List.IsChain.cons_cons hl.1 (ih hl.2)
  have h1 := (hchain _ h).nodup
  have h2 : (sets.toList.map setKey).Nodup := ((List.mergeSort_perm _ _).nodup_iff).1 h1
  exact h2.of_map setKey

theorem co3OrigArrs_size : co3OrigArrs.size = 2 := by
  simp [co3OrigArrs, co3ChainArrs_size]

theorem rep_co3OrigArrs :
    ∀ k < co3OrigArrs.size, Rep 276 co3OrigArrs[k]! (co3GenPerm k) := by
  intro k hk
  rw [co3OrigArrs_size] at hk
  have e : co3OrigArrs[k]! = co3ChainArrs[k]! := by
    rw [co3OrigArrs, getElem!_pos _ k (by simp [co3ChainArrs_size]; omega),
      getElem!_pos _ k (by rw [co3ChainArrs_size]; omega), Array.getElem_extract]
    simp
  rw [e]
  exact rep_co3GenPerm hk

theorem co3GenPerm_mem' : ∀ k < co3OrigArrs.size, co3GenPerm k ∈ co3P := by
  intro k hk
  rw [co3OrigArrs_size] at hk
  exact co3GenPerm_mem k hk

theorem pointList_co3IzNat : PointList 276 co3IzNat := by
  rw [← co3Centralizer_check.2.2.2.2.2.2.1]
  exact pointList_fixedList _

theorem pointList_co3ItNat : PointList 276 co3ItNat := by
  rw [← co3Centralizer_check.2.2.2.2.2.2.2]
  exact pointList_fixedList _

theorem co3Iz_orbit :
    170775 ≤ (Set.range fun g : co3P => g • finSet 276 co3IzNat).ncard := by
  have h := le_ncard_orbit_of_translatesOK (H := co3P) rep_co3OrigArrs co3GenPerm_mem'
    pointList_co3IzNat co3OrbitZ_check.1 (keysSortedOK_nodup co3OrbitZ_check.2.1)
  rw [co3OrbitZ_check.2.2] at h
  exact h

theorem co3It_orbit :
    2608200 ≤ (Set.range fun g : co3P => g • finSet 276 co3ItNat).ncard :=
  co3It_orbit_ge

@[expose] def co3ZP :
    co3P := ⟨co3Z, co3Z_mem_P⟩

@[expose] def co3TtP :
    co3P := ⟨co3Tt, co3Tt_mem_P⟩

theorem co3M_subgroupOf_index :
    (co3M.subgroupOf co3P).index = 170775 := by
  have h := (co3M.subgroupOf co3P).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe co3M_le_P).toEquiv, card_co3M,
    card_co3P] at h
  omega

theorem co3M1_subgroupOf_index :
    (co3M1.subgroupOf co3P).index = 2608200 := by
  have h := (co3M1.subgroupOf co3P).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe co3M1_le_P).toEquiv, card_co3M1,
    card_co3P] at h
  omega

theorem fixedSet_co3ZP :
    {p : Fin 276 | co3ZP • p = p} = finSet 276 co3IzNat := by
  rw [co3Iz_fixed, co3ZP]
  ext p
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, Subgroup.mk_smul, Equiv.Perm.smul_def]

theorem fixedSet_co3TtP :
    {p : Fin 276 | co3TtP • p = p} = finSet 276 co3ItNat := by
  rw [co3It_fixed, co3TtP]
  ext p
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, Subgroup.mk_smul, Equiv.Perm.smul_def]

theorem co3M_subgroupOf_eq :
    co3M.subgroupOf co3P = Subgroup.centralizer {co3ZP} := by
  have hH : co3M.subgroupOf co3P ≤ Subgroup.centralizer {co3ZP} := by
    intro g hg
    rw [co3ZP, co3_centralizer_mk_eq, Subgroup.mem_subgroupOf]
    exact co3M_le_centralizer (Subgroup.mem_subgroupOf.1 hg)
  have horb : (co3M.subgroupOf co3P).index ≤
      (Set.range fun g : co3P => g • {p : Fin 276 | co3ZP • p = p}).ncard := by
    rw [co3M_subgroupOf_index, fixedSet_co3ZP]
    exact co3Iz_orbit
  exact (fixed_point_set_orbit_centralizer_bound co3ZP _ hH horb).1

theorem co3M1_subgroupOf_eq :
    co3M1.subgroupOf co3P = Subgroup.centralizer {co3TtP} := by
  have hH : co3M1.subgroupOf co3P ≤ Subgroup.centralizer {co3TtP} := by
    intro g hg
    rw [co3TtP, co3_centralizer_mk_eq, Subgroup.mem_subgroupOf]
    exact co3M1_le_centralizer (Subgroup.mem_subgroupOf.1 hg)
  have horb : (co3M1.subgroupOf co3P).index ≤
      (Set.range fun g : co3P => g • {p : Fin 276 | co3TtP • p = p}).ncard := by
    rw [co3M1_subgroupOf_index, fixedSet_co3TtP]
    exact co3It_orbit
  exact (fixed_point_set_orbit_centralizer_bound co3TtP _ hH horb).1

theorem co3M_eq_centralizer :
    co3M = co3P ⊓ Subgroup.centralizer {co3Z} := by
  have h := co3M_subgroupOf_eq
  rw [co3ZP, co3_centralizer_mk_eq, Subgroup.subgroupOf_inj] at h
  rw [inf_comm, ← h]
  exact (inf_eq_left.2 co3M_le_P).symm

theorem co3M1_eq_centralizer :
    co3M1 = co3P ⊓ Subgroup.centralizer {co3Tt} := by
  have h := co3M1_subgroupOf_eq
  rw [co3TtP, co3_centralizer_mk_eq, Subgroup.subgroupOf_inj] at h
  rw [inf_comm, ← h]
  exact (inf_eq_left.2 co3M1_le_P).symm

theorem AT_Co3_exact_involution_centralizers :
    co3M = co3P ⊓ Subgroup.centralizer {co3Z} ∧ Nat.card co3M = 2903040 ∧
    co3M1 = co3P ⊓ Subgroup.centralizer {co3Tt} ∧ Nat.card co3M1 = 190080 ∧
    co3Tt ∈ co3T ⊓ co3M ∧ orderOf co3Tt = 2 ∧
    (∀ p : Fin 276, (p : ℕ) ∈ co3IzNat ↔ co3Z p = p) ∧ co3IzNat.Pairwise (· < ·) ∧
      co3IzNat.length = 36 ∧
    (∀ p : Fin 276, (p : ℕ) ∈ co3ItNat ↔ co3Tt p = p) ∧ co3ItNat.Pairwise (· < ·) ∧
      co3ItNat.length = 12 ∧
    170775 ≤ (Set.range fun g : co3P => g • finSet 276 co3IzNat).ncard ∧
    2608200 ≤ (Set.range fun g : co3P => g • finSet 276 co3ItNat).ncard :=
  ⟨co3M_eq_centralizer, card_co3M, co3M1_eq_centralizer, card_co3M1,
    Subgroup.mem_inf.2 ⟨co3Tt_mem_T, co3Tt_mem_M⟩, orderOf_co3Tt, co3Iz_spec,
    pointList_co3IzNat.sorted, rfl, co3It_spec, pointList_co3ItNat.sorted, rfl, co3Iz_orbit,
    co3It_orbit⟩

end CFSG.Sporadic.Schreier.Co3
