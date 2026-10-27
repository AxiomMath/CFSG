module

public import CFSG.Sporadic.Schreier.Co3Order
public import CFSG.Sporadic.Schreier.Co3SylowCheck
public import CFSG.Certificates.NativeSchreierEnum
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Core

public noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.Co3.Native

theorem mem_co3P_of_sift
    {g : Array ℕ} {G : Equiv.Perm (Fin 276)} (hG : Rep 276 g G)
    (h : siftA 276 co3ChainLevels co3ChainBaseArr 0 g = true) : G ∈ co3P :=
  (siftA_iff_mem_originalSubgroup co3ChainArrays (by norm_num) co3Order_check.1 hG).1 h

theorem co3TArrs_size : co3TArrs.size = 10 := co3Field276_size' 5 rfl

theorem co3TArrs_inv : ∀ j < co3TArrs.size,
    isInvA 276 co3TArrs[j]! (rawInvs 276 co3TArrs)[j]! = true := by
  intro j hj
  rw [rawInvs, co3_getElem!_map hj]
  exact isInvA_co3Field276 (f := 5) (by norm_num) hj

theorem co3TArrays :
    ChainArrays co3TChain (co3TArrs.extract 0 co3TGenCount) co3TArrs
    co3TBaseArr (wordsArr co3TGenCount co3TStrongCount co3TDerivations) :=
  chainArrays_ofArrays co3TArrs_inv

@[expose] def co3TGen (k : ℕ) : Equiv.Perm (Fin 276) := permOfArr 276 co3TArrs[k]!

theorem rep_co3TGen
    {k : ℕ} (hk : k < 10) : Rep 276 co3TArrs[k]! (co3TGen k) :=
  (rep_permOfArr (co3TArrs_inv k (by rw [co3TArrs_size]; exact hk))).1

theorem co3T_eq : co3T = Subgroup.closure (Set.range fun k : Fin 8 => co3TGen k) := by
  rw [co3T, co3TChain, ofArrays_originalSubgroup]
  rfl

theorem co3TGen_mem {k : ℕ} (hk : k < 8) : co3TGen k ∈ co3T := by
  rw [co3T_eq]
  exact Subgroup.subset_closure ⟨⟨k, hk⟩, rfl⟩

theorem card_co3T :
    Nat.card co3T = 1024 := by
  rw [co3T, card_originalSubgroup_of_chainOK co3TArrays (by norm_num) co3TChain_check.1,
    co3TChain_check.2]
  rfl

theorem co3T_le_P :
    co3T ≤ co3P := by
  rw [co3T_eq, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  exact mem_co3P_of_sift (rep_co3TGen (by omega)) (co3TSift_check.1 k k.2)

theorem mem_co3T_of_sift
    {g : Array ℕ} {G : Equiv.Perm (Fin 276)} (hG : Rep 276 g G)
    (h : siftA 276 co3TLevels co3TBaseArr 0 g = true) : G ∈ co3T :=
  (siftA_iff_mem_originalSubgroup co3TArrays (by norm_num) co3TChain_check.1 hG).1 h

theorem rep_co3Z : Rep 276 co3ZArr co3Z :=
  (rep_permOfArr (isInvA_co3Field276 (f := 2) (k := 0) (by norm_num)
    (by rw [co3Field276_size]; decide))).1

theorem co3Z_mem_T :
    co3Z ∈ co3T := mem_co3T_of_sift rep_co3Z co3TSift_check.2.2.1

theorem co3Z_mem_P :
    co3Z ∈ co3P := mem_co3P_of_sift rep_co3Z co3TSift_check.2.1

theorem co3Z_mul_self :
    co3Z * co3Z = 1 :=
  eq_of_eqA (rep_compA rep_co3Z rep_co3Z) rep_idA co3TSift_check.2.2.2.2.1

theorem co3Z_ne_one : co3Z ≠ 1 := by
  intro h
  have h1 := co3TSift_check.2.2.2.2.2.1
  rw [← Bool.not_eq_true, eqA_iff rep_co3Z rep_idA] at h1
  exact h1 h

theorem orderOf_co3Z :
    orderOf co3Z = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [sq, co3Z_mul_self]) co3Z_ne_one

theorem co3Z_comm_gen
    {k : ℕ} (hk : k < 8) : co3Z * co3TGen k = co3TGen k * co3Z :=
  eq_of_eqA (rep_compA rep_co3Z (rep_co3TGen (by omega)))
    (rep_compA (rep_co3TGen (by omega)) rep_co3Z) (co3TSift_check.2.2.2.1 k hk)

theorem co3T_le_centralizer_Z :
    co3T ≤ Subgroup.centralizer {co3Z} := by
  rw [co3T_eq, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  exact (co3Z_comm_gen k.2).symm

theorem co3TExtract_get {k : ℕ} (hk : k < 8) : (co3TArrs.extract 0 8)[k]! = co3TArrs[k]! := by
  rw [getElem!_pos _ k (by simp [co3TArrs_size]; omega), getElem!_pos _ k (by
    rw [co3TArrs_size]; omega), Array.getElem_extract]
  simp

theorem co3T_center_iff
    (x : Equiv.Perm (Fin 276)) :
    (x ∈ co3T ∧ ∀ y ∈ co3T, x * y = y * x) ↔ x = 1 ∨ x = co3Z := by
  constructor
  · rintro ⟨hx, hc⟩
    have hF := chainCheckFacts co3TChain_check.1
    obtain ⟨a, ha, b, hb, c, hc', hprod⟩ := ChainArrays.exists_prod3 co3TArrays (by norm_num)
      co3TChain_check.1 (by decide) (fun i h3 hi => absurd hi (by
        change ¬ i < 3; omega)) hx
    have h0 : (0 : ℕ) < co3TChain.baseCount := by decide
    have h1 : (1 : ℕ) < co3TChain.baseCount := by decide
    have h2 : (2 : ℕ) < co3TChain.baseCount := by decide
    have hrep : Rep 276 (compA 276 (compA 276 (co3TLevels[0]!).tr[a]! (co3TLevels[1]!).tr[b]!)
        (co3TLevels[2]!).tr[c]!) x := by
      rw [← hprod]
      exact rep_compA (rep_compA (co3TArrays.rep_levT hF h0 ha) (co3TArrays.rep_levT hF h1 hb))
        (co3TArrays.rep_levT hF h2 hc')
    have hcheck := co3TSift_check.2.2.2.2.2.2
    unfold centerCheck3 at hcheck
    have hk := allLt_spec (allLt_spec (allLt_spec hcheck ha) hb) hc'
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at hk
    have hall : allLt (co3TArrs.extract 0 8).size (fun k => commutesA 276
        (compA 276 (compA 276 (co3TLevels[0]!).tr[a]! (co3TLevels[1]!).tr[b]!)
          (co3TLevels[2]!).tr[c]!) (co3TArrs.extract 0 8)[k]!) = true := by
      rw [allLt_iff]
      intro k hk8
      have hk8' : k < 8 := by simpa [co3TArrs_size] using hk8
      rw [co3TExtract_get hk8', commutesA]
      exact (eqA_iff (rep_compA hrep (rep_co3TGen (by omega)))
        (rep_compA (rep_co3TGen (by omega)) hrep)).2 (hc _ (co3TGen_mem hk8'))
    rcases hk with (hk | hk) | hk
    · rw [hall] at hk
      exact absurd hk (by decide)
    · exact Or.inl (eq_of_eqA hrep rep_idA hk)
    · exact Or.inr (eq_of_eqA hrep rep_co3Z hk)
  · rintro (rfl | rfl)
    · exact ⟨co3T.one_mem, fun y _ => by rw [one_mul, mul_one]⟩
    · refine ⟨co3Z_mem_T, fun y hy => ?_⟩
      exact (Subgroup.mem_centralizer_singleton_iff.1 (co3T_le_centralizer_Z hy)).symm

theorem co3T_centerIn :
    (CFSG.centerIn co3T : Set (Equiv.Perm (Fin 276))) = {1, co3Z} := by
  ext x
  rw [SetLike.mem_coe, CFSG.centerIn, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, SetLike.mem_coe]
  rw [← co3T_center_iff]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, fun y hy => (h2 y hy).symm⟩,
    fun ⟨h1, h2⟩ => ⟨h1, fun y hy => (h2 y hy).symm⟩⟩

theorem card_co3T_subgroupOf :
    Nat.card (co3T.subgroupOf co3P) = 1024 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe co3T_le_P).toEquiv, card_co3T]

theorem co3T_index :
    (co3T.subgroupOf co3P).index = 484147125 := by
  have h := (co3T.subgroupOf co3P).card_mul_index
  rw [card_co3T_subgroupOf, card_co3P] at h
  omega

theorem co3T_isPGroup :
    IsPGroup 2 (co3T.subgroupOf co3P) :=
  IsPGroup.of_card (n := 10) (by rw [card_co3T_subgroupOf]; norm_num)

theorem co3T_not_dvd_index :
    ¬ 2 ∣ (co3T.subgroupOf co3P).index := by
  rw [co3T_index]
  decide

@[expose] def co3TSylow :
    Sylow 2 co3P :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  co3T_isPGroup.toSylow co3T_not_dvd_index

theorem co3TSylow_coe :
    (co3TSylow : Subgroup co3P) = co3T.subgroupOf co3P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.toSylow_coe co3T_isPGroup co3T_not_dvd_index

theorem AT_Co3_Sylow_center :
    co3T ≤ co3P ∧ (∃ S : Sylow 2 co3P, (S : Subgroup co3P) = co3T.subgroupOf co3P) ∧
    Nat.card co3T = 1024 ∧
    (∀ x : Equiv.Perm (Fin 276), (x ∈ co3T ∧ ∀ y ∈ co3T, x * y = y * x) ↔ x = 1 ∨ x = co3Z) ∧
    (CFSG.centerIn co3T : Set (Equiv.Perm (Fin 276))) = {1, co3Z} ∧ orderOf co3Z = 2 :=
  ⟨co3T_le_P, ⟨co3TSylow, co3TSylow_coe⟩, card_co3T, co3T_center_iff, co3T_centerIn,
    orderOf_co3Z⟩

end CFSG.Sporadic.Schreier.Co3
