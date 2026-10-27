module

public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXAlternatingPCycles
import CFSG.RankThree.Classical2.UnitarySplitPrimeRank
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.RankThree.GroupTheory

open Equiv Equiv.Perm Subgroup

variable {n p k : ℕ}

@[expose] def blockEquiv (hkp : k * p ≤ n) (i : Fin k) :
    Fin p ≃ {x : Fin n // i.val * p ≤ x.val ∧ x.val < i.val * p + p} where
  toFun j := ⟨⟨i.val * p + j.val, by
      have h1 : (i.val + 1) * p ≤ k * p := Nat.mul_le_mul_right p i.2
      have h2 := j.2
      rw [add_mul, one_mul] at h1
      omega⟩, by
    exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left j.2 _⟩⟩
  invFun x := ⟨x.1.val - i.val * p, by have := x.2; omega⟩
  left_inv j := by
    apply Fin.ext
    simp
  right_inv x := by
    apply Subtype.ext
    apply Fin.ext
    have := x.2
    simp only
    omega

@[expose] def blockCycle (hkp : k * p ≤ n) (i : Fin k) : Perm (Fin n) :=
  (finRotate p).extendDomain (blockEquiv hkp i)

theorem blockCycle_isCycle_card (hp2 : 2 ≤ p) (hkp : k * p ≤ n) (i : Fin k) :
    (blockCycle hkp i).IsCycle ∧ (blockCycle hkp i).support.card = p ∧
      ∀ x ∈ (blockCycle hkp i).support, i.val * p ≤ x.val ∧ x.val < i.val * p + p := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 2 := ⟨p - 2, by omega⟩
  refine ⟨isCycle_finRotate.extendDomain _, ?_, fun x hx => ?_⟩
  · rw [blockCycle, support_extend_domain, Finset.card_map, support_finRotate, Finset.card_univ,
      Fintype.card_fin]
  · rw [blockCycle, support_extend_domain, Finset.mem_map] at hx
    obtain ⟨j, -, rfl⟩ := hx
    exact ((blockEquiv hkp i) j).2

theorem blockCycle_mem_alternatingGroup (hp : p.Prime) (hp2 : p ≠ 2) (hkp : k * p ≤ n)
    (i : Fin k) : blockCycle hkp i ∈ alternatingGroup (Fin n) := by
  obtain ⟨hcyc, hcard, -⟩ := blockCycle_isCycle_card hp.two_le hkp i
  rw [mem_alternatingGroup, hcyc.sign, hcard, (hp.odd_of_ne_two hp2).neg_one_pow, neg_neg]

open CFSG.Assembly.RankThreeEven (localRank) in
theorem alternating_central_cover_two_local_prime_rank_witness {G : Type*} [Group G] [Finite G]
    {K : Subgroup G} (hp : p.Prime) (hp3 : 3 < p) (hk : 1 ≤ k) (hn : k * p + 4 ≤ n)
    (π : K →* alternatingGroup (Fin n)) (hπ : Function.Surjective π)
    (hZ : π.ker ≤ Subgroup.center K) :
    (∃ u : G, u ∈ K ∧ orderOf u = 2 ∧ ∃ V : Subgroup G,
      V ≤ K ⊓ Subgroup.centralizer ({u} : Set G) ∧ CFSG.IsElementaryAbelian p V ∧
        Nat.card V = p ^ k) ∧ k ≤ localRank p G := by
  have : Fact p.Prime := ⟨hp⟩
  have hkp : k * p ≤ n := by omega
  have hp2 : p ≠ 2 := by omega
  have hp5 : 5 ≤ p := by
    rcases (show p = 4 ∨ 5 ≤ p by omega) with h | h
    · exact absurd hp (h ▸ by decide)
    · exact h
  set c : Fin k → alternatingGroup (Fin n) := fun i =>
    ⟨blockCycle hkp i, blockCycle_mem_alternatingGroup hp hp2 hkp i⟩
  set Ω : Fin k → Finset (Fin n) := fun i => (blockCycle hkp i).support
  have hΩ : ∀ i, (Ω i).card = p := fun i => (blockCycle_isCycle_card hp.two_le hkp i).2.1
  have hdisj : Pairwise fun i j => Disjoint (Ω i) (Ω j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    have hi := (blockCycle_isCycle_card hp.two_le hkp i).2.2 x hxi
    have hj := (blockCycle_isCycle_card hp.two_le hkp j).2.2 x hxj
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
    · have h1 : (i.val + 1) * p ≤ j.val * p := Nat.mul_le_mul_right p h
      rw [add_mul, one_mul] at h1
      omega
    · have h1 : (j.val + 1) * p ≤ i.val * p := Nat.mul_le_mul_right p h
      rw [add_mul, one_mul] at h1
      omega
  have hc : ∀ i, (c i : Perm (Fin n)).IsCycle ∧ (c i : Perm (Fin n)).support = Ω i := fun i =>
    ⟨(blockCycle_isCycle_card hp.two_le hkp i).1, rfl⟩
  obtain ⟨v, -, -, -, hEA, hcard, -, -, -, hinv⟩ :=
    LocalAnalysis.GorensteinLyons.alternating_central_cover_injective_disjoint_p_cycles
      hp5 hk hkp π hπ hZ Ω hΩ hdisj c hc
  obtain ⟨u, hu, huv⟩ := hinv hn
  set VK := Subgroup.closure (Set.range v)
  have hVKu : VK ≤ Subgroup.centralizer ({u} : Set K) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (huv i).symm.eq
  have hVu : VK.map K.subtype ≤ K ⊓ Subgroup.centralizer ({(u : G)} : Set G) := by
    refine le_inf (Subgroup.map_subtype_le _) ?_
    rintro _ ⟨w, hw, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp (hVKu hw))
  have huG : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe, hu]
  have hVel : CFSG.IsElementaryAbelian p (VK.map K.subtype) := CFSG.IsElementaryAbelian.map_subtype
  have hVcard : Nat.card (VK.map K.subtype) = p ^ k := by
    rw [Subgroup.card_map_of_injective K.subtype_injective, hcard]
  refine ⟨⟨u, u.2, huG, VK.map K.subtype, hVu, hVel, hVcard⟩, ?_⟩
  exact CFSG.RankThree.Classical2.le_localRank_of_involution_elemAbelian hp huG
    (hVu.trans inf_le_right) ⟨hVel.toIsMulCommutative,
      fun x hx => CFSG.elemPow_eq_one_of_isElementaryAbelian x hx⟩ hVcard

end CFSG.RankThree.GroupTheory
