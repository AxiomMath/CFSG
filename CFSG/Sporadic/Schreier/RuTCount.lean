
module

public import CFSG.Sporadic.Schreier.RuTCountBase

public import CFSG.Sporadic.Schreier.RuOrbL
public import CFSG.Sporadic.Schreier.RuCheckBasicInputs
public import CFSG.Sporadic.Schreier.RuCheckChainsInputs
public import CFSG.Sporadic.Schreier.RuCheckLInputs
public meta import CFSG.Sporadic.Schreier.RuCheckChains
public meta import CFSG.Sporadic.Schreier.RuWitArrays
public import CFSG.Sporadic.Schreier.RuArrays
public import CFSG.Certificates.NativeSetOrbit
public import CFSG.Sporadic.Schreier.RuOrbLFacts
public import CFSG.Sporadic.Schreier.RuCheckOrbLBInputs
public meta import CFSG.Sporadic.Schreier.RuOrbLDefs
public import CFSG.Sporadic.Schreier.RuCheckTreeInputs
public import CFSG.Sporadic.Schreier.RuWitArrays

public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

theorem ncard_ruRoots :
    {x | x ∈ ruP ∧ x ^ 2 = ruZ}.ncard = 816 := by
  have e : {x | x ∈ ruP ∧ x ^ 2 = ruZ} = {x | x ∈ ruC ∧ x ^ 2 = ruZ} := by
    ext x
    constructor
    · rintro ⟨hx, h⟩
      exact ⟨mem_ruC_of_sq hx h, h⟩
    · rintro ⟨hx, h⟩
      exact ⟨ruC_le hx, h⟩
  rw [e, ncard_setOf_mem_and ruC (fun x => x ^ 2 = ruZ),
    ruC_card_of_count (P := fun g => g ^ 2 = ruZ) (p := ruSqZA) fun t g ht => by
      rw [ruSqZA_iff ht, pow_two]]
  exact ruOrbLB_check.2.2.1

theorem ruFibCounts :
    (ruFib (ruRepZ 3)).ncard = 0 ∧ (ruFib (ruRepZ 6)).ncard = 0 ∧
    (ruFib (ruRepZ 11)).ncard = 4 := by
  have h := ruOrbLB_check.2.2.2
  simp only [List.cons.injEq, and_true] at h
  rw [ncard_ruFib_rep, ncard_ruFib_rep, ncard_ruFib_rep]
  exact h

theorem ruT_eq :
    ruT = ⋃ t ∈ ruOrb 11, ruFib t := by
  ext x
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨hx, hz, h13, h14, h29⟩
    rw [ruZP_eq_iUnion] at hz
    simp only [Set.mem_iUnion, Finset.mem_range, exists_prop] at hz
    obtain ⟨k, hk, hkt⟩ := hz
    have hspec := (ruOrb_ord14 hk hkt).1 h14
    have hfib : x ∈ ruFib (x ^ 2) := ⟨hx, rfl, h13, h29⟩
    have hne : (ruFib (x ^ 2)).ncard ≠ 0 :=
      (Set.ncard_pos (Set.toFinite _)).2 ⟨x, hfib⟩ |>.ne'
    rw [ncard_ruFib_of_mem_ruOrb hkt] at hne
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hspec
    rcases hspec with rfl | rfl | rfl
    · exact absurd ruFibCounts.1 hne
    · exact absurd ruFibCounts.2.1 hne
    · exact ⟨x ^ 2, hkt, hfib⟩
  · rintro ⟨t, ht, hx, h2, h13, h29⟩
    subst h2
    refine ⟨hx, ruOrb_sub 11 ht, h13, (ruOrb_ord14 (by decide) ht).2 (by decide), h29⟩

theorem ncard_ruOrb11 :
    (ruOrb 11).ncard = 29120 := by
  rw [ncard_ruOrb (by decide)]
  rfl

theorem ncard_ruT :
    ruT.ncard = 116480 := by
  have hs : (ruOrb 11).Finite := Set.toFinite _
  have hdisj : (ruOrb 11).PairwiseDisjoint ruFib := by
    intro t _ t' _ htt'
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨-, h, -⟩ ⟨-, h', -⟩
    exact htt' (h.symm.trans h')
  rw [ruT_eq, hs.ncard_biUnion (fun _ _ => Set.toFinite _) hdisj,
    finsum_mem_congr rfl fun t ht => (ncard_ruFib_of_mem_ruOrb ht).trans ruFibCounts.2.2,
    finsum_mem_eq_finite_toFinset_sum _ hs, Finset.sum_const, ← Set.ncard_eq_toFinset_card _ hs,
    ncard_ruOrb11, smul_eq_mul]

theorem CTUC_Ru_constrained_second_generator_orbit_count :
    ruT.ncard = 116480 ∧
    (∀ k < 19, ruRepZ k ∈ ruZP) ∧ ruZP = ⋃ k ∈ Finset.range 19, conjSet ruL (ruRepZ k) ∧
    (∀ k < 19, ∀ k' < 19, k ≠ k' →
      Disjoint (conjSet ruL (ruRepZ k)) (conjSet ruL (ruRepZ k'))) ∧
    (∀ k < 19, ∀ t ∈ conjSet ruL (ruRepZ k), orderOf (ruA0 * t) = 14 ↔ k ∈ [3, 6, 11]) ∧
    (∀ k ∈ [3, 6, 11], (conjSet ruL (ruRepZ k)).ncard = 29120) ∧
    [ruReps.getD 3 0, ruReps.getD 6 0, ruReps.getD 11 0] = [7, 13, 27] ∧
    (ruFib (ruRepZ 3)).ncard = 0 ∧ (ruFib (ruRepZ 6)).ncard = 0 ∧
    (ruFib (ruRepZ 11)).ncard = 4 ∧
    {x | x ∈ ruP ∧ x ^ 2 = ruZ}.ncard = 816 := by
  refine ⟨ncard_ruT, fun k _ => ruRepZ_mem k, ruZP_eq_iUnion,
    fun k hk k' hk' h => ruOrb_disjoint hk hk' h, fun k hk t ht => ruOrb_ord14 hk ht, ?_, rfl,
    ruFibCounts.1, ruFibCounts.2.1, ruFibCounts.2.2, ncard_ruRoots⟩
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl <;> rw [ncard_ruOrb (by decide)] <;> rfl

end CFSG.Sporadic.RuSchreier
