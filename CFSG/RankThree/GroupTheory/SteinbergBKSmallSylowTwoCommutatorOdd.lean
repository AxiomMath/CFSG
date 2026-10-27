module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Defs
import CFSG.GroupTheory.Fitting.CoprimeAutomorphisms
import CFSG.Assembly.OrderReductions.InvariantSylow
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Core

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBK

open Subgroup CFSG

theorem smul_eq_self_of_card_le_prime {p : ℕ} (hp : p.Prime) {S A : Type*} [Group S]
    [Finite S] [Group A] [Finite A] [MulDistribMulAction A S] (hA : IsPGroup p A)
    (T : Subgroup S) (hTinv : ∀ a : A, ∀ x ∈ T, a • x ∈ T) (hTp : Nat.card T ≤ p) :
    ∀ a : A, ∀ x ∈ T, a • x = x := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  intro a x hx
  by_cases hx1 : x = 1
  · rw [hx1, smul_one]
  have horb : MulAction.orbit A x ⊆ (T : Set S) \ {1} := by
    rintro _ ⟨b, rfl⟩
    refine ⟨hTinv b x hx, fun h => hx1 ?_⟩
    have h' : b • x = b • (1 : S) := by rw [smul_one]; exact h
    exact smul_left_cancel b h'
  have hle : (MulAction.orbit A x).ncard < p := by
    have h := Set.ncard_le_ncard horb (Set.toFinite _)
    rw [Set.ncard_sdiff_singleton_of_mem (one_mem T)] at h
    have hT : (T : Set S).ncard = Nat.card T := (Nat.card_coe_set_eq _).symm
    have := hp.pos
    omega
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA
  have hdvd : (MulAction.orbit A x).ncard ∣ p ^ k := by
    rw [← MulAction.index_stabilizer, ← hk]
    exact (MulAction.stabilizer A x).index_dvd_card
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hi0 : i = 0 := by
    by_contra h0
    have : p ≤ p ^ i := Nat.le_self_pow h0 p
    omega
  rw [hi0, pow_zero, Set.ncard_eq_one] at hi
  obtain ⟨y, hy⟩ := hi
  have h1 : a • x ∈ MulAction.orbit A x := MulAction.mem_orbit x a
  have h2 : x ∈ MulAction.orbit A x := MulAction.mem_orbit_self x
  rw [hy, Set.mem_singleton_iff] at h1 h2
  rw [h1, h2]

theorem solvable_large_prime_small_sylow_two_commutator_odd {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) {S A : Type*} [Group S] [Finite S] [Group A] [Finite A]
    [MulDistribMulAction A S] (hS : Group.IsSolvable S) (hpS : ¬ p ∣ Nat.card S)
    (hA : IsPGroup p A) (hT : ∃ T : Sylow 2 S, Nat.card (T : Subgroup S) ≤ 4) :
    commutatorSubgroup A S ⊤ ≤ pPrimeCore 2 S ∧
      Odd (Nat.card (commutatorSubgroup A S ⊤)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set α := MulDistribMulAction.toMulAut A S with hα
  obtain ⟨T₀, hT₀⟩ :=
    CFSG.OrderReductions.InvariantSylow.exists_invariant_sylow_of_coprime p 2 hA hpS α
  have hT₀inv : ∀ a : A, ∀ x ∈ (T₀ : Subgroup S), a • x ∈ (T₀ : Subgroup S) := fun a x hx => by
    rw [← hT₀ a]
    exact ⟨x, hx, rfl⟩
  have hT₀card : Nat.card (T₀ : Subgroup S) ≤ p := by
    obtain ⟨T, hT⟩ := hT
    rw [T₀.card_eq_multiplicity, ← T.card_eq_multiplicity]
    omega
  have hT₀fix := smul_eq_self_of_card_le_prime hp hA (T₀ : Subgroup S) hT₀inv hT₀card
  set R := pPrimeCore 2 S with hRdef
  have hR : ∀ a : A, ∀ n ∈ R, α a n ∈ R := fun a n hn =>
    (characteristic_iff_map_le.mp inferInstance (α a)) ⟨n, hn, rfl⟩
  set β := CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α R hR with hβ
  have hQsolv : Group.IsSolvable (S ⧸ R) := by
    have := hS
    infer_instance
  have hF : fittingSubgroup (S ⧸ R) = pCore 2 (S ⧸ R) :=
    Fitting_eq_pcore (S ⧸ R) 2 (pPrimeCore_quotient_pPrimeCore_eq_bot 2)
  set T₁ := T₀.mapSurjective (QuotientGroup.mk'_surjective R) with hT₁
  have hFT : pCore 2 (S ⧸ R) ≤ (T₁ : Subgroup (S ⧸ R)) :=
    IsPGroup.le_sylow_of_normal pCore_isPGroup T₁
  have hβ1 : ∀ a : A, β a = 1 := by
    intro a
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (pCore_isPGroup (p := 2) (G := S ⧸ R))
    refine mulAut_eq_one_of_fixes_fittingSubgroup (S ⧸ R) hQsolv (β a) (Nat.card A) ?_ ?_ ?_
    · rw [← map_pow, pow_card_eq_one', map_one]
    · rw [hF, hk, hm]
      exact Nat.Coprime.pow k m ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega))
    · intro y hy
      rw [hF] at hy
      obtain ⟨t, ht, rfl⟩ := hFT hy
      change β a (t : S ⧸ R) = (t : S ⧸ R)
      rw [hβ, CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk]
      exact congrArg _ (hT₀fix a t ht)
  have hle : commutatorSubgroup A S ⊤ ≤ R := by
    refine closure_le _ |>.mpr ?_
    rintro _ ⟨a, s, -, rfl⟩
    have h := congrArg (fun φ : MulAut (S ⧸ R) => φ (s : S ⧸ R)) (hβ1 a)
    simp only [hβ, CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk,
      MulAut.one_apply] at h
    exact QuotientGroup.eq.mp h.symm
  refine ⟨hle, ?_⟩
  have hRodd : Odd (Nat.card R) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  exact hRodd.of_dvd_nat (card_dvd_of_le hle)

end CFSG.RankThree.GroupTheory.SteinbergBK
