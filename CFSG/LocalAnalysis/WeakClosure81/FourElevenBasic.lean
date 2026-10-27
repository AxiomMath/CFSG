module

public import CFSG.Milestones.ASVolI.F429.OutOdd
public import CFSG.Adapters.LieModelL3U3Torus
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1OddL3Inputs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE

public section

namespace CFSG.LocalAnalysis.WeakClosure81.FourEleven

open Subgroup CFSG.Open CFSG.Quasithin
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {Q : Type} [Group Q] [Finite Q]

theorem tA_eq_inf_centralizer (hO2 : pCoreOf 2 (⊤ : Subgroup Q) = ⊥) (T A : Subgroup Q) :
    UniquenessCase.PartTwo.tA T A = T ⊓ centralizer (A : Set Q) := by
  have _ : Finite Q := inferInstance
  ext t
  rw [UniquenessCase.PartTwo.tA, E1.mem_tauOf, Subgroup.mem_inf,
    Subgroup.mem_centralizer_iff_commutator_eq_one']
  constructor
  · rintro ⟨ht, -, hcomm⟩
    exact ⟨ht, by simpa [hO2] using hcomm⟩
  · rintro ⟨ht, hcomm⟩
    refine ⟨ht, ?_, fun a ha => ?_⟩
    · rw [hO2, Subgroup.normalizer_eq_top_iff.mpr inferInstance]
      exact Subgroup.mem_top t
    · rw [hO2, Subgroup.mem_bot]
      exact hcomm a ha

theorem index_le_two {L : Subgroup Q} [L.Normal] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hC : centralizer (L : Set Q) = ⊥) (h2 : IsPGroup 2 (Q ⧸ L))
    (hL : LieModel ↥L .PSL 3 p 1 ∨ LieModel ↥L .PSU 3 p 1) : L.index ≤ 2 := by
  have _ : p.Prime := hp
  have _ : p ≠ 2 := hp2
  have hd1 : Odd (Nat.gcd 3 (p ^ 1 - 1)) :=
    Odd.of_dvd_nat (⟨1, by norm_num⟩ : Odd 3) (Nat.gcd_dvd_left 3 (p ^ 1 - 1))
  have hd2 : Odd (Nat.gcd 3 (p ^ 1 + 1)) :=
    Odd.of_dvd_nat (⟨1, by norm_num⟩ : Odd 3) (Nat.gcd_dvd_left 3 (p ^ 1 + 1))
  have hidx_dvd : L.index ∣ Nat.card (Outer ↥L) :=
    CFSG.ASVolI.burnsideF429_index_dvd_card_outer hC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := h2.exists_card_eq
  have hmain : ∀ {d : ℕ}, Odd d → 2 ^ k ∣ 2 * d → L.index ≤ 2 := by
    intro d hd hdvd
    obtain ⟨t, ht⟩ := hd
    have hd0 : d ≠ 0 := by omega
    have h2d0 : 2 * d ≠ 0 := by omega
    have hnot : ¬ 2 ∣ d := by omega
    have hk_le : k ≤ (2 * d).factorization 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization h2d0).1 hdvd
    rw [Nat.factorization_mul two_ne_zero hd0, Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd hnot] at hk_le
    simp only [add_zero] at hk_le
    calc L.index = 2 ^ k := hk
      _ ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk_le
      _ = 2 := by norm_num
  rcases hL with h | h
  · have hmd : Nat.card (Outer ↥L) ∣ 2 * Nat.gcd 3 (p ^ 1 - 1) := by
      simpa using h.card_outer_psl3_dvd
    exact hmain hd1 (by rw [← hk]; exact hidx_dvd.trans hmd)
  · have hmd : Nat.card (Outer ↥L) ∣ 2 * Nat.gcd 3 (p ^ 1 + 1) := by
      rw [h.card_outer_psu3]
    exact hmain hd2 (by rw [← hk]; exact hidx_dvd.trans hmd)

theorem card_inf_le_four {L : Subgroup Q} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hL : LieModel ↥L .PSL 3 p 1 ∨ LieModel ↥L .PSU 3 p 1) {A : Subgroup Q}
    (hA : IsElemAbelian 2 A) : Nat.card ↥(A ⊓ L) ≤ 4 := by
  have _ : p.Prime := hp
  have hS : StatedClassicalModel ↥L .PSL 3 p 1 ∨
      StatedClassicalModel ↥L .PSU 3 p 1 :=
    hL.imp (fun h => h.statedClassicalModel_of_ne_zero (by norm_num))
      (fun h => h.statedClassicalModel_of_ne_zero (by norm_num))
  have hE : IsElemAbelian 2 ((A ⊓ L).subgroupOf L) :=
    (hA.mono inf_le_left).subgroupOf L
  have hle := CFSG.RankThree.PartTwo.Sec15.Sylow155R1.res1OddL3_card_elemAbelian_le_four
    hp2 hS ((A ⊓ L).subgroupOf L) (fun a ha b hb => hE.comm ha hb)
      (fun a ha => hE.2 a ha)
  have hcard : Nat.card ↥((A ⊓ L).subgroupOf L) = Nat.card ↥(A ⊓ L) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  rwa [hcard] at hle

theorem card_le_two_mul_card_inf {L : Subgroup Q} [L.Normal] (hidx : L.index ≤ 2)
    (A : Subgroup Q) : Nat.card A ≤ 2 * Nat.card ↥(A ⊓ L) := by
  have hrel : L.relIndex A ≤ 2 := by
    have hle : L.relIndex A ≤ L.index := by
      rw [← Subgroup.relIndex_top_right (H := L)]
      exact Subgroup.relIndex_le_of_le_right le_top (by
        simpa using Subgroup.index_ne_zero_of_finite (H := L))
    exact hle.trans hidx
  have hmul := Subgroup.relIndex_mul_card (H := L) (K := A)
  calc Nat.card A = L.relIndex A * Nat.card ↥(L ⊓ A) := hmul.symm
    _ = L.relIndex A * Nat.card ↥(A ⊓ L) := by rw [inf_comm]
    _ ≤ 2 * Nat.card ↥(A ⊓ L) := Nat.mul_le_mul_right _ hrel

theorem mem_of_commute_of_card_inf_eq_four {L : Subgroup Q} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hL : LieModel ↥L .PSL 3 p 1 ∨ LieModel ↥L .PSU 3 p 1) {A : Subgroup Q}
    (hA : IsElemAbelian 2 A) (h4 : Nat.card ↥(A ⊓ L) = 4) {z : Q} (hzL : z ∈ L)
    (hz2 : orderOf z = 2) (hzA : ∀ a ∈ A, a * z = z * a) : z ∈ A := by
  have hzsq : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rw [hz2] at h
    simpa [pow_two] using h
  let B : Subgroup Q := Subgroup.closure (((A ⊓ L : Subgroup Q) : Set Q) ∪ {z})
  have hB : IsElemAbelian 2 B := by
    refine IsElemAbelian.closure_of_commute ?_ ?_
    · intro x hx y hy
      rw [Set.mem_union, Set.mem_singleton_iff] at hx hy
      rcases hx with hx | rfl
      · rcases hy with hy | rfl
        · exact hA.comm (Subgroup.mem_inf.mp hx).1 (Subgroup.mem_inf.mp hy).1
        · exact hzA x (Subgroup.mem_inf.mp hx).1
      · rcases hy with hy | rfl
        · exact (hzA y (Subgroup.mem_inf.mp hy).1).symm
        · rfl
    · intro x hx
      rw [Set.mem_union, Set.mem_singleton_iff] at hx
      rcases hx with hx | rfl
      · exact hA.2 x (Subgroup.mem_inf.mp hx).1
      · simpa [pow_two] using hzsq
  have hBL : B ≤ L := by
    change Subgroup.closure (((A ⊓ L : Subgroup Q) : Set Q) ∪ {z}) ≤ L
    refine (Subgroup.closure_le (K := L)).mpr ?_
    intro x hx
    rw [Set.mem_union, Set.mem_singleton_iff] at hx
    rcases hx with hx | rfl
    · exact (Subgroup.mem_inf.mp hx).2
    · exact hzL
  have hcardB : Nat.card B ≤ 4 := by
    have h := card_inf_le_four hp hp2 hL hB
    rwa [inf_eq_left.mpr hBL] at h
  have hAleB : A ⊓ L ≤ B := by
    intro x hx
    exact Subgroup.subset_closure (Or.inl hx)
  have h4le : 4 ≤ Nat.card B := by
    calc 4 = Nat.card ↥(A ⊓ L) := h4.symm
      _ ≤ Nat.card B := Subgroup.card_le_of_le hAleB
  have hBeq : A ⊓ L = B :=
    Subgroup.eq_of_le_of_card_ge hAleB (by omega)
  have hzB : z ∈ B := Subgroup.subset_closure (Or.inr (Set.mem_singleton z))
  rw [← hBeq] at hzB
  exact hzB.1

theorem mQuot_le_of_card_le {A U : Subgroup Q} {n : ℕ} (hA : IsElemAbelian 2 A)
    (hcard : Nat.card A ≤ 2 ^ (n + 1)) {a : Q} (haA : a ∈ A) (haU : a ∈ U) (ha1 : a ≠ 1) :
    E3.mQuot A U ≤ n := by
  have hdvd : orderOf a ∣ 2 :=
    orderOf_dvd_iff_pow_eq_one.mpr (by simpa using hA.2 a haA)
  have hord : orderOf a = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ha1
    · exact h
  have hcardinf : 2 ≤ Nat.card ↥(A ⊓ U) := by
    have hle : Subgroup.zpowers a ≤ A ⊓ U := Subgroup.zpowers_le.mpr ⟨haA, haU⟩
    calc 2 = Nat.card (Subgroup.zpowers a) := by rw [Nat.card_zpowers, hord]
      _ ≤ Nat.card ↥(A ⊓ U) := Subgroup.card_le_of_le hle
  have hsplit := E3.card_eq_two_pow_mul (V := A) (U := A ⊓ U) hA.isPGroup inf_le_left
  have hmq : E3.mQuot A (A ⊓ U) = E3.mQuot A U := by
    unfold E3.mQuot
    rw [inf_comm, Subgroup.inf_relIndex_right]
  have hmul : 2 ^ E3.mQuot A U * 2 ≤ 2 ^ (n + 1) := by
    calc 2 ^ E3.mQuot A U * 2 ≤ 2 ^ E3.mQuot A U * Nat.card ↥(A ⊓ U) :=
          Nat.mul_le_mul_left _ hcardinf
      _ = 2 ^ E3.mQuot A (A ⊓ U) * Nat.card ↥(A ⊓ U) := by rw [hmq]
      _ = Nat.card A := hsplit.symm
      _ ≤ 2 ^ (n + 1) := hcard
  have hpow : 2 ^ E3.mQuot A U ≤ 2 ^ n := by
    rw [pow_succ] at hmul
    exact Nat.le_of_mul_le_mul_right hmul (by norm_num)
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hpow

end CFSG.LocalAnalysis.WeakClosure81.FourEleven
