module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotUniqueGraph
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotEndField

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical (matrixIsometryGroup)
open CFSG.Timmesfeld (IsPrimitivePrimeDivisor exists_isPrimitivePrimeDivisor)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.EvenSmallLie (StandardSetting)

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {n : ℕ}

theorem not_two_pow_dvd_two_mul_card_mulAut_unitaryPSU (hn : 3 ≤ n) (hnq : (n, 2 ^ f) ≠ (3, 2))
    {r : ℕ} (hr : n = 2 * r) (hfr : 2 ≤ f ∨ 3 ≤ r) :
    ¬ 2 ^ (2 * f * r ^ 2) ∣ 2 * Nat.card (MulAut (unitaryPSU h n)) := by
  have := h.finite
  have hf := h.one_le
  intro hd
  have h0 : 2 * Nat.card (MulAut (unitaryPSU h n)) ≠ 0 :=
    mul_ne_zero two_ne_zero Nat.card_pos.ne'
  have hv := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two h0).1 hd
  rw [Nat.factorization_mul two_ne_zero Nat.card_pos.ne', Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_two] at hv
  have hA := factorization_card_mulAut_unitaryPSU_le h hn hnq
  have hN : n * (n - 1) / 2 = r * (2 * r - 1) := by
    rw [hr, show 2 * r * (2 * r - 1) = 2 * (r * (2 * r - 1)) by ring]
    exact Nat.mul_div_cancel_left _ two_pos
  rw [hN] at hA
  have hr2 : 2 ≤ r := by omega
  have hsplit : f * (r * (2 * r - 1)) + f * r = 2 * f * r ^ 2 := by
    have h2r : 2 * r - 1 + 1 = 2 * r := by omega
    calc f * (r * (2 * r - 1)) + f * r = f * (r * (2 * r - 1 + 1)) := by ring
      _ = 2 * f * r ^ 2 := by rw [h2r]; ring
  have hvf : f.factorization 2 < f := Nat.factorization_lt 2 (by omega)
  have hB : f * r ≤ 2 + f.factorization 2 := by omega
  rcases hfr with hf2 | hr3
  · have : f * 2 ≤ f * r := Nat.mul_le_mul_left f hr2
    omega
  · have : f * 3 ≤ f * r := Nat.mul_le_mul_left f hr3
    omega

theorem not_zU_two_mul_two_mul {f r : ℕ} (hf : 1 ≤ f) (hr : 2 ≤ r) :
    ¬ Timmesfeld.Orders.zU (2 * r) f (2 * (2 * f) * r) := by
  intro hz
  rcases Timmesfeld.Orders.zU_gap (t := r) (Or.inl rfl) (by omega) (by omega) hz with h1 | h1 | h1
  · nlinarith
  · nlinarith
  · nlinarith

theorem not_card_statedSp_dvd_two_mul_card_mulAut_unitaryPSU (hn : 5 ≤ n)
    {r : ℕ} (hr : n = 2 * r + 1) :
    ¬ Nat.card (StatedSp r K) ∣ 2 * Nat.card (MulAut (unitaryPSU h n)) := by
  have := h.finite
  have hf := h.one_le
  have hnq : (n, 2 ^ f) ≠ (3, 2) := fun h' => by
    have := congrArg Prod.fst h'
    simp only at this
    omega
  intro hd
  have hr1 : 1 ≤ r := by omega
  have hk2 : 2 ≤ 2 * (2 * f) * r := by nlinarith
  have hk6 : 2 * (2 * f) * r ≠ 6 := by
    intro h6
    have : 4 * (f * r) = 6 := by rw [← h6]; ring
    omega
  obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor hk2 hk6
  have hk0 : 0 < 2 * (2 * f) * r := by omega
  have hpS := LinearPilot.ppd_dvd_card_statedSp h.card hr1 hp.dvd
  have hpr := hp.prime
  have hpk := LinearPilot.index_lt_of_isPrimitivePrimeDivisor hp hk0
  have h1 : p ∣ 2 * (Nat.card (unitaryPSU h n) * (2 ^ f + 1) * (2 * f)) :=
    (hpS.trans hd).trans (Nat.mul_dvd_mul_left 2 (card_mulAut_unitaryPSU_dvd h (by omega) hnq))
  have hp2 : ¬ p ∣ 2 := fun h' =>
    hp.ne_two hk0 ((Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).1 h')
  have hpf : ¬ p ∣ 2 * f := fun h' => by
    have := Nat.le_of_dvd (by omega) h'
    have : 2 * f ≤ 2 * (2 * f) * r := by nlinarith
    omega
  have hpq : ¬ p ∣ 2 ^ f + 1 := fun h' => by
    have h2 : 2 ^ f + 1 ∣ 2 ^ (2 * f) - 1 := by
      have h3 : 2 ^ (2 * f) - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
        rw [pow_mul', sq, ← Nat.mul_self_sub_mul_self_eq, Nat.mul_one]
      rw [h3]
      exact dvd_mul_right _ _
    exact hp.2.2 (2 * f) (by omega) (by nlinarith) (h'.trans h2)
  have hpU : ¬ p ∣ Nat.card (unitaryPSU h n) := by
    rw [natCard_unitaryPSU_eq_ordTwistedA h (by omega) hnq]
    intro h'
    have hU := (Timmesfeld.Orders.profile_ordTwistedA (n := n - 1) (by omega) hf).prim p
      (2 * (2 * f) * r) hp hk0
    rw [show n - 1 = 2 * r by omega] at hU
    exact not_zU_two_mul_two_mul hf (by omega) (hU.1 (by rwa [show n - 1 = 2 * r by omega] at h'))
  rcases (Nat.Prime.dvd_mul hpr).1 h1 with h' | h'
  · exact hp2 h'
  rcases (Nat.Prime.dvd_mul hpr).1 h' with h' | h'
  · rcases (Nat.Prime.dvd_mul hpr).1 h' with h' | h'
    · exact hpU h'
    · exact hpq h'
  · exact hpf h'

theorem not_card_fixedSubgroup_graph_dvd_unitary (hn : 5 ≤ n) (A : GL (Fin n) K)
    (hθ : (conjAut n K A * dualAut n K) * (conjAut n K A * dualAut n K) = 1) :
    ¬ Nat.card (fixedSubgroup (conjAut n K A * dualAut n K)) ∣
      2 * Nat.card (MulAut (unitaryPSU h n)) := by
  have := h.finite
  have : CharP K 2 := h.charP
  have hf := h.one_le
  have hnq : (n, 2 ^ f) ≠ (3, 2) := fun h' => by
    have := congrArg Prod.fst h'
    simp only at this
    omega
  obtain ⟨C, hC, hcard, -⟩ :=
    LinearPilot.card_fixedSubgroup_graph_eq (by omega : 1 ≤ 2 * f) h.card (by omega) A hθ
  rw [hcard]
  rcases hC with hC1 | ⟨r, hr, hJ⟩
  · rw [hC1]
    obtain ⟨r, hr | hr⟩ := Nat.even_or_odd' n
    ·
      intro hd
      refine not_two_pow_dvd_two_mul_card_mulAut_unitaryPSU h (by omega) hnq hr
        (Or.inr (by omega)) ?_
      refine dvd_trans ?_
        ((LinearPilot.pow_dvd_card_matrixIsometryGroup_one (F := K) hr (by omega)).trans hd)
      exact dvd_of_eq (by rw [h.card, ← pow_mul])
    ·
      rw [LinearPilot.card_matrixIsometryGroup_one_of_odd hr]
      exact not_card_statedSp_dvd_two_mul_card_mulAut_unitaryPSU h hn hr
  ·
    rw [hJ, LinearPilot.card_matrixIsometryGroup_blockSwapJ hr]
    intro hd
    refine not_two_pow_dvd_two_mul_card_mulAut_unitaryPSU h (by omega) hnq hr
      (Or.inr (by omega)) ?_
    refine dvd_trans ?_ ((LinearPilot.pow_dvd_card_statedSp (F := K) r).trans hd)
    exact dvd_of_eq (by rw [h.card, ← pow_mul])

theorem unitaryGraphInvolutionExclusion (hn : 5 ≤ n) : UnitaryGraphInvolutionExclusion h n :=
  fun A hθ h1 => absurd h1 (not_card_fixedSubgroup_graph_dvd_unitary h hn A hθ)

theorem graphFieldCoreTypeDet_holds (hn : 5 ≤ n) : GraphFieldCoreTypeDet h n :=
  graphFieldCoreTypeDet_of_graph h hn (unitaryGraphInvolutionExclusion h hn)

section Unconditional

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {m : ℕ}

theorem false_of_graphFieldNeighbourParam_unitaryRootTorus_of_nonempty_holds
    (hset : SeitzSetting G L) (e : L ≃* unitaryPSU h (m + 1)) (hm : 5 ≤ m) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {a b : Fin (m + 1)} (hab : a ≠ b)
    (hP : Nonempty (GraphFieldNeighbourParam e t (modelToG e (unitaryRootTorus h hab))
      ({a, b}ᶜ : Finset (Fin (m + 1))))) : False :=
  false_of_graphFieldNeighbourParam_unitaryRootTorus_of_nonempty h hset e hm ht hKt
    (graphFieldCoreTypeDet_holds h (by omega)) hab hP

end Unconditional

end CFSG.SeitzReduction.UnitaryPilot
