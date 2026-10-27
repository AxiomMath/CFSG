module

public import CFSG.RankThree.PartTwo.Sec18.Item185OuterLin
import CFSG.RankThree.PartTwo.Sec8.Hering611RInspectF4
import CFSG.LieType.SeitzGeneration.ExcPlaneModel
import CFSG.RankThree.PartTwo.Sec19.SimsC198Ree
import CFSG.RankThree.PartTwo.Sec8.Item86ResProofOrders

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item185Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.LieType.Ree
open CFSG.Open (ordTwistedF4)
open scoped commutatorElement

private theorem prime_dvd_card_of_sq {Y : Type} [Group Y] [Finite Y] {D : Subgroup Y} {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hsq : ∀ y : Y, y ^ 2 ∈ D) (h : p ∣ Nat.card Y) :
    p ∣ Nat.card D := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Y) p h
  obtain ⟨m, hm⟩ := hodd
  have hxp : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hxD : x ∈ D := by
    have : x = (x ^ 2) ^ (m + 1) := by
      rw [← pow_mul, show 2 * (m + 1) = p + 1 by omega, pow_succ, hxp, one_mul]
    rw [this]
    exact D.pow_mem (hsq x) _
  have : orderOf (⟨x, hxD⟩ : D) = p := by rw [Subgroup.orderOf_mk]; exact hx
  rw [← this]
  exact orderOf_dvd_natCard _

private theorem not_comm_of_dvd {N : Type} [Group N] [IsSimpleGroup N] (h3 : 3 ∣ Nat.card N)
    (h13 : 13 ∣ Nat.card N) : ¬ ∀ x y : N, x * y = y * x := by
  intro hc
  letI : CommGroup N := { ‹Group N› with mul_comm := hc }
  have hp : (Nat.card N).Prime := IsSimpleGroup.prime_card
  have e3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3
  have e13 := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 13) hp).mp h13
  omega

private theorem three_dvd_ordTwistedF4 (b : ℕ) : 3 ∣ ordTwistedF4 (2 ^ (2 * b + 1)) := by
  unfold ordTwistedF4
  have h : 3 ∣ (2 ^ (2 * b + 1)) ^ 3 + 1 := by
    have h1 : (2 ^ (2 * b + 1)) ^ 3 = 8 ^ (2 * b + 1) := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [h1]
    have h2 := Odd.nat_add_dvd_pow_add_pow 8 1 (⟨b, rfl⟩ : Odd (2 * b + 1))
    rw [one_pow] at h2
    exact (show 3 ∣ 8 + 1 by norm_num).trans h2
  exact (h.mul_left _).mul_right _

private theorem centralizer_commutator_eq_bot {Y : Type} [Group Y] (hZ : Subgroup.center Y = ⊥)
    (hs : IsSimpleGroup ↥(commutator Y)) (hna : ¬ ∀ x y : ↥(commutator Y), x * y = y * x) :
    Subgroup.centralizer ((commutator Y : Subgroup Y) : Set Y) = ⊥ := by
  haveI := hs
  have hNn : (commutator Y).Normal := Subgroup.commutator_normal ⊤ ⊤
  have hZN : Subgroup.center ↥(commutator Y) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(commutator Y)) with h0 | h0
    · exact h0
    · refine absurd (fun x y => ?_) hna
      have hy : y ∈ Subgroup.center ↥(commutator Y) := by
        rw [h0]
        exact Subgroup.mem_top y
      exact Subgroup.mem_center_iff.mp hy x
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_centralizer_iff] at hz
  rw [Subgroup.mem_bot]
  have hzc : z ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hcomm : ⁅y, z⁆ ∈ commutator Y :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top y) (Subgroup.mem_top z)
    have hw : (⟨⁅y, z⁆, hcomm⟩ : ↥(commutator Y)) ∈ Subgroup.center ↥(commutator Y) := by
      rw [Subgroup.mem_center_iff]
      intro n
      apply Subtype.ext
      show (n : Y) * ⁅y, z⁆ = ⁅y, z⁆ * (n : Y)
      have h1 : (n : Y) * z = z * (n : Y) := hz n n.2
      have hconj : y⁻¹ * (n : Y) * y ∈ commutator Y := by
        have := hNn.conj_mem n n.2 y⁻¹
        simpa using this
      have h2 : y⁻¹ * (n : Y) * y * z = z * (y⁻¹ * (n : Y) * y) := hz _ hconj
      have e2 : (n : Y) * (y * z * y⁻¹) = (y * z * y⁻¹) * (n : Y) := by
        calc (n : Y) * (y * z * y⁻¹) = y * ((y⁻¹ * (n : Y) * y) * z) * y⁻¹ := by group
          _ = y * (z * (y⁻¹ * (n : Y) * y)) * y⁻¹ := by rw [h2]
          _ = (y * z * y⁻¹) * (n : Y) := by group
      have e1 : (n : Y) * z⁻¹ = z⁻¹ * (n : Y) := by
        calc (n : Y) * z⁻¹ = z⁻¹ * (z * (n : Y)) * z⁻¹ := by group
          _ = z⁻¹ * ((n : Y) * z) * z⁻¹ := by rw [h1]
          _ = z⁻¹ * (n : Y) := by group
      rw [commutatorElement_def]
      calc (n : Y) * (y * z * y⁻¹ * z⁻¹) = ((n : Y) * (y * z * y⁻¹)) * z⁻¹ := by group
        _ = ((y * z * y⁻¹) * (n : Y)) * z⁻¹ := by rw [e2]
        _ = (y * z * y⁻¹) * ((n : Y) * z⁻¹) := by group
        _ = (y * z * y⁻¹) * (z⁻¹ * (n : Y)) := by rw [e1]
        _ = (y * z * y⁻¹ * z⁻¹) * (n : Y) := by group
    rw [hZN, Subgroup.mem_bot] at hw
    have hw1 : ⁅y, z⁆ = 1 := congrArg Subtype.val hw
    exact commutatorElement_eq_one_iff_mul_comm.mp hw1
  rw [hZ, Subgroup.mem_bot] at hzc
  exact hzc

section ReeF4


private theorem exists_normal_simple_of_mulEquiv_reeGamma {Y : Type} [Group Y] {b : ℕ} {k : Type}
    [Field k] [Finite k] [CharP k ReeTag.F4.prime] (hk : Nat.card k = 2 ^ (2 * b + 1))
    (e : Y ≃* ReeTag.F4.reeGamma k b) :
    ∃ N : Subgroup Y, N.Normal ∧ IsSimpleGroup N ∧ ¬ (∀ x y : N, x * y = y * x) ∧
      Subgroup.centralizer (N : Set Y) = ⊥ := by
  haveI : Finite (ReeTag.F4.reeGamma k b) := by
    haveI := CFSG.LieType.Chevalley.finite_modGL (τ := ReeTag.F4.tag) (K := k)
    infer_instance
  haveI : Finite Y := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨hs, hsq⟩ := Sec8.Hering611R.simple_commutator_reeGamma hk e
  have hZ : Subgroup.center Y = ⊥ :=
    KFacts.center_eq_bot_of_mulEquiv_of_center_eq_bot e
      (ReeTag.large_Ree_fixed_group_center_trivial b k hk)
  have hcard : Nat.card Y = ordTwistedF4 (2 ^ (2 * b + 1)) :=
    Sec8.Item86ResProof.card_of_mulEquiv_reeGamma b k hk e
  have h3 : 3 ∣ Nat.card ↥(commutator Y) :=
    prime_dvd_card_of_sq Nat.prime_three ⟨1, rfl⟩ hsq
      (by rw [hcard]; exact three_dvd_ordTwistedF4 b)
  have h13 : 13 ∣ Nat.card ↥(commutator Y) :=
    prime_dvd_card_of_sq (by norm_num) ⟨6, rfl⟩ hsq
      (by rw [hcard]; exact Sec8.Hering611R.thirteen_dvd_ordTwistedF4 b)
  haveI := hs
  have hna : ¬ ∀ x y : ↥(commutator Y), x * y = y * x := not_comm_of_dvd h3 h13
  exact ⟨commutator Y, Subgroup.commutator_normal ⊤ ⊤, hs, hna,
    centralizer_commutator_eq_bot hZ hs hna⟩


theorem gapReeF4_fixedFacts :
    ∀ (m : ℕ) (hv : (TauCeti.LieTypeIndex.reeF4 m).Valid) (X : Type) [Group X]
      (_ : X ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group),
      ∀ σ : MulAut X, σ ∉ innerAut X → σ ^ 3 = 1 → FixedFactsAt σ := by
  intro m hv X _ e σ hσout hσ3
  obtain ⟨-, a, ha, -, K, _, _, _, hK, ⟨e'⟩⟩ :=
    Sec4.exists_mulEquiv_reeGamma (CFSG.LieType.SeitzGeneration.reeTitsModel_cat_reeF4 hv)
  let ψ : X ≃* ReeTag.F4.reeGamma K a := e.trans e'
  have hσ'3 : MulAut.congr ψ σ ^ 3 = 1 := by rw [← map_pow, hσ3, map_one]
  have hσ'out : MulAut.congr ψ σ ∉
      (MulAut.conj : ReeTag.F4.reeGamma K a →* MulAut (ReeTag.F4.reeGamma K a)).range :=
    fun h => hσout ((KFacts.isInnerAut_congr ψ σ).mp h)
  obtain ⟨b, k, _, _, _, hk, -, ι, hι, hrange⟩ :=
    Sec19.SimsC198.reeGamma_fixed_of_outer ha hK _ hσ'3 hσ'out
  obtain ⟨eC⟩ := KFacts.nonempty_eqLocus_mulEquiv ψ σ ι hι hrange
  unfold FixedFactsAt
  left
  exact exists_normal_simple_of_mulEquiv_reeGamma hk eC

end ReeF4

end CFSG.RankThree.PartTwo.Sec18.Item185Proof
