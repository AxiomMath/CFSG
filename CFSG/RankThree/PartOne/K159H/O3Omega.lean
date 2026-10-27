module

public import CFSG.RankThree.PartOne.K159H.O3Group
public import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailWittFlags

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.RankThree.PartOne.K159H

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal.Spin
  CFSG.RankThree.OrthogonalInvolutions Module
open CFSG.RankThree.Classical2 (orthDerived)

variable {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A] {r : ℕ}

omit [Module K A] in
theorem nontrivial_tail (hr : 1 ≤ r) : Nontrivial ((Fin r ⊕ Fin r → K) × A) := by
  refine nontrivial_of_ne (hypVec K A (Sum.inl ⟨0, hr⟩)) 0 fun h => ?_
  have := congrFun (congrArg Prod.fst h) (Sum.inl ⟨0, hr⟩)
  simp [hypVec_fst] at this

theorem tail_exists_totSing {qA : QuadraticForm K A} (hr : 3 ≤ r) :
    ∃ T : Submodule K ((Fin r ⊕ Fin r → K) × A), finrank K T = 3 ∧ ∀ x ∈ T, quadTail r qA x = 0 :=
  ⟨tailFlag K A r 3, finrank_tailFlag hr, fun _ hx => quadTail_eq_zero_of_mem_tailFlag hx⟩

abbrev Om (qA : QuadraticForm K A) (r : ℕ) :
    Subgroup (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) :=
  orthDerived (quadTail r qA)

section Basic

variable {qA : QuadraticForm K A}

theorem Om_le_orth : Om qA r ≤ TauCeti.QuadraticMap.orthogonalGroup (quadTail r qA) :=
  Subgroup.commutator_le_of_le le_rfl le_rfl

theorem torH_pow (d : Fin r → Kˣ) (n : ℕ) : torH K A r d ^ n = torH K A r (d ^ n) := (map_pow _ _ _).symm


variable [Finite K] [CharP K 2] in
theorem odd_card_units : Odd (Nat.card Kˣ) := by
  classical
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have h1 : Nat.card Kˣ = Nat.card K - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, Nat.card_eq_fintype_card]
  rw [h1, Nat.card_eq_fintype_card, hn]
  have : 2 ≤ 2 ^ (n : ℕ) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n : ℕ) := Nat.pow_le_pow_right (by norm_num) n.pos
  have h2 : Even (2 ^ (n : ℕ)) := (Nat.even_pow.mpr ⟨by norm_num, n.pos.ne'⟩)
  obtain ⟨m, hm⟩ := h2
  exact ⟨m - 1, by omega⟩

variable [Finite K] [CharP K 2] in
theorem odd_orderOf_torH (d : Fin r → Kˣ) : Odd (orderOf (torH K A r d)) := by
  have h1 : torH K A r d ^ Nat.card Kˣ = 1 := by
    rw [torH_pow, ← map_one (torH K A r)]
    congr 1
    funext k
    simp [pow_card_eq_one']
  exact Odd.of_dvd_nat odd_card_units (orderOf_dvd_of_pow_eq_one h1)

theorem mem_of_odd_orderOf_of_relIndex_two {G : Type*} [Group G] {N H : Subgroup G}
    (hidx : N.relIndex H = 2) {g : G} (hg : g ∈ H) (hodd : Odd (orderOf g)) : g ∈ N := by
  have hN : (N.subgroupOf H).index = 2 := hidx
  have : (N.subgroupOf H).Normal := Subgroup.normal_of_index_eq_two hN
  set x : ↥H := ⟨g, hg⟩ with hx
  have h2 : x ^ 2 ∈ N.subgroupOf H := by
    have := Subgroup.pow_index_mem (N.subgroupOf H) x
    rwa [hN] at this
  obtain ⟨k, hk⟩ := hodd
  have hord : orderOf x = 2 * k + 1 := by
    rw [hx, Subgroup.orderOf_mk]
    exact hk
  have : x = (x ^ 2) ^ (k + 1) := by
    have e : (x ^ 2) ^ (k + 1) = x ^ (2 * k + 1) * x := by
      rw [← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ]
    rw [e, ← hord, pow_orderOf_eq_one, one_mul]
  have : x ∈ N.subgroupOf H := by
    rw [this]
    exact pow_mem h2 _
  exact Subgroup.mem_subgroupOf.mp this

end Basic

section Facts

variable [Finite K] [CharP K 2] [FiniteDimensional K A] {qA : QuadraticForm K A}
  (hreg : (polarBilin qA).Nondegenerate) (hr : 3 ≤ r)

include hreg hr

omit [CharP K 2] in
theorem Om_eq_elementary : Om qA r = elementaryGroup (quadTail r qA) :=
  (CFSG.RankThree.Classical.orthDerived_eq_and_le_closure (nondegenerate_polarBilin_quadTail hreg)
    (tail_exists_totSing hr)).1

theorem Om_eq_omega :
    Om qA r = omegaGroup (quadTail r qA) (nondegenerate_polarBilin_quadTail hreg) :=
  le_antisymm (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup _)
    (CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived _ (tail_exists_totSing hr))

omit [CharP K 2] in
theorem eichler_mem_Om (u w : (Fin r ⊕ Fin r → K) × A) : eichler (quadTail r qA) u w ∈ Om qA r := by
  rw [Om_eq_elementary hreg hr]
  exact eichler_mem_elementaryGroup _ _ _

theorem rEl_mem_Om (t : K) (j j' : Fin r ⊕ Fin r) : rEl qA t j j' ∈ Om qA r := eichler_mem_Om hreg hr _ _

theorem torH_mem_Om (d : Fin r → Kˣ) : torH K A r d ∈ Om qA r := by
  have hQ := nondegenerate_polarBilin_quadTail (r := r) hreg
  have : Nontrivial ((Fin r ⊕ Fin r → K) × A) := nontrivial_tail (by omega)
  rw [Om_eq_omega hreg hr]
  exact mem_of_odd_orderOf_of_relIndex_two (relIndex_omegaGroup (quadTail r qA) hQ)
    (torH_mem_orth qA d) (odd_orderOf_torH d)

theorem Tor_le_Om : Tor K A r ≤ Om qA r := by
  rintro _ ⟨d, rfl⟩
  exact torH_mem_Om hreg hr d

theorem Rts_le_Om (S : Subgroup (Fin r → Kˣ)) : Rts qA S ≤ Om qA r := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g (⟨t, j, j', -, -, rfl⟩ | ⟨j, a, -, rfl⟩)
  · exact rEl_mem_Om hreg hr t j j'
  · exact eichler_mem_Om hreg hr _ _

end Facts

@[expose] def Csub (qA : QuadraticForm K A) (S : Subgroup (Fin r → Kˣ)) :
    Subgroup (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) :=
  Om qA r ⊓ CO qA S

theorem mem_Csub {qA : QuadraticForm K A} {S : Subgroup (Fin r → Kˣ)}
    {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)} :
    g ∈ Csub qA S ↔ g ∈ Om qA r ∧ g ∈ CO qA S := Subgroup.mem_inf

end CFSG.RankThree.PartOne.K159H
