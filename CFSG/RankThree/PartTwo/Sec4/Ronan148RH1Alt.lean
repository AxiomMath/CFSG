module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Crit
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowA1112
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowAlt

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open Equiv Equiv.Perm
open CFSG.Quasithin.SteinbergCB (conjPerm conjPerm_apply)

section Cycles

variable {n : ℕ}

theorem card_cycleType_eq (τ : Perm (Fin n)) :
    Multiset.card τ.cycleType = τ.cycleFactorsFinset.card := by
  rw [cycleType_def, Multiset.card_map]
  rfl

theorem commute_cycleFactors_of_isPerfect {τ : Perm (Fin n)}
    (hk : Multiset.card τ.cycleType ≤ 4) {K : Subgroup (alternatingGroup (Fin n))}
    (hK : K ≤ autFix (conjPerm n τ)) [Group.IsPerfect K] {x : alternatingGroup (Fin n)}
    (hx : x ∈ K) {c : Perm (Fin n)} (hc : c ∈ τ.cycleFactorsFinset) :
    (x : Perm (Fin n)) * c = c * x := by
  let ι : K →* Subgroup.centralizer ({τ} : Set (Perm (Fin n))) :=
    { toFun := fun k => ⟨((k : alternatingGroup (Fin n)) : Perm (Fin n)),
        Subgroup.mem_centralizer_singleton_iff.mpr (mem_autFix_conjPerm_iff.mp (hK k.2))⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let ρ : K →* Perm τ.cycleFactorsFinset := (OnCycleFactors.toPermHom τ).comp ι
  haveI : Group.IsPerfect ρ.range :=
    Group.IsPerfect.ofSurjective (f := ρ.rangeRestrict) ρ.rangeRestrict_surjective
  have hcard : Nat.card ρ.range ∣ 2 ^ 3 * 3 ^ 1 := by
    have h1 : Nat.card ρ.range ∣ Nat.card (Perm τ.cycleFactorsFinset) :=
      Subgroup.card_subgroup_dvd_card _
    rw [Nat.card_perm, Nat.card_eq_finsetCard] at h1
    have hF : τ.cycleFactorsFinset.card ≤ 4 := by rw [← card_cycleType_eq]; exact hk
    exact h1.trans ((Nat.factorial_dvd_factorial hF).trans (by decide))
  have hpf : (Nat.card ρ.range).primeFactors.card ≤ 2 :=
    primeFactors_card_le_two_of_dvd Nat.prime_two Nat.prime_three hcard
  haveI := subsingleton_of_isPerfect_of_card_primeFactors hpf
  have h1 : ρ ⟨x, hx⟩ = 1 := by
    have : (⟨ρ ⟨x, hx⟩, ⟨_, rfl⟩⟩ : ρ.range) = 1 := Subsingleton.elim _ _
    exact congrArg Subtype.val this
  have h2 := congrArg
    (fun φ : Perm τ.cycleFactorsFinset => ((φ ⟨c, hc⟩ : τ.cycleFactorsFinset) : Perm (Fin n))) h1
  simp only [ρ, MonoidHom.comp_apply, OnCycleFactors.coe_toPermHom, Perm.one_apply] at h2
  calc (x : Perm (Fin n)) * c = (x : Perm (Fin n)) * c * (x : Perm (Fin n))⁻¹ * x := by group
    _ = c * x := by rw [show (x : Perm (Fin n)) * c * (x : Perm (Fin n))⁻¹ = c from h2]

theorem le_range_ofSubtype_of_card_cycleType_le {τ : Perm (Fin n)}
    (hk : Multiset.card τ.cycleType ≤ 4) {K : Subgroup (alternatingGroup (Fin n))}
    (hK : K ≤ autFix (conjPerm n τ)) [Group.IsPerfect K] :
    K ≤ (alternatingGroup.ofSubtype τ.supportᶜ).range := by
  intro x hx
  rw [alternatingGroup.mem_range_ofSubtype_iff]
  intro m hm
  rw [Finset.mem_compl]
  intro hmτ
  have hc : τ.cycleOf m ∈ τ.cycleFactorsFinset := cycleOf_mem_cycleFactorsFinset_iff.mpr hmτ
  have hKc : K ≤ autFix (conjPerm n (τ.cycleOf m)) := fun y hy =>
    mem_autFix_conjPerm_iff.mpr (commute_cycleFactors_of_isPerfect hk hK hy hc)
  have hcyc : (τ.cycleOf m).IsCycle := (mem_cycleFactorsFinset_iff.mp hc).1
  have h := le_range_ofSubtype_of_isPerfect hcyc hKc hx
  rw [alternatingGroup.mem_range_ofSubtype_iff] at h
  have hm' := h hm
  rw [Finset.mem_compl] at hm'
  exact hm' (mem_support_cycleOf_iff.mpr ⟨SameCycle.refl _ _, hmτ⟩)

theorem good427_alternating {τ : Perm (Fin n)} (hk : Multiset.card τ.cycleType ≤ 4)
    (hΩ : Fintype.card ↥(τ.supportᶜ) ≠ 5) : Good427 (autFix (conjPerm n τ)) := by
  have hEC := range_ofSubtype_le_autFix τ
  have hle : ∀ K : Subgroup (alternatingGroup (Fin n)), K ≤ autFix (conjPerm n τ) →
      Group.IsPerfect K → K ≤ (alternatingGroup.ofSubtype τ.supportᶜ).range :=
    fun K hK _ => le_range_ofSubtype_of_card_cycleType_le hk hK
  let ψ : alternatingGroup ↥(τ.supportᶜ) ≃* (alternatingGroup.ofSubtype τ.supportᶜ).range :=
    MonoidHom.ofInjective alternatingGroup.ofSubtype_injective
  by_cases h5 : 5 ≤ Fintype.card ↥(τ.supportᶜ)
  · have h6 : 6 ≤ Fintype.card ↥(τ.supportᶜ) := by omega
    haveI : IsSimpleGroup (alternatingGroup ↥(τ.supportᶜ)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card]; omega)
    haveI : IsSimpleGroup (alternatingGroup.ofSubtype τ.supportᶜ).range := ψ.symm.isSimpleGroup
    have hna : ∃ a b : (alternatingGroup.ofSubtype τ.supportᶜ).range, a * b ≠ b * a := by
      have hnc : ¬ IsMulCommutative (alternatingGroup ↥(τ.supportᶜ)) := by
        rw [alternatingGroup.isMulCommutative_iff_card_le_three, Nat.card_eq_fintype_card]
        omega
      by_contra h
      push Not at h
      exact hnc ⟨⟨fun a b => ψ.injective (by rw [map_mul, map_mul]; exact h _ _)⟩⟩
    have hcard : Nat.card (alternatingGroup.ofSubtype τ.supportᶜ).range ≠ 60 := by
      rw [← Nat.card_congr ψ.toEquiv, nat_card_alternatingGroup_of_card rfl (by omega)]
      have h720 : (6 : ℕ).factorial ≤ (Fintype.card ↥(τ.supportᶜ)).factorial :=
        Nat.factorial_le h6
      have : (6 : ℕ).factorial = 720 := rfl
      omega
    exact good427_of_le_simple hEC hna hcard hle
  · intro K hKC hKq _ hT
    haveI : Group.IsPerfect K := hKq.1
    have hKE := hle K hKC inferInstance
    obtain ⟨a, ha⟩ := exists_card_eq_sixty_mul hT
    have h1 : Nat.card K ≤ Nat.card (alternatingGroup.ofSubtype τ.supportᶜ).range :=
      Subgroup.card_le_of_le hKE
    have h2 : Nat.card (alternatingGroup.ofSubtype τ.supportᶜ).range ≤ 24 := by
      rw [← Nat.card_congr ψ.toEquiv]
      calc Nat.card (alternatingGroup ↥(τ.supportᶜ)) ≤ Nat.card (Perm ↥(τ.supportᶜ)) :=
            Subgroup.card_le_card_group _
        _ = (Fintype.card ↥(τ.supportᶜ)).factorial := by
            rw [Nat.card_perm, Nat.card_eq_fintype_card]
        _ ≤ (4 : ℕ).factorial := Nat.factorial_le (by omega)
        _ = 24 := rfl
    have h60 : 60 ≤ 60 * 2 ^ a := Nat.le_mul_of_pos_right _ (by positivity)
    omega

end Cycles

section Rows

theorem noCfgS427_alternating {n : ℕ} (hn5 : 5 ≤ n) (hn : n ≤ 12) (h8 : n ≠ 8) (h11 : n ≠ 11) :
    NoCfgS427 (alternatingGroup (Fin n)) := by
  refine noCfgS427_of_inner (alternatingGroup.center_eq_bot (by simp; omega))
    (not_three_dvd_outer_alternatingGroup hn5) fun s hs => ?_
  have hconj : MulAut.conj s = conjPerm n (s : Perm (Fin n)) := by
    ext x
    rw [conjPerm_apply]
    rfl
  rw [← autFix_conj, hconj]
  set τ : Perm (Fin n) := (s : Perm (Fin n)) with hτ
  have hτ3 : τ ^ 3 = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs] at h
    have := congrArg Subtype.val h
    simpa [hτ] using this
  have hτ1 : τ ≠ 1 := by
    intro h
    have : s = 1 := Subtype.ext h
    rw [this, orderOf_one] at hs
    exact absurd hs (by norm_num)
  have hord : orderOf τ ∣ 3 := orderOf_dvd_of_pow_eq_one hτ3
  have hmem : ∀ m ∈ τ.cycleType, m = 3 := fun m hm => by
    have h2 := two_le_of_mem_cycleType hm
    have hd := (dvd_of_mem_cycleType hm).trans hord
    have : m ≤ 3 := Nat.le_of_dvd (by norm_num) hd
    interval_cases m
    · norm_num at hd
    · rfl
  set k := Multiset.card τ.cycleType with hk
  have hrep : τ.cycleType = Multiset.replicate k 3 := Multiset.eq_replicate.mpr ⟨rfl, hmem⟩
  have hsupp : τ.support.card = 3 * k := by
    rw [← sum_cycleType, hrep, Multiset.sum_replicate, smul_eq_mul, mul_comm]
  have hsum : 3 * k ≤ n := by
    have := τ.support.card_le_univ
    rw [Fintype.card_fin] at this
    omega
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr fun h0 =>
    hτ1 (card_cycleType_eq_zero.mp (by rw [← hk]; exact h0))
  have hΩ : Fintype.card ↥(τ.supportᶜ) = n - 3 * k := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hsupp]
  exact good427_alternating (by omega) (by rw [hΩ]; omega)



theorem rowOf427_alternating
    {n : ℕ} (hn5 : 5 ≤ n) (hn : n ≤ 12) (h8 : n ≠ 8) (h11 : n ≠ 11) :
    RowOf427 (alternatingGroup (Fin n)) := by
  refine rowOf427_of_noCfgS fun S _ _ _ _ ⟨e⟩ =>
    ⟨NoCfgS427.of_mulEquiv e (noCfgS427_alternating hn5 hn h8 h11), noONS427_of_card ?_⟩
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  interval_cases n <;> norm_num [Nat.factorial] at *

end Rows

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
