module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Solvable
import CFSG.GroupTheory.OrderBelowSixtySolvable
import CFSG.LocalAnalysis.GLTheoremA.Basic
import CFSG.RankThree.PartTwo.Sec21.FF84A8
import CFSG.Quasithin.SteinbergCBAlternatingAut

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

private theorem exph_fin_card_centA_le_centPerm {n : ℕ} (σ : Equiv.Perm (Fin n))
    (hσ : σ ∈ alternatingGroup (Fin n)) :
    Nat.card (Subgroup.centralizer ({⟨σ, hσ⟩} : Set (alternatingGroup (Fin n)))) ≤
      Nat.card (Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin n)))) := by
  classical
  have key : ∀ x : Subgroup.centralizer ({⟨σ, hσ⟩} : Set (alternatingGroup (Fin n))),
      x.val.val * σ = σ * x.val.val := by
    intro x
    have hx := x.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    exact congrArg Subtype.val hx
  refine Nat.card_le_card_of_injective
    (fun x : Subgroup.centralizer ({⟨σ, hσ⟩} : Set (alternatingGroup (Fin n))) =>
      (⟨x.val.val, ?_⟩ : Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin n))))) ?_
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact key x
  · intro x y hxy
    have h1 : x.val.val = y.val.val :=
      congrArg (fun z : Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin n))) =>
        (z : Equiv.Perm (Fin n))) hxy
    exact Subtype.ext (Subtype.ext h1)

private theorem exph_fin_card_cent_perm_eight_five (g : Equiv.Perm (Fin 8))
    (hc : g.cycleType = {5}) :
    Nat.card (Subgroup.centralizer ({g} : Set (Equiv.Perm (Fin 8)))) = 30 := by
  rw [Equiv.Perm.nat_card_centralizer, hc]
  decide

private theorem exph_fin_card_cent_perm_eight_seven (g : Equiv.Perm (Fin 8))
    (hc : g.cycleType = {7}) :
    Nat.card (Subgroup.centralizer ({g} : Set (Equiv.Perm (Fin 8)))) = 7 := by
  rw [Equiv.Perm.nat_card_centralizer, hc]
  decide

private theorem exph_fin_card_cent_perm_eight_three_three (g : Equiv.Perm (Fin 8))
    (hc : g.cycleType = {3, 3}) :
    Nat.card (Subgroup.centralizer ({g} : Set (Equiv.Perm (Fin 8)))) = 36 := by
  rw [Equiv.Perm.nat_card_centralizer, hc]
  decide

private theorem exph_fin_card_cent_perm_eight_lt_sixty (g : Equiv.Perm (Fin 8))
    (hc : g.cycleType = {5} ∨ g.cycleType = {7} ∨ g.cycleType = {3, 3}) :
    Nat.card (Subgroup.centralizer ({g} : Set (Equiv.Perm (Fin 8)))) < 60 := by
  rcases hc with h | h | h
  · rw [exph_fin_card_cent_perm_eight_five g h]; norm_num
  · rw [exph_fin_card_cent_perm_eight_seven g h]; norm_num
  · rw [exph_fin_card_cent_perm_eight_three_three g h]; norm_num

private theorem exph_fin_cycleType_eq_five_of_orderOf_eq_five (σ : Equiv.Perm (Fin 8))
    (h : orderOf σ = 5) : σ.cycleType = {5} := by
  have hp : (orderOf σ).Prime := by rw [h]; norm_num
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order hp
  rw [h] at hn
  have hsum : (Multiset.replicate (n + 1) (5 : ℕ)).sum ≤ 8 := by
    rw [← hn, Equiv.Perm.sum_cycleType]
    exact (Finset.card_le_univ _).trans (by simp)
  rw [Multiset.sum_replicate, smul_eq_mul] at hsum
  have hn0 : n = 0 := by omega
  rw [hn, hn0]
  simp

private theorem exph_fin_cycleType_eq_seven_of_orderOf_eq_seven (σ : Equiv.Perm (Fin 8))
    (h : orderOf σ = 7) : σ.cycleType = {7} := by
  have hp : (orderOf σ).Prime := by rw [h]; norm_num
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order hp
  rw [h] at hn
  have hsum : (Multiset.replicate (n + 1) (7 : ℕ)).sum ≤ 8 := by
    rw [← hn, Equiv.Perm.sum_cycleType]
    exact (Finset.card_le_univ _).trans (by simp)
  rw [Multiset.sum_replicate, smul_eq_mul] at hsum
  have hn0 : n = 0 := by omega
  rw [hn, hn0]
  simp

private theorem exph_fin_card_mulAut_alt_five :
    Nat.card (MulAut (alternatingGroup (Fin 5))) = 120 := by
  have hbij : Function.Bijective (CFSG.Quasithin.SteinbergCB.conjPerm 5) :=
    ⟨CFSG.Quasithin.SteinbergCB.conjPerm_injective (by norm_num),
      CFSG.Quasithin.SteinbergCB.conjPerm_surjective (Or.inl rfl)⟩
  rw [← Nat.card_congr (MulEquiv.ofBijective (CFSG.Quasithin.SteinbergCB.conjPerm 5) hbij).toEquiv,
    Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  norm_num

theorem exc_A8_centralizer_solvable (σ : Equiv.Perm (Fin 8)) (hσ : σ ∈ alternatingGroup (Fin 8))
    (h : orderOf σ = 5 ∨ orderOf σ = 7 ∨ (orderOf σ = 3 ∧ σ.cycleType = {3, 3})) :
    IsSolvable (Subgroup.centralizer ({⟨σ, hσ⟩} : Set (alternatingGroup (Fin 8)))) := by
  have hle := exph_fin_card_centA_le_centPerm σ hσ
  rcases h with h5 | h7 | ⟨_, h33⟩
  · have hct : σ.cycleType = {5} := exph_fin_cycleType_eq_five_of_orderOf_eq_five σ h5
    have hlt : Nat.card (Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 8)))) < 60 :=
      exph_fin_card_cent_perm_eight_lt_sixty σ (Or.inl hct)
    exact CFSG.GroupTheory.groups_order_below_sixty_solvable (lt_of_le_of_lt hle hlt)
  · have hct : σ.cycleType = {7} := exph_fin_cycleType_eq_seven_of_orderOf_eq_seven σ h7
    have hlt : Nat.card (Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 8)))) < 60 :=
      exph_fin_card_cent_perm_eight_lt_sixty σ (Or.inr (Or.inl hct))
    exact CFSG.GroupTheory.groups_order_below_sixty_solvable (lt_of_le_of_lt hle hlt)
  · have hlt : Nat.card (Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 8)))) < 60 :=
      exph_fin_card_cent_perm_eight_lt_sixty σ (Or.inr (Or.inr h33))
    exact CFSG.GroupTheory.groups_order_below_sixty_solvable (lt_of_le_of_lt hle hlt)

private theorem exph_fin_commutator_le_of_subgroupOf_le
    {G : Type*} [Group G] (C H : Subgroup G) (hHC : H ≤ C)
    (h : commutator ↥C ≤ H.subgroupOf C) : ⁅C, C⁆ ≤ H := by
  have hmap : (commutator ↥C).map C.subtype ≤ (H.subgroupOf C).map C.subtype :=
    Subgroup.map_mono h
  have h1 : (commutator ↥C).map C.subtype = ⁅C, C⁆ := by
    rw [show commutator ↥C = ⁅(⊤ : Subgroup ↥C), ⊤⁆ from rfl, Subgroup.map_commutator,
      Subgroup.map_top, Subgroup.range_subtype]
  have h2 : (H.subgroupOf C).map C.subtype = H := by
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      exact Subgroup.mem_subgroupOf.mp hy
    · intro x hx
      exact ⟨⟨x, hHC hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  rwa [h1, h2] at hmap

private theorem exph_fin_a8_perfect_of_le_sup_alt_five
    {G : Type*} [Group G] [Finite G] (C H A : Subgroup G)
    (hC : C = A ⊔ H) (hHleC : H ≤ C)
    (hAcent : A ≤ Subgroup.centralizer (H : Set G))
    (hAcomm : IsMulCommutative ↥A)
    (hcardH : Nat.card H = 60)
    (J : Subgroup G) (hJ : J ≤ C) (hperf : ⁅J, J⁆ = J) :
    Nat.card J = 1 ∨ Nat.card J = 60 := by
  haveI : IsMulCommutative ↥A := hAcomm
  have hAleC : A ≤ C := by rw [hC]; exact le_sup_left
  have hCnorm : C ≤ Subgroup.normalizer (H : Set G) := by
    rw [hC]
    exact sup_le (hAcent.trans (Subgroup.centralizer_le_normalizer (H : Set G)))
      Subgroup.le_normalizer
  have hNnormal : (H.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHleC).mpr hCnorm
  have hKcomm : IsMulCommutative ↥(A.subgroupOf C) := Subgroup.subgroupOf_isMulCommutative C A
  have hsup_top : H.subgroupOf C ⊔ A.subgroupOf C = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hHleC hAleC, Subgroup.subgroupOf_eq_top, hC]
    exact le_of_eq (sup_comm A H)
  have hcomm_le : commutator ↥C ≤ H.subgroupOf C := by
    haveI : (H.subgroupOf C).Normal := hNnormal
    exact Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup_top hKcomm
  have hCC_le_H : ⁅C, C⁆ ≤ H := exph_fin_commutator_le_of_subgroupOf_le C H hHleC hcomm_le
  have hJleH : J ≤ H :=
    calc J = ⁅J, J⁆ := hperf.symm
      _ ≤ ⁅C, C⁆ := Subgroup.commutator_mono hJ hJ
      _ ≤ H := hCC_le_H
  have hJle60 : Nat.card J ≤ 60 := by
    have hinj : Function.Injective (fun j : J => (⟨j.val, hJleH j.2⟩ : H)) := by
      intro a b hab
      exact Subtype.ext (congrArg (fun z : H => (z : G)) hab)
    calc Nat.card J ≤ Nat.card H := Nat.card_le_card_of_injective _ hinj
      _ = 60 := hcardH
  rcases lt_or_eq_of_le hJle60 with hlt | heq
  · left
    have hsolv : Group.IsSolvable ↥J := CFSG.GroupTheory.groups_order_below_sixty_solvable hlt
    have hperfJ : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.mpr hperf
    have hsub : Subsingleton ↥J := by
      by_contra h
      haveI : Nontrivial ↥J := not_subsingleton_iff_nontrivial.mp h
      exact Group.IsPerfect.not_isSolvable ↥J hsolv
    exact Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
  · right
    exact heq

theorem exc_A8_three_cycle_perfect (σ : Equiv.Perm (Fin 8)) (hσ : σ ∈ alternatingGroup (Fin 8))
    (h3 : σ.cycleType = {3}) (J : Subgroup (alternatingGroup (Fin 8)))
    (hJ : J ≤ Subgroup.centralizer ({⟨σ, hσ⟩} : Set (alternatingGroup (Fin 8))))
    (hperf : ⁅J, J⁆ = J) : Nat.card J = 1 ∨ Nat.card J = 60 := by
  classical
  have hσ3 : σ.IsThreeCycle := by
    rw [← card_support_eq_three_iff, ← Equiv.Perm.sum_cycleType, h3]
    simp
  have ha8c : CFSG.LocalAnalysis.GLTheoremA.CatB.a8c.IsThreeCycle := by
    have h := Equiv.Perm.isThreeCycle_swap_mul_swap_same
      (show (1 : Fin 8) ≠ 0 by decide) (show (1 : Fin 8) ≠ 2 by decide)
      (show (0 : Fin 8) ≠ 2 by decide)
    rw [CFSG.LocalAnalysis.GLTheoremA.CatB.a8c, ← Equiv.swap_comm (1 : Fin 8) 0]
    exact h
  have ha8c8 : (CFSG.LocalAnalysis.GLTheoremA.CatB.a8c8 : Equiv.Perm (Fin 8)).IsThreeCycle :=
    ha8c
  obtain ⟨c, hc⟩ := isConj_iff.mp
    (alternatingGroup.isThreeCycle_isConj (α := Fin 8) (by norm_num)
      (σ := ⟨σ, hσ⟩) (τ := CFSG.LocalAnalysis.GLTheoremA.CatB.a8c8) hσ3 ha8c8)
  obtain ⟨H, ⟨eH⟩, -, hHleC, hsup, -⟩ :=
    CFSG.RankThree.PartTwo.Sec21.FF84.exists_H_of_conj (x := ⟨σ, hσ⟩) (y := 1) (g := c)
      (Or.inl hc) (by simp)
  have hHcent : H ≤ Subgroup.centralizer
      (Subgroup.zpowers (⟨σ, hσ⟩ : CFSG.LocalAnalysis.GLTheoremA.CatB.A8) :
        Set CFSG.LocalAnalysis.GLTheoremA.CatB.A8) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hHleC
  have hAcent : Subgroup.zpowers (⟨σ, hσ⟩ : CFSG.LocalAnalysis.GLTheoremA.CatB.A8) ≤
      Subgroup.centralizer (H : Set CFSG.LocalAnalysis.GLTheoremA.CatB.A8) :=
    Subgroup.le_centralizer_iff.mpr hHcent
  have hcardH : Nat.card H = 60 := by
    rw [Nat.card_congr eH.toEquiv, nat_card_alternatingGroup]
    norm_num
  exact exph_fin_a8_perfect_of_le_sup_alt_five
    (Subgroup.centralizer ({⟨σ, hσ⟩} : Set (alternatingGroup (Fin 8)))) H
    (Subgroup.zpowers (⟨σ, hσ⟩ : CFSG.LocalAnalysis.GLTheoremA.CatB.A8))
    hsup.symm hHleC hAcent (Subgroup.zpowers_isMulCommutative _) hcardH J hJ hperf

theorem exc_A5_aut_elementaryAbelian_card_le (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (H : Subgroup (MulAut (alternatingGroup (Fin 5))))
    (hcomm : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (hexp : ∀ x ∈ H, x ^ p = 1) :
    Nat.card H ≤ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hE : CFSG.Open.IsElemAbelian p H :=
    ⟨⟨⟨fun (x y : ↥H) => Subtype.ext (hcomm (x : MulAut (alternatingGroup (Fin 5))) x.2
      (y : MulAut (alternatingGroup (Fin 5))) y.2)⟩⟩, hexp⟩
  obtain ⟨k, hk⟩ := CFSG.LocalAnalysis.GLTheoremA.exists_card_eq_pow_of_isElemAbelian hp hE
  rw [hk]
  have hdvd : p ^ k ∣ 120 := by
    have h := Subgroup.card_subgroup_dvd_card H
    rwa [hk, exph_fin_card_mulAut_alt_five] at h
  have hk1 : k ≤ 1 := by
    by_contra h
    have hk2 : 2 ≤ k := by omega
    have h2 : p ^ 2 ∣ 120 := dvd_trans (pow_dvd_pow p hk2) hdvd
    have hp35 : p = 3 ∨ p = 5 := by
      have h120 : p ∣ 120 := by
        have hpk : p ∣ p ^ k := by simpa using pow_dvd_pow p (by omega : 1 ≤ k)
        exact dvd_trans hpk hdvd
      have h235 : p ∣ 2 ^ 3 * 3 * 5 := by
        rwa [show (120 : ℕ) = 2 ^ 3 * 3 * 5 by norm_num] at h120
      rcases (hp.dvd_mul).mp h235 with h | h
      · rcases (hp.dvd_mul).mp h with h | h
        · have h2' : p ∣ 2 := hp.dvd_of_dvd_pow h
          exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2') hp2
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h)
    rcases hp35 with rfl | rfl <;> norm_num at h2
  interval_cases k
  · simpa using hp.one_lt.le
  · simp

end CFSG.StandardType.LieKnownR2.ExcPos
