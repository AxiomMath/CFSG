module

public import CFSG.LocalAnalysis.SolvableZJ.Thompson
import CFSG.GroupTheory.PCore.PrimeSetCore
import CFSG.GroupTheory.PStability.Solvable
public import CFSG.LocalAnalysis.SignalizerFunctor.SolvablePrimeCore

public section

open scoped Pointwise

namespace CFSG

open SignalizerFunctor

private theorem subgroupProduct_normalizer_eq_univ (p : ℕ) [Fact p.Prime]
    {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (hN : p.Coprime (Nat.card N)) (S : Sylow p G)
    (K : Subgroup G) (hKS : K ≤ (S : Subgroup G))
    (himage : (K.map (QuotientGroup.mk' N)).Normal) :
    subgroupProduct N (Subgroup.normalizer (K : Set G)) = Set.univ := by
  have hKP : IsPGroup p K := S.isPGroup'.to_le hKS
  have : (N ⊔ K).Normal := by
    rw [← QuotientGroup.comap_map_mk' (N := N) (H := K)]
    exact himage.comap (QuotientGroup.mk' N)
  have hNK : Disjoint K N := by
    obtain ⟨k, hk⟩ := hKP.exists_card_eq
    exact Subgroup.disjoint_of_coprime_natCard (by rw [hk]; exact hN.pow_left k)
  have hdisj : Disjoint (N.subgroupOf (N ⊔ K)) (K.subgroupOf (N ⊔ K)) := by
    refine Subgroup.disjoint_def.mpr fun {x} hxN hxK => Subtype.ext ?_
    exact Subgroup.disjoint_def.mp hNK (Subgroup.mem_subgroupOf.mp hxK)
      (Subgroup.mem_subgroupOf.mp hxN)
  have hmul : (N.subgroupOf (N ⊔ K) : Set ↥(N ⊔ K)) * (K.subgroupOf (N ⊔ K) : Set ↥(N ⊔ K)) =
      Set.univ := by
    have : (N.subgroupOf (N ⊔ K)).Normal := Subgroup.Normal.comap ‹N.Normal› (N ⊔ K).subtype
    rw [← Subgroup.normal_mul, ← Subgroup.subgroupOf_sup le_sup_left le_sup_right,
      Subgroup.subgroupOf_self, Subgroup.coe_top]
  have hcompl := Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hmul
  have hindex : ¬ p ∣ (K.subgroupOf (N ⊔ K)).index := by
    rw [hcompl.index_eq_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : N ≤ N ⊔ K)).toEquiv]
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp hN
  have hKsub : IsPGroup p (K.subgroupOf (N ⊔ K)) := hKP.comap_subtype
  let P : Sylow p ↥(N ⊔ K) := hKsub.toSylow hindex
  have hP : (P : Subgroup ↥(N ⊔ K)).map (N ⊔ K).subtype = K := by
    rw [IsPGroup.toSylow_coe, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr le_sup_right]
  have : Finite (Sylow p ↥(N ⊔ K)) := Sylow.finite_of_finiteIndex P
  have htop := Sylow.normalizer_sup_eq_top P
  rw [hP, ← sup_assoc, sup_eq_left.mpr (Subgroup.le_normalizer.trans le_sup_left),
    sup_comm] at htop
  refine Set.eq_univ_iff_forall.mpr fun g => ?_
  have hg : g ∈ ((N ⊔ Subgroup.normalizer (K : Set G) : Subgroup G) : Set G) := by
    rw [htop]
    exact Subgroup.mem_top g
  rw [Subgroup.normal_mul] at hg
  exact hg

private theorem isCharacteristicP_quotient_pPrimeCore (p : ℕ) [Fact p.Prime]
    (G : Type*) [Group G] [Finite G] [Group.IsSolvable G] :
    IsCharacteristicP p (G ⧸ pPrimeCore p G) := by
  have : Group.IsSolvable (G ⧸ pPrimeCore p G) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective (pPrimeCore p G))
  have hcore : Helpers.primeSetCore (GroupType := G ⧸ pPrimeCore p G) ({p}ᶜ) = ⊥ := by
    rw [← pPrimeCore_eq_helpersPrimeSetCore Fact.out]
    exact pPrimeCore_quotient_eq_bot Fact.out
  rw [IsCharacteristicP, pCore_eq_helpersPrimeSetCore Fact.out]
  exact Helpers.solvable_prime_core_self_centralizing p Fact.out hcore

private theorem isPStableAction_of_isSolvable (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    {G P : Type*} [Group G] [Finite G] [Group.IsSolvable G] [Group P] [Finite P]
    (hP : IsPGroup p P) (ρ : G →* MulAut P) :
    IsPStableAction p ρ := by
  intro x hx
  have hquad : ∀ u : P, ρ x⁻¹ (u⁻¹ * ρ x⁻¹ u) = u⁻¹ * ρ x⁻¹ u :=
    fun u => (inv_mul_eq_one.mp (hx u)).symm
  have hmem := solvable_action_p_stability p
    ((Fact.out : p.Prime).odd_of_ne_two (by omega)) G P hP ρ x⁻¹ (Or.inl hp) hquad
  simpa only [actionPrimeCore, Subgroup.mem_comap, map_inv, inv_inv] using
    (pCore p (G ⧸ ρ.ker)).inv_mem hmem

theorem solvable_zj_normalizer_factorization (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (G : Type*) [Group G] [Finite G] (hsolv : Group.IsSolvable G) (S : Sylow p G) :
    subgroupProduct (pPrimeCore p G)
      (Subgroup.normalizer (embeddedThompsonCenter (S : Subgroup G) : Set G)) =
      Set.univ := by
  set N := pPrimeCore p G
  have : N.Normal := pPrimeCore_normal
  have hcop : p.Coprime (Nat.card N) := pPrimeCore_coprime_card
  have hker : (QuotientGroup.mk' N).ker ⊓ (S : Subgroup G) = ⊥ := by
    obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
    have hdisj : Disjoint (S : Subgroup G) N :=
      Subgroup.disjoint_of_coprime_natCard (by rw [hk]; exact hcop.pow_left k)
    rw [QuotientGroup.ker_mk', inf_comm]
    exact hdisj.eq_bot
  have hstable : StableNormalPSubgroupActions p (G ⧸ N) := fun U hU hUp =>
    isPStableAction_of_isSolvable p hp hUp _
  let Sq : Sylow p (G ⧸ N) := Sylow.mapSurjective (QuotientGroup.mk'_surjective N) S
  have : (embeddedThompsonCenter (Sq : Subgroup (G ⧸ N))).Characteristic :=
    embeddedThompsonCenter_characteristic p (by omega) (G ⧸ N)
      (isCharacteristicP_quotient_pPrimeCore p G) Sq hstable
  have himage : ((embeddedThompsonCenter (S : Subgroup G)).map (QuotientGroup.mk' N)).Normal := by
    rw [map_embeddedThompsonCenter _ _ hker]
    exact inferInstanceAs (embeddedThompsonCenter (Sq : Subgroup (G ⧸ N))).Normal
  exact subgroupProduct_normalizer_eq_univ p N hcop S _ (embeddedThompsonCenter_le _) himage

end CFSG
