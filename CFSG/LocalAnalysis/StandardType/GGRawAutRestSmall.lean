module

public import CFSG.LocalAnalysis.StandardType.GGRawAutRestCore
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldCyclicLabels
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.StandardType.MarkingSmall
public import CFSG.LocalAnalysis.ComponentInitial.InvolutionFixedFourGroupTransport
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryTransport
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.Sporadic.Schreier.TitsOther

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

namespace RawAutSmall

theorem mem_inner_u33 {K : Type} [Field K] (hu : UnitaryFieldData 3 1 K)
    {β : MulAut (primeFormP hu ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))} {m : ℕ}
    (hm : Odd m) (hβ : β ^ m = 1) :
    β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner _ := by
  have hC : IsPrimeFormGram (1 : GL (Fin 3) K) := isPrimeFormGram_one
  have hq : ¬(3 = 3 ∧ 3 ^ 1 = 2) := by norm_num
  obtain ⟨-, -, -, -, -, -, -, hker, -, -, hcard⟩ :=
    unitary_prime_form_full_semilinear_realization hu hC le_rfl hq
  have := hu.finite
  have hK9 : Nat.card K = 3 ^ 2 := hu.card.trans (by norm_num)
  have hAut : Nat.card (K ≃+* K) = 2 :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_three K hK9).1
  have hΘ : primeFormFieldFactor hu hC le_rfl hq β = 1 := by
    have h1 : orderOf (primeFormFieldFactor hu hC le_rfl hq β) ∣ m :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hβ, map_one])
    have h2 : orderOf (primeFormFieldFactor hu hC le_rfl hq β) ∣ 2 :=
      hAut ▸ orderOf_dvd_natCard _
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left h1 (Nat.coprime_two_right.mpr hm)) h2)
  have hβD : β ∈ primeFormD hu ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [← hker]
    exact hΘ
  have hD1 : (⟨β, hβD⟩ : primeFormD hu ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) ^ m = 1 :=
    Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hβ)
  have hy1 : orderOf (QuotientGroup.mk ⟨β, hβD⟩ :
      primeFormD hu ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ⧸
        (CFSG.ComponentClassification.OuterAutomorphisms.inner
          (primeFormP hu ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))).subgroupOf
          (primeFormD hu ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))) ∣ m :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hD1, QuotientGroup.mk_one])
  have hy2 : orderOf (QuotientGroup.mk ⟨β, hβD⟩ :
      primeFormD hu ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ⧸
        (CFSG.ComponentClassification.OuterAutomorphisms.inner
          (primeFormP hu ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))).subgroupOf
          (primeFormD hu ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))) ∣ 2 ^ 2 :=
    (orderOf_dvd_natCard _).trans (hcard.trans (by norm_num))
  have hy := orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hy1
    (Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr hm))) hy2)
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hy
  exact hy

theorem mem_inner_g2der {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2)
    (hR : ∃ x y : LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true), x * y ≠ y * x)
    {m : ℕ} (hm : Odd m)
    {α : MulAut (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true))}
    (hα : α ^ m = 1) : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner _ := by
  have hC : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true)) .PSU 3 3 1 := by
    rcases lieModel_g2der K hK hR with ⟨-, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact h
    · simp [chevalleyExceptionalTags] at ht
    · simp [reeTitsTags] at ht
    · cases ht
  obtain ⟨-, K', _, _, hK', ⟨e⟩⟩ := hC
  have hu : UnitaryFieldData 3 1 K' := ⟨Nat.prime_three, le_rfl, hK'.trans (by norm_num)⟩
  obtain ⟨⟨e'⟩, -⟩ := unitary_prime_form_full_semilinear_realization hu
    (isPrimeFormGram_one (K := K') (n := 3)) le_rfl (by norm_num)
  have E : LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true) ≃*
      primeFormP hu ((1 : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K') :=
    e.trans ((unitaryPSUEquiv hu (by norm_num : 1 ≤ 3)).symm.trans e'.symm)
  have hβ : MulAut.congr E α ^ m = 1 := by rw [← map_pow, hα, map_one]
  exact (CFSG.LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff E α).mp
    (mem_inner_u33 hu hm hβ)

theorem ggRawPCyclic_g2der {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {p : ℕ} (hp : Odd p) :
    GGRawPCyclic p (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true))
      (LargeEvenChevIDImage LargeEvenCartanG2 K (LargeEvenChevH LargeEvenCartanG2 K true))
      (LargeEvenChevFieldImage LargeEvenCartanG2 K (LargeEvenChevH LargeEvenCartanG2 K true)) := by
  intro hs hna
  refine ggRawPCyclic_of_mem
    (F := LargeEvenChevFieldImage LargeEvenCartanG2 K (LargeEvenChevH LargeEvenCartanG2 K true))
    (MulAut.conj : _ →* MulAut _).range ?_ (fun α ⟨_, hk⟩ => mem_inner_g2der hK hna hp.pow hk)
    hs hna
  rw [LargeEvenChevIDImage, chevID_closure_eq_inn_of_card_two hK]

theorem ggOddAutInnField_g2der {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {p : ℕ} (hp : Odd p)
    (hR : ∃ x y : LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true), x * y ≠ y * x) :
    GGOddAutInnField p
      (LargeEvenChevIDImage LargeEvenCartanG2 K (LargeEvenChevH LargeEvenCartanG2 K true))
      (LargeEvenChevFieldImage LargeEvenCartanG2 K (LargeEvenChevH LargeEvenCartanG2 K true)) := by
  intro φ hφ
  obtain ⟨r, rfl⟩ := mem_inner_g2der hK hR hp hφ
  exact ⟨MulAut.conj r, conj_mem_chevIDImage _ r, 1, Subgroup.one_mem _, (mul_one _).symm⟩

section Tits


theorem isPGroup_outer_twF4der {a : ℕ} (ha : a = 0) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    IsPGroup 2 (Outer (LargeEvenCenterQuot (LargeEvenTwF4H a K))) := by
  subst ha
  exact (CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier _ 2 1
    ⟨⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩, 0, rfl, reeTitsRelationModel_largeEven 0 hK⟩).1

theorem ggRawPCyclic_twF4der {a : ℕ} (ha : a = 0) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : Odd p) :
    GGRawPCyclic p (LargeEvenCenterQuot (LargeEvenTwF4H a K))
      (LargeEvenChevIDImage LargeEvenCartanF4 K (LargeEvenTwF4H a K))
      (LargeEvenChevFieldImage LargeEvenCartanF4 K (LargeEvenTwF4H a K)) := by
  have h2 := isPGroup_outer_twF4der ha hK
  subst ha
  have hK2 : Nat.card K = 2 := by simpa using hK
  refine ggRawPCyclic_of_mem (MulAut.conj : _ →* MulAut _).range ?_ fun α ⟨_, hk⟩ =>
    RawAut.mem_inner_of_isPGroup_outer h2 hp.pow hk
  rw [LargeEvenChevIDImage, chevID_closure_eq_inn_of_card_two hK2]

theorem ggOddAutInnField_twF4der {a : ℕ} (ha : a = 0) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : Odd p) :
    GGOddAutInnField p (LargeEvenChevIDImage LargeEvenCartanF4 K (LargeEvenTwF4H a K))
      (LargeEvenChevFieldImage LargeEvenCartanF4 K (LargeEvenTwF4H a K)) :=
  RawAut.ggOddAutInnField_of_isPGroup_outer (isPGroup_outer_twF4der ha hK)
    (conj_mem_chevIDImage _) hp

end Tits

end RawAutSmall

open RawAutSmall

theorem ggRawPCyclicOn_g2der :
    GGRawPCyclicOn fun _ lab => lab.tag = .G2der := by
  intro p hp hp2 lab _ ht Q h
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  exact recipeChevalley_and (fun K _ _ hK => ggRawPCyclic_g2der hK (hp.odd_of_ne_two hp2)) h

theorem ggOddAutOn_g2der :
    GGOddAutOn fun lab => lab.tag = .G2der := by
  intro p lab hp hp2 _ ht _ Q h
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  exact recipeChevalley_and (P := fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      GGOddAutInnField p I F)
    (fun K _ _ hK _ hR => ggOddAutInnField_g2der hK (hp.odd_of_ne_two hp2) hR) h

section Tits


theorem ggRawPCyclicOn_twF4der : GGRawPCyclicOn fun _ lab => lab.tag = .twF4der := by
  intro p hp hp2 lab hlab ht Q h
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  obtain ⟨-, -, hn1⟩ := hlab
  subst hn1
  exact recipeTwF4_and (fun K _ _ hK => ggRawPCyclic_twF4der (by norm_num) hK
    (hp.odd_of_ne_two hp2)) h

theorem ggOddAutOn_twF4der : GGOddAutOn fun lab => lab.tag = .twF4der := by
  intro p lab hp hp2 hlab ht _ Q h
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  obtain ⟨-, -, hn1⟩ := hlab
  subst hn1
  exact recipeTwF4_and (P := fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      GGOddAutInnField p I F)
    (fun K _ _ hK _ _ => ggOddAutInnField_twF4der (by norm_num) hK (hp.odd_of_ne_two hp2)) h

end Tits

end CFSG.StandardType

end
