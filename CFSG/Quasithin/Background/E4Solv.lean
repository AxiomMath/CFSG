module

public import CFSG.Quasithin.Background.StabSubBasics
public import CFSG.Quasithin.Background.E3Odd
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.GroupTheory.LocalCores.Fitting

public section

namespace CFSG.Quasithin

namespace E3

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

section Solv

variable {W : Type*} [CommGroup W] [Finite W]

theorem fittingSubgroup_le_fusionOddCore {X : Type*} [Group X] [Finite X]
    (hO2 : CFSG.Open.pCore 2 X = ⊥) : CFSG.fittingSubgroup X ≤ fusionOddCore X := by
  rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
  refine iSup_le fun p => ?_
  have hp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
  have : Fact (p : ℕ).Prime := ⟨hp⟩
  by_cases hp2 : (p : ℕ) = 2
  · rw [hp2, hO2]
    exact bot_le
  · refine le_sSup ⟨CFSG.LieType.BorelTits.pCore_normal _, ?_⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1
      (CFSG.LieType.BorelTits.pCore_isPGroup (G := X) (p : ℕ))
    rw [hn]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow

theorem aSet_two_eq_empty (hW : ∀ w : W, w ^ 2 = 1) {X : Subgroup (MulAut W)}
    (hsolv : Group.IsSolvable ↥X) (hO2 : CFSG.Open.pCore 2 ↥X = ⊥) : aSet 2 X = ∅ := by
  ext A
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hA
  have h40 := e3_40 hW hA
  obtain ⟨hAX, hA1, hAab, -⟩ := hA
  have hFo : CFSG.fittingSubgroup ↥X ≤ fusionOddCore ↥X := fittingSubgroup_le_fusionOddCore hO2
  have hAF : A.subgroupOf X ≤ Subgroup.centralizer ((CFSG.fittingSubgroup ↥X : Subgroup ↥X) :
      Set ↥X) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hf' : (f : MulAut W) ∈ oddCoreIn X := ⟨f, hFo hf, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.1 (h40 ha) _ hf'
    exact Subtype.ext h1
  have hAF' : A.subgroupOf X ≤ CFSG.fittingSubgroup ↥X := fun a ha =>
    CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv (hAF ha)
  have hAO : A ≤ oddCoreIn X := by
    intro x hx
    exact ⟨⟨x, hAX hx⟩, hFo (hAF' (show (⟨x, hAX hx⟩ : ↥X) ∈ A.subgroupOf X from hx)), rfl⟩
  have hA2 : IsPGroup 2 A := isPGroup_of_isElemAbelian2 hAab
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hA2
  have hdvd : Nat.card A ∣ Nat.card (oddCoreIn X) := Subgroup.card_dvd_of_le hAO
  rw [hk] at hdvd
  have hk0 : k = 0 := by
    by_contra hne
    exact (Nat.not_even_iff_odd.mpr (odd_card_oddCoreIn' X))
      (even_iff_two_dvd.mpr ((dvd_pow_self 2 hne).trans hdvd))
  rw [hk0, pow_zero] at hk
  exact hA1 (Subgroup.card_eq_one.mp hk)

omit [Finite W] in
theorem isElemAbelian2_zpowers {t : MulAut W} (ht : t ^ 2 = 1) :
    IsElemAbelian2 (Subgroup.zpowers t) :=
  CFSG.Quasithin.StabLat.isElemAbelian2_zpowers ht

theorem e4_1 (hW : ∀ w : W, w ^ 2 = 1) {X : Subgroup (MulAut W)} (hsolv : Group.IsSolvable ↥X)
    (hO2 : CFSG.Open.pCore 2 ↥X = ⊥) (hev : Even (Nat.card X)) : aParam X = 1 := by
  simp only [aParam, hev, ↓reduceIte]
  have hsub : {k : ℕ | 0 < k ∧ (aSet k X).Nonempty} = {1} := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hk, A, hA⟩
      by_contra hk1
      have hA2 : A ∈ aSet 2 X := aSet_anti (by omega) X hA
      rw [aSet_two_eq_empty hW hsolv hO2] at hA2
      exact hA2
    · rintro rfl
      refine ⟨Nat.one_pos, ?_⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 2 (even_iff_two_dvd.1 hev)
      set t : MulAut W := (x : MulAut W) with ht
      have hto : orderOf t = 2 := by rw [ht, Subgroup.orderOf_coe, hx]
      have ht2 : t ^ 2 = 1 := by rw [← hto]; exact pow_orderOf_eq_one t
      refine ⟨Subgroup.zpowers t, ?_⟩
      rw [aSet_one]
      refine ⟨(Subgroup.zpowers_le).2 x.2, ?_, isElemAbelian2_zpowers ht2⟩
      intro h
      have hmem : t ∈ Subgroup.zpowers t := Subgroup.mem_zpowers t
      rw [h, Subgroup.mem_bot] at hmem
      rw [hmem, orderOf_one] at hto
      omega
  rw [hsub, csSup_singleton]

end Solv

end E3

end CFSG.Quasithin
