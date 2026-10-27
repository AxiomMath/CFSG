module

public import CFSG.Walter.Bender1970.S2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_19
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.Adapters.GeneralizedFitting
import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter

theorem fittingSubgroup_le_centralizer_of_mem_sylow {Y : Type*} [Group Y] [Finite Y]
    (hY : HasAbelianSylowTwo Y) (S : Sylow 2 Y) {s : Y} (hs : s ∈ (S : Subgroup Y))
    (hsO : s ∈ Subgroup.centralizer (pPrimeCore 2 Y : Set Y)) :
    CFSG.fittingSubgroup Y ≤ Subgroup.centralizer ({s} : Set Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := hY S
  rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
  refine iSup_le fun p => ?_
  have hp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
  have : Fact (p : ℕ).Prime := ⟨hp⟩
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  by_cases hp2 : (p : ℕ) = 2
  · have hxS : x ∈ (S : Subgroup Y) := by
      have hle : pCore (p : ℕ) Y ≤ (S : Subgroup Y) := by
        rw [hp2]
        exact IsPGroup.le_sylow_of_normal (pCore_isPGroup (p := 2) (G := Y)) S
      exact hle hx
    exact setLike_mul_comm hxS hs
  · have hle : pCore (p : ℕ) Y ≤ pPrimeCore 2 Y := by
      refine le_sSup ⟨inferInstance, ?_⟩
      obtain ⟨k, hk⟩ := (pCore_isPGroup (p := (p : ℕ)) (G := Y)).exists_card_eq
      rw [hk]
      exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
    exact (Subgroup.mem_centralizer_iff.mp hsO x (hle hx))

theorem bender1970_2_1_of_hasAbelianSylowTwo {Y : Type} [Group Y] [Finite Y]
    (hY : HasAbelianSylowTwo Y) {P : Subgroup Y} (hP : IsPGroup 2 P)
    (hPO : P ≤ Subgroup.centralizer (pPrimeCore 2 Y : Set Y)) :
    P ≤ generalizedFittingSubgroupOf (⊤ : Subgroup Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hPS⟩ := hP.exists_le_sylow
  have hFit : CFSG.fittingSubgroupOf (⊤ : Subgroup Y) = CFSG.fittingSubgroup Y :=
    CFSG.Adapters.fittingSubgroupOf_top_eq_foundations Y
  have hEF : ∀ K : Subgroup Y, IsComponentOf K ⊤ →
      K ≤ Subgroup.centralizer (CFSG.fittingSubgroup Y : Set Y) := by
    intro K hK
    have := (CFSG.LocalCores.component_solvable_centralizer (R := CFSG.fittingSubgroup Y)
      inferInstance (CFSG.fittingSubgroup_normal).isSubnormal).1 K
      ((isComponent_iff_isComponentOf_top K).mpr hK)
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp this
  intro s hs
  have hsF := fittingSubgroup_le_centralizer_of_mem_sylow hY S (hPS hs) (hPO hs)
  obtain ⟨e, he, hconj⟩ := exists_mem_componentLayerOf_conj_eq' hY S (hPS hs)
  have heC : e ∈ Subgroup.centralizer (CFSG.fittingSubgroup Y : Set Y) :=
    (sSup_le fun K hK => hEF K hK) he
  have hc : e⁻¹ * s ∈
      Subgroup.centralizer (generalizedFittingSubgroupOf (⊤ : Subgroup Y) : Set Y) := by
    suffices hle : generalizedFittingSubgroupOf (⊤ : Subgroup Y) ≤
        Subgroup.centralizer ({e⁻¹ * s} : Set Y) by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hh)
    apply sup_le
    · try rw [show CFSG.GorensteinWalter.fittingSubgroupOf (⊤ : Subgroup Y) =
        CFSG.fittingSubgroupOf (⊤ : Subgroup Y) from rfl]
      rw [hFit]
      intro f hf
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : f * s = s * f := Subgroup.mem_centralizer_singleton_iff.mp (hsF hf)
      have h2 : f * e = e * f := Subgroup.mem_centralizer_iff.mp heC f hf
      have h2' : f * e⁻¹ = e⁻¹ * f := Commute.inv_right h2
      calc f * (e⁻¹ * s) = f * e⁻¹ * s := by rw [mul_assoc]
        _ = e⁻¹ * f * s := by rw [h2']
        _ = e⁻¹ * (s * f) := by rw [mul_assoc, h1]
        _ = e⁻¹ * s * f := by rw [mul_assoc]
    · apply sSup_le
      intro K hK x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := hconj K hK x hx
      calc x * (e⁻¹ * s) = e⁻¹ * (e * x * e⁻¹) * s := by group
        _ = e⁻¹ * (s * x * s⁻¹) * s := by rw [h]
        _ = e⁻¹ * s * x := by group
  have hcF := CFSG.Adapters.centralizer_generalizedFittingSubgroupOf_top_le hc
  have heF : e ∈ generalizedFittingSubgroupOf (⊤ : Subgroup Y) :=
    (le_sup_right : componentLayerOf (⊤ : Subgroup Y) ≤ _) he
  have : s = e * (e⁻¹ * s) := by group
  rw [this]
  exact mul_mem heF hcF

theorem bender1970_2_1 {X : Type} [Group X] [Finite X] (hX : IsAStar X) {P : Subgroup X}
    (hP : IsPGroup 2 P) (hPO : P ≤ Subgroup.centralizer (pPrimeCore 2 X : Set X)) :
    P ≤ generalizedFittingSubgroupOf (⊤ : Subgroup X) :=
  bender1970_2_1_of_hasAbelianSylowTwo hX.1 hP hPO

theorem bender1970_2_1_subgroup {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : IsAStar H) {P : Subgroup G} (hPH : P ≤ H) (hP : IsPGroup 2 P)
    (hPO : P ≤ Subgroup.centralizer (oddCoreOf H : Set G)) :
    P ≤ generalizedFittingSubgroupOf H := by
  have hP' : IsPGroup 2 (P.subgroupOf H) := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  have hPO' : P.subgroupOf H ≤ Subgroup.centralizer (pPrimeCore 2 H : Set H) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hPO (Subgroup.mem_subgroupOf.mp hx)) (y : G)
      ⟨y, hy, rfl⟩
  have h := bender1970_2_1 hH hP' hPO'
  rw [← generalizedFittingSubgroupOf_subgroup_top_eq H]
  intro x hx
  exact ⟨⟨x, hPH hx⟩, h (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

end CFSG.Walter
