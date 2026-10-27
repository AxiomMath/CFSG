module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueGen
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotUnique
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsBasic

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.EvenSmallLie (StandardSetting)
open CFSG.SeitzReduction.F4Pilot (centerQuotientAut)

variable {f : ℕ} {K : Type} [Field K]

@[expose] def GraphFieldCoreTypeDet (h : UnitaryFieldData 2 f K) (n : ℕ) : Prop :=
  ∀ θ : MulAut (LinearFlag.projectiveSL n K), θ * θ = 1 →
    Nat.card (fixedSubgroup θ) ∣ 2 * Nat.card (MulAut (unitaryPSU h n)) →
    Nat.card (perfectCore (fixedSubgroup θ)) ∣ Nat.card (unitaryPSU h n) →
    Nat.card (unitaryPSU h n) ≤ Nat.card (perfectCore (fixedSubgroup θ))

variable (h : UnitaryFieldData 2 f K)

section Reduction

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem le_of_mem_normalizer_of_graphFieldCoreTypeDet (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {n : ℕ} (e : L ≃* unitaryPSU h n) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hTD : GraphFieldCoreTypeDet h n) {M : Subgroup G}
    (ψ₀ : M ⧸ center M ≃* LinearFlag.projectiveSL n K) (htM : t ∈ normalizer (M : Set G)) :
    L ≤ M := by
  have := h.finite
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  set τ := M.normalizerMonoidHom ⟨t, htM⟩ with hτ
  have hτ2 : τ * τ = 1 := by
    rw [← sq]
    exact F4Pilot.normalizerMonoidHom_sq_eq_one M htM (by rw [← ht]; exact pow_orderOf_eq_one t)
  set θ := MulAut.congr ψ₀ (centerQuotientAut τ) with hθ
  have hθ2 : θ * θ = 1 := by
    rw [hθ, ← map_mul, ← LinearPilot.centerQuotientAut_mul, hτ2,
      LinearPilot.centerQuotientAut_one, map_one]
  set P := perfectCore (M ⊓ centralizer ({t} : Set G)) with hP
  have hPL : P ≤ L := std_perfect_le hset hOut htC ht (CFSG.Quasithin.perfectCore_perfect _)
    ((CFSG.Quasithin.perfectCore_le _).trans inf_le_right)
  have hfixτ : (fixedSubgroup τ).map M.subtype = M ⊓ centralizer ({t} : Set G) := by
    rw [hτ, F4Pilot.fixedSubgroup_normalizerMonoidHom, subgroupOf_map_subtype, inf_comm]
  have hcardfixτ : Nat.card (fixedSubgroup τ) = Nat.card (M ⊓ centralizer ({t} : Set G) :
      Subgroup G) := by
    rw [← hfixτ, card_map_of_injective M.subtype_injective]
  have hcardP : Nat.card (perfectCore (fixedSubgroup τ)) = Nat.card P := by
    rw [hP, ← hfixτ, ← CFSG.Quasithin.map_perfectCore, card_map_of_injective M.subtype_injective]
  have h1 : Nat.card (fixedSubgroup θ) ∣ 2 * Nat.card (MulAut (unitaryPSU h n)) := by
    rw [hθ, LinearPilot.card_fixedSubgroup_congr]
    refine (LinearPilot.card_fixedSubgroup_centerQuotientAut_dvd τ).trans ?_
    rw [hcardfixτ]
    exact (Subgroup.card_dvd_of_le inf_le_right).trans
      (F4Pilot.card_centralizer_dvd_two_mul_card_mulAut e ht
        (CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hset.standard htC ht) hKt)
  have h2 : Nat.card (perfectCore (fixedSubgroup θ)) ∣ Nat.card P := by
    rw [hθ, LinearPilot.card_perfectCore_fixedSubgroup_congr,
      LinearPilot.perfectCore_fixedSubgroup_centerQuotientAut, ← hcardP]
    exact Subgroup.card_map_dvd _ (QuotientGroup.mk' (center M))
  have hPLcard : Nat.card P ∣ Nat.card (unitaryPSU h n) := by
    rw [← Nat.card_congr e.toEquiv]
    exact Subgroup.card_dvd_of_le hPL
  have h3 := hTD θ hθ2 h1 (h2.trans hPLcard)
  have h4 : Nat.card L ≤ Nat.card P := by
    rw [Nat.card_congr e.toEquiv]
    exact h3.trans (Nat.le_of_dvd Nat.card_pos h2)
  have hPeq : P = L := Subgroup.eq_of_le_of_card_ge hPL h4
  rw [← hPeq]
  exact (CFSG.Quasithin.perfectCore_le _).trans inf_le_left

end Reduction

section Unique

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem conjugate_eq_of_mem_normalizer_of_graphFieldCoreTypeDet (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {m : ℕ} (hm : 2 ≤ m) (hnq : (m + 1, 2 ^ f) ≠ (3, 2))
    (e : L ≃* unitaryPSU h (m + 1)) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hTD : GraphFieldCoreTypeDet h (m + 1)) {G₀ : Subgroup G}
    (hG₀ : G₀ = ⨆ i : Fin m, pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))))
    (hq : CFSG.IsQuasisimple G₀) (ψ : G₀ ⧸ center G₀ ≃* LinearFlag.projectiveSL (m + 1) K)
    (g : G) (htg : t ∈ normalizer (CFSG.conjugate G₀ g : Set G)) :
    CFSG.conjugate G₀ g = G₀ := by
  have : Group.IsPerfect G₀ := hq.1
  exact conjugate_eq_of_le_unitary h hset hOut hm hnq e
    (LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt) ht hG₀ ψ g htg
    (le_of_mem_normalizer_of_graphFieldCoreTypeDet h hset hOut e ht hKt hTD
      ((LinearPilot.conjugateQuotientCenterEquiv G₀ g).symm.trans ψ) htg)

theorem unique_of_graphFieldCoreTypeDet (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {m : ℕ} (hm : 2 ≤ m) (hnq : (m + 1, 2 ^ f) ≠ (3, 2))
    (e : L ≃* unitaryPSU h (m + 1)) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hTD : GraphFieldCoreTypeDet h (m + 1)) {G₀ : Subgroup G}
    (hG₀ : G₀ = ⨆ i : Fin m, pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))))
    (hq : CFSG.IsQuasisimple G₀) (ψ : G₀ ⧸ center G₀ ≃* LinearFlag.projectiveSL (m + 1) K) :
    ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G) :=
  F4Pilot.unique_of_forall_conjugate_eq fun g htg =>
    conjugate_eq_of_mem_normalizer_of_graphFieldCoreTypeDet h hset hOut hm hnq e ht hKt hTD hG₀
      hq ψ g htg

end Unique

end CFSG.SeitzReduction.UnitaryPilot
