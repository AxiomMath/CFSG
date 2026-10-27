module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.InducedQuotInfAut
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.GroupTheory.CoprimeActionSupport.CoprimeAutomorphismFixedQuotientLift
import CFSG.GroupTheory.PCore.SolvableRadical

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open CFSG.GroupTheory.CoprimeActionSupport.CoprimeAutomorphismFixedQuotientLift
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem uc22s2112l3p_le_map_centralizer {L : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 L)) {b : G} (hb : b ∈ normalizer (L : Set G))
    (hbp : (orderOf b).Prime) (hb2 : orderOf b ≠ 2) {K : Subgroup (BarInf L)} (hK : ⁅K, K⁆ = K)
    (hfix : ∀ k ∈ K, inducedBarInfAutHom L ⟨b, hb⟩ k = k) :
    K ≤ ((centralizer ({b} : Set G)).subgroupOf L).map
      (QuotientGroup.mk' (CFSG.solvableRadical ↥L)) := by
  classical
  haveI : Fact (orderOf b).Prime := ⟨hbp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  set α : MulAut ↥L := L.normalizerMonoidHom ⟨b, hb⟩ with hαdef
  have hbpow : (⟨b, hb⟩ : ↥(normalizer (L : Set G))) ^ orderOf b = 1 := by
    rw [← Subgroup.orderOf_mk b hb]
    exact pow_orderOf_eq_one _
  have hα : α ^ orderOf b = 1 := by rw [hαdef, ← map_pow, hbpow, map_one]
  have hαy : ∀ y : ↥L, ((α y : ↥L) : G) = b * (y : G) * b⁻¹ := fun y => by
    rw [hαdef, Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hN2 : ∀ n ∈ CFSG.pCore 2 ↥L, α n ∈ CFSG.pCore 2 ↥L := fun n hn => by
    have h := (characteristic_iff_comap_eq.mp (CFSG.pCore_characteristic (p := 2) (G := ↥L))) α
    rw [← h] at hn
    exact hn
  have h2 : ¬ orderOf b ∣ Nat.card (CFSG.pCore 2 ↥L) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
    rw [hk]
    exact fun h => hb2 ((Nat.prime_dvd_prime_iff_eq hbp Nat.prime_two).1 (hbp.dvd_of_dvd_pow h))
  have hcen : ∀ y : ↥L, (QuotientGroup.mk' (CFSG.solvableRadical ↥L) y) ∈ K →
      (QuotientGroup.mk (α y * y⁻¹) : Bar2 L) ∈ center (Bar2 L) := by
    intro y hy
    have h1 := hfix _ hy
    change (QuotientGroup.mk (α y) : BarInf L) = QuotientGroup.mk y at h1
    have hmem : α y * y⁻¹ ∈ CFSG.solvableRadical ↥L := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1,
        mul_inv_cancel]
    rw [← uc22p21k_map_solvableRadical_eq_center hq]
    exact mem_map_of_mem _ hmem
  have hA : ∀ z ∈ center (Bar2 L), ∀ x : Bar2 L, z * x * z⁻¹ = x := fun z hz x => by
    rw [← mem_center_iff.1 hz x, mul_inv_cancel_right]
  have hcomm : ∀ (u v c d : Bar2 L), c ∈ center (Bar2 L) → d ∈ center (Bar2 L) →
      ⁅c * u, d * v⁆ = ⁅u, v⁆ := by
    intro u v c d hc hd
    calc ⁅c * u, d * v⁆ = c * (u * (d * v) * u⁻¹) * c⁻¹ * (d * v)⁻¹ := by
          simp only [commutatorElement_def]
          group
      _ = u * (d * v) * u⁻¹ * (d * v)⁻¹ := by rw [hA c hc]
      _ = d * (u * v * u⁻¹ * v⁻¹) * d⁻¹ := by
          rw [show u * (d * v) = d * (u * v) by
            rw [← mul_assoc, mem_center_iff.1 hd u, mul_assoc]]
          group
      _ = ⁅u, v⁆ := by rw [hA d hd, commutatorElement_def]
  have key : ∀ y₁ y₂ : ↥L, QuotientGroup.mk' (CFSG.solvableRadical ↥L) y₁ ∈ K →
      QuotientGroup.mk' (CFSG.solvableRadical ↥L) y₂ ∈ K →
      QuotientGroup.mk' (CFSG.solvableRadical ↥L) ⁅y₁, y₂⁆ ∈
        ((centralizer ({b} : Set G)).subgroupOf L).map
          (QuotientGroup.mk' (CFSG.solvableRadical ↥L)) := by
    intro y₁ y₂ h₁ h₂
    have hfix2 : quotientMap α (CFSG.pCore 2 ↥L) hN2 (QuotientGroup.mk ⁅y₁, y₂⁆) =
        QuotientGroup.mk ⁅y₁, y₂⁆ := by
      have e₁ : (QuotientGroup.mk (α y₁) : Bar2 L) =
          QuotientGroup.mk (α y₁ * y₁⁻¹) * QuotientGroup.mk y₁ := by
        rw [← QuotientGroup.mk_mul, inv_mul_cancel_right]
      have e₂ : (QuotientGroup.mk (α y₂) : Bar2 L) =
          QuotientGroup.mk (α y₂ * y₂⁻¹) * QuotientGroup.mk y₂ := by
        rw [← QuotientGroup.mk_mul, inv_mul_cancel_right]
      rw [quotientMap_mk, map_commutatorElement]
      change QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⁅α y₁, α y₂⁆ =
        QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⁅y₁, y₂⁆
      rw [map_commutatorElement, map_commutatorElement, QuotientGroup.mk'_apply,
        QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, e₁, e₂]
      exact hcomm _ _ _ _ (hcen y₁ h₁) (hcen y₂ h₂)
    obtain ⟨w, hw, hαw⟩ := (fixed_quotient_iff α hα (CFSG.pCore 2 ↥L) hN2 h2 _).1 hfix2
    refine ⟨w, mem_subgroupOf.2 (mem_centralizer_singleton_iff.2 ?_), ?_⟩
    · have h1 := congrArg Subtype.val hαw
      rw [hαy] at h1
      calc (w : G) * b = b * w * b⁻¹ * b := by rw [h1]
        _ = b * w := by group
    · rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      exact CFSG.pCore_le_solvableRadical 2 ↥L (QuotientGroup.eq.1 hw)
  rw [← hK, commutator_le]
  intro k₁ hk₁ k₂ hk₂
  obtain ⟨y₁, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.solvableRadical ↥L) k₁
  obtain ⟨y₂, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.solvableRadical ↥L) k₂
  rw [← map_commutatorElement]
  exact key y₁ y₂ hk₁ hk₂

theorem uc22s2112l3p_card_dvd_of_fixes {L : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 L)) {b : G} (hb : b ∈ normalizer (L : Set G))
    (hbp : (orderOf b).Prime) (hb2 : orderOf b ≠ 2) {K : Subgroup (BarInf L)} (hK : ⁅K, K⁆ = K)
    (hfix : ∀ k ∈ K, inducedBarInfAutHom L ⟨b, hb⟩ k = k) :
    Nat.card K ∣ Nat.card ↥(L ⊓ centralizer ({b} : Set G)) := by
  have h1 := Subgroup.card_dvd_of_le (uc22s2112l3p_le_map_centralizer hq hb hbp hb2 hK hfix)
  have hH : Nat.card ((centralizer ({b} : Set G)).subgroupOf L) =
      Nat.card ↥(L ⊓ centralizer ({b} : Set G)) := by
    rw [← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  exact h1.trans ((Subgroup.card_map_dvd _ _).trans hH.dvd)

end CFSG.LocalAnalysis.UniquenessCase.UC22
