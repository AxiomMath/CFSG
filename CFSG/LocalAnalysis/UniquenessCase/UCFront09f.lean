module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09e
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_pCoreOf_of_isAlt_bar2 {L X B : Subgroup G} (hXL : X ≤ L)
    (hcov : L = X ⊔ pCoreOf 2 L) (hA5 : IsAlt (Bar2 L) 5) (hBL : B ≤ L)
    (hB3 : ¬ 3 ∣ Nat.card ↥B) (hXB : X ≤ normalizer (B : Set G)) : B ≤ pCoreOf 2 L := by
  have h60 := card_bar2_of_isAlt hA5
  obtain ⟨e⟩ := hA5
  haveI : IsSimpleGroup (Bar2 L) := e.isSimpleGroup
  have hφ := surjective_bar2 hXL hcov
  have hJ : ((B.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨x, rfl⟩ := hφ g
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.1 hn
    refine Subgroup.mem_map.2 ⟨Subgroup.inclusion hXL x * j * (Subgroup.inclusion hXL x)⁻¹, ?_,
      by simp⟩
    rw [Subgroup.mem_subgroupOf] at hj ⊢
    simpa using (Subgroup.mem_normalizer_iff.1 (hXB x.2) (j : G)).1 hj
  rcases hJ.eq_bot_or_eq_top with h | h
  · intro y hy
    have h1 := Subgroup.mem_map_of_mem (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
      (Subgroup.mem_subgroupOf.2 hy : (⟨y, hBL hy⟩ : ↥L) ∈ B.subgroupOf L)
    rw [h, Subgroup.mem_bot, ← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at h1
    exact (CFSG.mem_openPCoreOf_iff _).2 h1
  · exfalso
    have h1 : Nat.card (Bar2 L) ∣ Nat.card (B.subgroupOf L) := by
      rw [← Subgroup.card_top (G := Bar2 L), ← h]
      exact Subgroup.card_map_dvd _ _
    have h2 : Nat.card (B.subgroupOf L) ∣ Nat.card B := by
      rw [← Subgroup.card_map_of_injective L.subtype_injective, Subgroup.subgroupOf_map_subtype]
      exact Subgroup.card_dvd_of_le inf_le_left
    rw [h60] at h1
    exact hB3 (((show (3 : ℕ) ∣ 60 by norm_num).trans h1).trans h2)

theorem commutator_le_pCoreOf_of_mem_inv9' {M L X A : Subgroup G}
    (hLN : M ≤ normalizer (L : Set G)) (hXL : X ≤ L) (hcov : L = X ⊔ pCoreOf 2 L)
    (hA5 : IsAlt (Bar2 L) 5) (hA : A ∈ Inv9' M X 3) : ⁅A, X⁆ ≤ pCoreOf 2 A := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hAM, hA3, hXA⟩ := hA
  have hAL : A ≤ normalizer (L : Set G) := hAM.trans hLN
  have hc : ⁅A, X⁆ ≤ A ⊓ L := by
    rw [Subgroup.commutator_le]
    intro a ha x hx
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have h : ⁅a, x⁆ = a * (x * a⁻¹ * x⁻¹) := by simp only [commutatorElement_def, mul_assoc]
      rw [h]
      exact A.mul_mem ha ((Subgroup.mem_normalizer_iff.1 (hXA hx) a⁻¹).1 (A.inv_mem ha))
    · rw [commutatorElement_def]
      exact L.mul_mem ((Subgroup.mem_normalizer_iff.1 (hAL ha) x).1 (hXL hx))
        (L.inv_mem (hXL hx))
  have hAO : A ⊓ L ≤ pCoreOf 2 L :=
    le_pCoreOf_of_isAlt_bar2 hXL hcov hA5 inf_le_right
      (fun h => hA3 (h.trans (Subgroup.card_dvd_of_le inf_le_left)))
      ((le_inf hXA (hXL.trans Subgroup.le_normalizer)).trans
        Subgroup.inf_normalizer_le_normalizer_inf)
  have hP : A ⊓ pCoreOf 2 L ≤ pCoreOf 2 A :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      ((le_inf Subgroup.le_normalizer
        (hAL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))).trans
          Subgroup.inf_normalizer_le_normalizer_inf)
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le inf_le_right)
  exact hc.trans ((le_inf inf_le_left hAO).trans hP)

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
