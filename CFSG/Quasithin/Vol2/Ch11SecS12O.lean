module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aL3C
public import CFSG.Quasithin.Vol2.Ch11SecQ9aL3G

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Std

variable {K : Type} [Field K] [Finite K]

theorem parab34_zero_ne_one [CharP K 2] (hK : Nat.card K = 4) : parab34 K 0 ≠ parab34 K 1 := by
  intro heq
  obtain ⟨P₁, P₂, hne, h₁t, h₂t, hc₁, hc₂, -, hS₁, hS₂, -⟩ :=
    factL34Parab_holds _ (isPSL_projectiveSL hK) _ isSylowTwoOf_projU
  have key : ∀ P : Subgroup (projectiveSL 3 K), P ≠ ⊤ → quasithinIsCComponent P P →
      projUnitriangular 3 K ≤ Subgroup.normalizer (P : Set (projectiveSL 3 K)) →
      P = parab34 K 0 := by
    intro P hPt hc hS
    rcases classify_std hK P hc.1 hc.2.1 hS with h | h | h
    · exact h
    · exact h.trans heq.symm
    · exact absurd h hPt
  exact hne ((key P₁ h₁t hc₁ hS₁).trans (key P₂ h₂t hc₂ hS₂).symm)

end Std

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem Ptheta_perfect (hF : Nat.card F = 4) (j : Fin 2) :
    ⁅Ptheta F j, Ptheta F j⁆ = Ptheta F j := by
  rw [← Subgroup.map_commutator, parab34_perfect hF j]

theorem Ptheta_ne_bot (hF : Nat.card F = 4) (j : Fin 2) : Ptheta F j ≠ ⊥ := by
  rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ thetaP_injective]
  intro h
  have h1 := (parab34_structure hF j).1
  rw [dInf_parab34 hF j, h, Subgroup.card_bot] at h1
  norm_num at h1

theorem Ptheta_ne_commutator (hF : Nat.card F = 4) (j : Fin 2) :
    Ptheta F j ≠ ⁅(⊤ : Subgroup (PGL3 F)), (⊤ : Subgroup (PGL3 F))⁆ := by
  rw [← range_thetaP_eq hF, MonoidHom.range_eq_map]
  intro h
  exact (parab34_covBy hF j).lt.ne (Subgroup.map_injective thetaP_injective h)

theorem eq_Ptheta_of_le (hF : Nat.card F = 4) {j : Fin 2} {Q : Subgroup (PGL3 F)}
    (hQp : ⁅Q, Q⁆ = Q) (hS : S0P F ≤ Subgroup.normalizer (Q : Set (PGL3 F)))
    (hPQ : Ptheta F j ≤ Q) (hQc : Q ≠ ⁅(⊤ : Subgroup (PGL3 F)), (⊤ : Subgroup (PGL3 F))⁆) :
    Q = Ptheta F j := by
  have hQ1 : Q ≠ ⊥ := fun h => Ptheta_ne_bot hF j (le_bot_iff.mp (h ▸ hPQ))
  have hle : ∀ k : Fin 2, Ptheta F j ≤ Ptheta F k → k = j := by
    intro k hjk
    by_contra hkj
    have hpq : parab34 F j ≤ parab34 F k :=
      (Subgroup.map_le_map_iff_of_injective thetaP_injective).mp hjk
    have heq : parab34 F j = parab34 F k :=
      (((parab34_covBy hF j).eq_or_eq hpq le_top).resolve_right (parab34_covBy hF k).lt.ne).symm
    fin_cases j <;> fin_cases k
    · exact hkj rfl
    · exact parab34_zero_ne_one hF heq
    · exact parab34_zero_ne_one hF heq.symm
    · exact hkj rfl
  rcases classify_pgl hF hQ1 hQp hQc hS with h | h
  · rw [h] at hPQ ⊢
    rw [hle 0 hPQ]
  · rw [h] at hPQ ⊢
    rw [hle 1 hPQ]

theorem sup_normalizer_S0P (hF : Nat.card F = 4) (hS0 : QuasithinUnique.IsSylowTwoOf (S0P F) ⊤) :
    Subgroup.normalizer (S0P F : Set (PGL3 F)) ⊔ (thetaP F).range = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ¬ 2 ∣ (S0P F).index := by
    have := hS0.2.2
    rwa [show ((S0P F).subgroupOf ⊤).index = (S0P F).index from
      Subgroup.relIndex_top_right _] at this
  let P : Sylow 2 (PGL3 F) := hS0.2.1.toSylow hidx
  have hP : (P : Subgroup (PGL3 F)) ≤ (thetaP F).range := by
    rintro _ ⟨u, -, rfl⟩
    exact ⟨u, rfl⟩
  have hn : ((thetaP F).range).Normal := by
    rw [range_thetaP_eq hF]
    exact Subgroup.commutator_normal ⊤ ⊤
  exact Sylow.normalizer_sup_eq_top' P hP

theorem normalizer_Ptheta_ne_top (hF : Nat.card F = 4) (j : Fin 2) :
    Subgroup.normalizer (Ptheta F j : Set (PGL3 F)) ≠ ⊤ := by
  intro htop
  have hsimp := isSimpleGroup_projectiveSL_four hF
  have hn : (parab34 F j).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hg : thetaP F g ∈ Subgroup.normalizer (Ptheta F j : Set (PGL3 F)) :=
      htop ▸ Subgroup.mem_top _
    have h1 := (map_mem_normalizer_iff (thetaP F) thetaP_injective).mp hg
    exact (Subgroup.mem_normalizer_iff.mp h1 n).mp hn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (parab34 F j) with h | h
  · exact Ptheta_ne_bot hF j (by
      show (parab34 F j).map (thetaP F) = ⊥
      rw [h, Subgroup.map_bot])
  · exact (parab34_covBy hF j).lt.ne h

variable (hS0 : QuasithinUnique.IsSylowTwoOf (S0P F) ⊤)
include hS0

theorem not_range_le_normalizer (hF : Nat.card F = 4) (j : Fin 2) {Q : Subgroup (PGL3 F)}
    (hQ : Subgroup.normalizer (Ptheta F j : Set (PGL3 F)) ≤ Q) (hQt : Q ≠ ⊤) :
    ¬ (thetaP F).range ≤ Q := by
  intro hle
  apply hQt
  rw [eq_top_iff, ← sup_normalizer_S0P hF hS0]
  exact sup_le ((normalizer_S0P_le j).trans hQ) hle

theorem perfectCore_normalizer_Ptheta (hF : Nat.card F = 4) (j : Fin 2) :
    perfectCore (Subgroup.normalizer (Ptheta F j : Set (PGL3 F))) = Ptheta F j := by
  set N := Subgroup.normalizer (Ptheta F j : Set (PGL3 F)) with hN
  have hPN : Ptheta F j ≤ N := Subgroup.le_normalizer
  refine eq_Ptheta_of_le hF (perfectCore_perfect N) ?_
    (le_perfectCore_of_perfect hPN (Ptheta_perfect hF j)) fun h => ?_
  · exact ((Subgroup.le_normalizer.trans (normalizer_S0P_le j)).trans
      Subgroup.le_normalizer).trans (normalizer_le_normalizer_perfectCore N)
  · apply not_range_le_normalizer hS0 hF j le_rfl (normalizer_Ptheta_ne_top hF j)
    rw [range_thetaP_eq hF, ← h]
    exact perfectCore_le N

theorem isMaxParabolic2_normalizer_Ptheta (hF : Nat.card F = 4) (j : Fin 2) :
    IsMaxParabolic2 ⊤ (Subgroup.normalizer (Ptheta F j : Set (PGL3 F))) := by
  refine ⟨⟨le_top, S0P F, hS0, inf_le_right.trans (normalizer_S0P_le j)⟩,
    normalizer_Ptheta_ne_top hF j, fun Q _ hQt hNQ => le_antisymm ?_ hNQ⟩
  have hPQ : Ptheta F j ≤ Q := Subgroup.le_normalizer.trans hNQ
  have hS0Q : S0P F ≤ Q := (Subgroup.le_normalizer.trans (normalizer_S0P_le j)).trans hNQ
  have h1 : perfectCore Q = Ptheta F j := by
    refine eq_Ptheta_of_le hF (perfectCore_perfect Q)
      ((hS0Q.trans Subgroup.le_normalizer).trans (normalizer_le_normalizer_perfectCore Q))
      (le_perfectCore_of_perfect hPQ (Ptheta_perfect hF j)) fun h => ?_
    apply not_range_le_normalizer hS0 hF j hNQ hQt
    rw [range_thetaP_eq hF, ← h]
    exact perfectCore_le Q
  rw [← h1]
  exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore Q)

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
