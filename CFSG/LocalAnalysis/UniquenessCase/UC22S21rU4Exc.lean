module

import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22s21ru4e_shape_conj {M L K : Subgroup G} (hK : K ∈ conjSetOf M L) {n : ℕ}
    (hshape : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) :
    IsL2 (Bar2 K) n ∨ IsSz (Bar2 K) n := by
  obtain ⟨g, -, rfl⟩ := hK
  obtain ⟨e⟩ := uc22p20d_bar2_conj g L
  exact hshape.imp (fun h => CFSG.Blueprint.LieModel.of_mulEquiv e h)
    (fun h => CFSG.Blueprint.LieModel.of_mulEquiv e h)

theorem uc22s21ru4e_exists_second_member {M : Subgroup G} {L : Subgroup G}
    (h2 : (conjSetOf M L).ncard = 2) (hL : L ∈ calC M) :
    ∃ K : Subgroup G, K ≠ L ∧ conjSetOf M L = {L, K} ∧ K ∈ calC M := by
  classical
  obtain ⟨K1, K2, h12, hset2⟩ := Set.ncard_eq_two.mp h2
  let K : Subgroup G := if K1 = L then K2 else K1
  have hKne : K ≠ L := by
    dsimp [K]
    by_cases h : K1 = L
    · simp [h]
      intro hK2L
      exact h12 (h.trans hK2L.symm)
    · simp [h]
  have hLmem : L ∈ conjSetOf M L := ⟨1, M.one_mem, by ext x; simp⟩
  have hL12 : L ∈ ({K1, K2} : Set (Subgroup G)) := by
    rw [← hset2]
    exact hLmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hL12
  have hset2' : conjSetOf M L = {L, K} := by
    rw [hset2]
    by_cases h : K1 = L
    · ext X
      simp [K, h]
    · have hK2L : K2 = L := by
        rcases hL12 with h1 | h2
        · exact absurd h1.symm h
        · exact h2.symm
      ext X
      simp [K, h, hK2L]
      tauto
  have hKmem : K ∈ conjSetOf M L := by
    rw [hset2']
    simp
  exact ⟨K, hKne, hset2', uc22p2214_calC_of_mem_conjSetOf hL hKmem⟩

theorem uc22s21ru4e_conjClosure_eq_sup_mul {M L K : Subgroup G}
    (hset : conjSetOf M L = {L, K}) (hL : L ∈ calC M) (hKcalC : K ∈ calC M) (hKne : K ≠ L) :
    conjClosure M L = L ⊔ K ∧ (conjClosure M L : Set G) = (L : Set G) * (K : Set G) := by
  have hclosure : conjClosure M L = L ⊔ K := by
    unfold conjClosure
    rw [hset]
    refine le_antisymm ?_ ?_
    · refine iSup_le fun X => iSup_le fun hX => ?_
      rcases hX with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
    · exact sup_le (le_iSup₂_of_le L (by simp) le_rfl)
        (le_iSup₂_of_le K (by simp) le_rfl)
  refine ⟨hclosure, ?_⟩
  rw [hclosure]
  exact Subgroup.coe_mul_of_left_le_normalizer_right L K
    (uc22p22u_calC_normalizes hKcalC hL hKne)

theorem uc22s21ru4e_hyp8100 {D : Data G} {L K : Subgroup G} {n r p : ℕ} {A : Subgroup G}
    (hL : L ∈ calC D.M) (hKC : K ∈ calC D.M) (hKne : K ≠ L)
    (hLshape : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) (hKshape : IsL2 (Bar2 K) n ∨ IsSz (Bar2 K) n)
    (hprod : (conjClosure D.M L : Set G) = (L : Set G) * (K : Set G))
    (hrPrime : r.Prime) (hrdvdn : r ∣ 2 ^ n - 1) (hp : p ∈ D.sig)
    (hAcard : Nat.card A = r) (hAL : A ≤ L) :
    F08.Hyp8100 D ![L, K] ![n, n] r p A (conjClosure D.M L) := by
  have hXnorm : D.M ≤ normalizer (conjClosure D.M L : Set G) :=
    (uc22p22u_conjClosure_isProd le_rfl Subgroup.le_normalizer hL).2.1
  refine ⟨?_, ?_, ?_, hrPrime, ?_, hp, hAcard, Or.inl ?_, ?_, hXnorm⟩
  · intro i
    fin_cases i
    · exact hL
    · exact hKC
  · exact Ne.symm hKne
  · intro i
    fin_cases i
    · exact hLshape
    · exact hKshape
  · simpa [Nat.gcd_self] using hrdvdn
  · simpa using hAL
  · simpa using hprod

theorem uc22s21ru4e_not_isPowTwo_three : ¬ IsPowTwo 3 := by
  rintro ⟨k, hk⟩
  rcases k with _ | k
  · norm_num at hk
  · have h2 : 2 ∣ 3 := by
      rw [hk, pow_succ]
      exact dvd_mul_left 2 _
    omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
