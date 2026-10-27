module

public import CFSG.LocalAnalysis.StandardType.GGQTwoChartDefs
import CFSG.LocalAnalysis.StandardType.GGQTwoSU34
import CFSG.LocalAnalysis.StandardType.GGQTwoSU34Comm

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open scoped Pointwise Matrix
variable {G : Type} [Group G] [Finite G]
variable {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {m : ℕ}

theorem qTwoChartTwoThree_oTwoPrime_eq_self {Y : Subgroup G} (hs : IsSolvable ↥Y)
    (hi : ∃ k : ℕ, (commutator ↥Y).index = 2 ^ k) : qTwoOTwoPrime Y = Y := by
  haveI : Group.IsSolvable ↥Y := hs
  let S : Set G := {y : G | y ∈ Y ∧ ∃ k : ℕ, y ^ (2 ^ k) = 1}
  let N : Subgroup G := Subgroup.closure S
  have hN : qTwoOTwoPrime Y = N := rfl
  have hNY : N ≤ Y := (Subgroup.closure_le Y).mpr fun _ hx => hx.1
  let K : Subgroup ↥Y := N.subgroupOf Y
  have hKnormal : K.Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNY]
    rw [Subgroup.le_normalizer_closure_iff]
    intro y hy g hg
    exact Subgroup.subset_closure
      ⟨Y.mul_mem (Y.mul_mem hy hg.1) (Y.inv_mem hy),
        ⟨hg.2.choose, by simp [conj_pow, hg.2.choose_spec]⟩⟩
  have hodd : ¬ 2 ∣ K.index := by
    let P : Sylow 2 ↥Y := default
    have hPle : (P : Subgroup ↥Y) ≤ K := by
      intro x hx
      rw [Subgroup.mem_subgroupOf]
      refine Subgroup.subset_closure ⟨x.2, ?_⟩
      obtain ⟨j, hj⟩ := isPGroup_iff_pow_pow_eq_one.mp P.isPGroup' ⟨x, hx⟩
      exact ⟨j, by simpa using congrArg (fun z : ↥(P : Subgroup ↥Y) => ((z : ↥Y) : G)) hj⟩
    have hPnot : ¬ 2 ∣ (P : Subgroup ↥Y).index := Sylow.not_dvd_index P
    exact fun h => hPnot (h.trans (Subgroup.index_dvd_of_le hPle))
  have hcup : commutator ↥Y ⊔ K = ⊤ := by
    obtain ⟨k, hk⟩ := hi
    have hcop : Nat.Coprime (2 ^ k) K.index :=
      Nat.Coprime.pow_left k (Nat.prime_two.coprime_iff_not_dvd.mpr hodd)
    rw [← Subgroup.index_eq_one]
    refine Nat.eq_one_of_dvd_coprimes hcop ?_ ?_
    · rw [← hk]
      exact Subgroup.index_dvd_of_le le_sup_left
    · exact Subgroup.index_dvd_of_le le_sup_right
  have hKtop : K = ⊤ := by
    by_contra hne
    haveI : K.Normal := hKnormal
    haveI : Nontrivial (↥Y ⧸ K) := QuotientGroup.nontrivial_iff.mpr hne
    have hcomm : (commutator ↥Y).map (QuotientGroup.mk' K) = commutator (↥Y ⧸ K) := by
      rw [map_commutator_eq,
        MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective K)]
      rfl
    have hKmap : K.map (QuotientGroup.mk' K) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    have htop : (commutator ↥Y).map (QuotientGroup.mk' K) = ⊤ := by
      have h1 : (commutator ↥Y ⊔ K).map (QuotientGroup.mk' K) = ⊤ := by
        rw [hcup, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective K)]
      rwa [Subgroup.map_sup, hKmap, sup_bot_eq] at h1
    have hperfect : Group.IsPerfect (↥Y ⧸ K) := by
      rw [Group.isPerfect_def, ← hcomm]
      exact htop
    haveI : Group.IsPerfect (↥Y ⧸ K) := hperfect
    exact (Group.IsPerfect.not_isSolvable (↥Y ⧸ K))
      (Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective K))
  have hNYeq : N = Y := by
    refine le_antisymm hNY fun x hx => ?_
    have hxK : (⟨x, hx⟩ : ↥Y) ∈ K := by rw [hKtop]; trivial
    exact Subgroup.mem_subgroupOf.mp hxK
  exact hN.trans hNYeq

theorem qTwoChartTwoThree_oTwoPrime_coordBlockSU (hF0 : Nat.card F0 = 4) {J : Finset (Fin m)}
    (h2 : 2 ≤ J.card) (h3 : J.card ≤ 3) :
    qTwoOTwoPrime (coordBlockSU F0 2 1 J) = coordBlockSU F0 2 1 J := by
  exact qTwoChartTwoThree_oTwoPrime_eq_self
    (isSolvable_coordBlockSU_of_card_le_three hF0 h3)
    (index_commutator_coordBlockSU_isPow_two hF0 h2 h3)

end CFSG.StandardType.QTwo

end
