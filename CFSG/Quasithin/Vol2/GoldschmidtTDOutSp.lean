module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticPerfectCoverOuterPrime
public import CFSG.Assembly.GL83LieDefs
public import CFSG.Quasithin.Background.PSL2TwoNilpotent

public section

namespace CFSG.Quasithin.H13.OutTwoNilp

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)
open CFSG.Quasithin.H13.Ch838 (TwoNilpotent)

theorem twoNilpotent_outer_symplectic_two {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    [Finite (StatedProj (StatedSp 2 K))] (hK : Nat.card K = 2 ^ f) :
    TwoNilpotent (Outer (StatedProj (StatedSp 2 K))) := by
  set P := StatedProj (StatedSp 2 K) with hP
  set π : MulAut P →* Outer P := QuotientGroup.mk' (inner P) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  obtain ⟨-, -, -, -, ⟨g, hgE, hg⟩, -⟩ :=
    standard_outer_quotient (K := K) (r := 2) (by norm_num)
  have hDI : spLinearAutGroup 2 K ≤ inner P := by
    have h := relIndex_inner_spLinearAutGroup_dvd (r := 2) (K := K) Nat.prime_two hf hK
    have hgcd : Nat.gcd 2 (2 ^ f - 1) = 1 := by
      have hpos : 1 ≤ 2 ^ f := Nat.one_le_pow _ _ (by norm_num)
      obtain ⟨k, hk⟩ : Even (2 ^ f) := Nat.even_pow.mpr ⟨even_two, by omega⟩
      exact Nat.coprime_two_left.mpr ⟨k - 1, by omega⟩
    rw [hgcd] at h
    exact Subgroup.relIndex_eq_one.mp (Nat.dvd_one.mp h)
  have hEn : (spSemilinearAutGroup 2 K).Normal := by
    have h := index_spSemilinearAutGroup_dvd_two (K := K) (r := 2) le_rfl
    rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h2
    · rw [Subgroup.index_eq_one.mp h1]
      infer_instance
    · exact Subgroup.normal_of_index_eq_two h2
  have hCn : ((spSemilinearAutGroup 2 K).map π).Normal := hEn.map π hπs
  refine TwoNilpotent.of_normal_comm ((spSemilinearAutGroup 2 K).map π) ?_ fun q => ?_
  ·
    have key : ∀ a ∈ (spSemilinearAutGroup 2 K).map π, ∃ m : ℤ, a = π g ^ m := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨k, hk⟩ := hg x hx
      refine ⟨-k, ?_⟩
      have h1 : π (g ^ k * x) = 1 := by
        have hx' : g ^ k * x ∈ inner P := hDI hk
        exact (QuotientGroup.eq_one_iff _).mpr hx'
      rw [map_mul, map_zpow] at h1
      rw [zpow_neg]
      exact eq_inv_of_mul_eq_one_right h1
    intro a ha b hb
    obtain ⟨m, rfl⟩ := key a ha
    obtain ⟨n, rfl⟩ := key b hb
    exact (Commute.zpow_zpow_self (π g) m n).eq
  · obtain ⟨a, rfl⟩ := hπs q
    exact ⟨1, ⟨a ^ 2, sq_mem_spSemilinearAutGroup (by norm_num) a, by simp⟩⟩

theorem twoNilpotent_outer_of_psp_two {S : Type} [Group S] [Finite S] {f : ℕ} (hf : 2 ≤ f)
    (h : StatedClassicalModel S .PSp 2 2 f) : TwoNilpotent (Outer S) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Finite (StatedProj (StatedSp 2 K)) := Finite.of_equiv S e.toEquiv
  exact TwoNilpotent.of_mulEquiv (equivalence e).symm
    (twoNilpotent_outer_symplectic_two (by omega) hK)

end CFSG.Quasithin.H13.OutTwoNilp
