module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticPerfectCoverOuterPrime
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.RankThree.PartOne.OutStructure

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.Assembly.LowTwoRank

theorem outPNice_StatedSp_odd {K : Type} [Field K] [Finite K] {r : ℕ} (hr : 3 ≤ r) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : OutPNice p (StatedProj (StatedSp r K)) := by
  have : NeZero r := ⟨by omega⟩
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨hgenTop, -⟩ := automorphism_generation (K := K) hr
  obtain ⟨hID, -, hDn, -, ⟨g, -, hg⟩, -⟩ := standard_outer_quotient (K := K) (r := r) (by omega)
  have hDnorm : (spLinearAutGroup r K).Normal := by
    refine ⟨fun d hd γ => ?_⟩
    have hγ : γ ∈ spSemilinearAutGroup r K := hgenTop ▸ Subgroup.mem_top γ
    have hd' : d ∈ spSemilinearAutGroup r K := hgenTop ▸ Subgroup.mem_top d
    have := hDn.conj_mem ⟨d, hd'⟩ (mem_subgroupOf.mpr hd) ⟨γ, hγ⟩
    exact mem_subgroupOf.mp this
  obtain ⟨m, hℓ, hcard⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hdvd := relIndex_inner_spLinearAutGroup_dvd (r := r) hℓ m.pos hK
  have hD2 : ∀ δ ∈ spLinearAutGroup r K, ∀ k : ℕ,
      δ ^ (p ^ k) ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
        (StatedProj (StatedSp r K)) →
      δ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (StatedProj (StatedSp r K)) := by
    intro δ hδ k hk
    set D := spLinearAutGroup r K with hD
    set I := CFSG.ComponentClassification.OuterAutomorphisms.inner
      (StatedProj (StatedSp r K)) with hI
    set x : D ⧸ I.subgroupOf D := QuotientGroup.mk (⟨δ, hδ⟩ : D) with hx
    have hxk : x ^ (p ^ k) = 1 := by
      rw [hx, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hk
    have hcard2 : Nat.card (D ⧸ I.subgroupOf D) ∣ 2 := by
      have h1 : Nat.card (D ⧸ I.subgroupOf D) = I.relIndex D := (Subgroup.index_eq_card _).symm
      rw [h1]
      exact hdvd.trans (Nat.gcd_dvd_left 2 _)
    have hdvd1 : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one hxk
    have hdvd2 : orderOf x ∣ 2 := (orderOf_dvd_natCard x).trans hcard2
    have hcop : Nat.Coprime (p ^ k) 2 :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun h =>
        hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h))
    have hx1 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
    have : x = 1 := orderOf_eq_one_iff.mp hx1
    have hmem := (QuotientGroup.eq_one_iff (⟨δ, hδ⟩ : D)).mp this
    exact Subgroup.mem_subgroupOf.mp hmem
  have hgE : ∀ α : MulAut (StatedProj (StatedSp r K)), ∃ k : ℤ, g ^ k * α ∈ spLinearAutGroup r K :=
    fun α => hg α (hgenTop ▸ Subgroup.mem_top α)
  exact outPNice_of_tower hp g (E := ⊤) hID hD2 (fun α _ => trivial)
    (fun γ α _ => commutator_mem_of_cyclic_quotient g hgE γ α) (fun α _ => hgE α)

theorem outPNice_PSp_ge_three_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Type} [Group X]
    {r ℓ m : ℕ} (hr : 3 ≤ r) (h : StatedClassicalModel X .PSp r ℓ m) : OutPNice p X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  exact OutPNice.of_mulEquiv e (outPNice_StatedSp_odd hr hp hp2)

end CFSG.RankThree.PartOne.OutStructure
