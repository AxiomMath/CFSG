module

public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticPerfectCoverOuterPrime

public section

namespace CFSG.RankThree.PartOne.OutStructure

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.Assembly.LowTwoRank

theorem outPNice_StatedSp {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ} (hr : 3 ≤ r)
    {p : ℕ} (hp : p.Prime) : OutPNice p (StatedProj (StatedSp r K)) := by
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
  have hDle : spLinearAutGroup r K ≤
      CFSG.ComponentClassification.OuterAutomorphisms.inner (StatedProj (StatedSp r K)) := by
    intro δ hδ
    obtain ⟨A, rfl⟩ := (mem_spLinearAutGroup_iff).mp hδ
    exact conjAut_mem_inner_of_isSquare
      (FiniteField.isSquare_of_char_two (ringChar.eq K 2) (multiplier r K A : K))
  have hgE : ∀ α : MulAut (StatedProj (StatedSp r K)), ∃ k : ℤ, g ^ k * α ∈ spLinearAutGroup r K :=
    fun α => hg α (hgenTop ▸ Subgroup.mem_top α)
  exact outPNice_of_tower hp g (E := ⊤) hID (fun δ hδ _ _ => hDle hδ) (fun α _ => trivial)
    (fun γ α _ => commutator_mem_of_cyclic_quotient g hgE γ α) (fun α _ => hgE α)

theorem outPNice_PSp_ge_three {p : ℕ} (hp : p.Prime) {X : Type} [Group X] {r m : ℕ}
    (hr : 3 ≤ r) (h : StatedClassicalModel X .PSp r 2 m) : OutPNice p X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have hchar : CharP K 2 := charP_of_card_eq_prime_pow (f := m) (by
    rw [← Nat.card_eq_fintype_card, hK])
  exact OutPNice.of_mulEquiv e (outPNice_StatedSp hr hp)

end CFSG.RankThree.PartOne.OutStructure
