module

public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerMixing

public section

namespace CFSG.RankThree.PartOne.KCSpFull

open CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

variable {r : ℕ} {K : Type} [Field K] {ℓ f p : ℕ} {Ahat : Subgroup (StatedSp r K)}

theorem SpPlaneSetup.exists_ne_one_mem (S : SpPlaneSetup ℓ f p r K Ahat) {M : Subgroup ↥Ahat}
    (hM : Nat.card M = p) : ∃ t : ↥Ahat, t ∈ M ∧ t ≠ 1 := by
  have := S.finite
  have h1 : Nontrivial ↥M :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hM]; exact S.prime_p.one_lt)
  obtain ⟨t, ht⟩ := exists_ne (1 : ↥M)
  exact ⟨t, t.2, fun h' => ht (Subtype.ext h')⟩

theorem SpPlaneSetup.rigidity_of_semilinear [NeZero r] (S : SpPlaneSetup ℓ f p r K Ahat)
    (A : gsp r K) (σ : K ≃+* K) {α : MulAut (StatedProj (StatedSp r K))}
    (hα : α = conjAut r K A * fieldAut r K σ)
    (hcent : ∀ x ∈ Ahat, x ≠ 1 → CentralizesListed α x) : α = 1 := by
  have D := S.decomp
  obtain ⟨M₁, M₂, hM₁, hM₂, hne, hV₁, hV₂⟩ := D.two_active
  obtain ⟨t₁, ht₁, ht₁1⟩ := S.exists_ne_one_mem hM₁
  have ht₁1' : (t₁ : StatedSp r K) ≠ 1 := fun h => ht₁1 (Subtype.ext h)
  have hσ : σ = RingEquiv.refl K :=
    (S.line_scalar D hM₁ hV₁ t₁.2 ht₁ ht₁1' A σ hα (hcent _ t₁.2 ht₁1')).1
  subst hσ
  have hline : ∀ M : Subgroup ↥Ahat, Nat.card M = p → spLineSpace M ≠ ⊥ →
      ∃ l : K, ∀ u ∈ spPlaneFix Ahat ⊔ spLineSpace M,
        semilinMap A (RingEquiv.refl K) u = l • u := by
    intro M hM hVM
    obtain ⟨t, ht, ht1⟩ := S.exists_ne_one_mem hM
    have ht1' : (t : StatedSp r K) ≠ 1 := fun h => ht1 (Subtype.ext h)
    obtain ⟨-, l, hl, -⟩ := S.line_scalar D hM hVM t.2 ht ht1' A (RingEquiv.refl K) hα
      (hcent _ t.2 ht1')
    refine ⟨l, fun u hu => hl u ?_⟩
    rw [D.ker_eq_sup hM t.2 ht ht1']
    exact hu
  obtain ⟨l, hl⟩ := S.exists_global_scalar D A hα hcent hline
  rw [hα]
  exact alpha_eq_one_of_scalar A hl

end CFSG.RankThree.PartOne.KCSpFull
