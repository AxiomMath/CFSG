module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen4Abelian

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

namespace Hyp141

variable {D : Data G} {L₁ L₂ X : Subgroup G}

theorem le_of_eq_sup_inf_normalizer (h : Hyp141 D L₁ L₂ X) (hSg : UC6S846.SigmaStd D)
    (h1421 : Thm1421 D) (h1422 : Thm1422 D) (hperm : PermutesPair D.M L₁ L₂)
    {H I : Subgroup G} (hXH : X ≤ H) (hIH : I ≤ H) (hHI : H ≤ normalizer (I : Set G))
    (hI3 : ¬ 3 ∣ Nat.card I) (hHeq : H = I ⊔ (H ⊓ normalizer (X : Set G)))
    (hodd : Odd (D.M.relIndex H))
    (hrank : ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ V : Subgroup G, V ≤ H → IsElemAbelian q V →
      Nat.card V ≤ q ^ 3)
    (hAut : ∀ n ∈ (L₁ ⊔ L₂) ⊓ normalizer (X : Set G), ∃ m ∈ H ⊓ normalizer (X : Set G),
      ∀ x ∈ X, m * x * m⁻¹ = n * x * n⁻¹) :
    H ≤ D.M := by
  by_contra hHM
  have hX3 : IsPGroup 3 X := h.sylow.isPGroup
  have hNX : H ⊓ normalizer (X : Set G) ≤ D.M := inf_le_right.trans (h.normalizer_X_le h1421)
  have hIM : ¬ I ≤ D.M := fun hIM => hHM (hHeq.le.trans (sup_le hIM hNX))
  have hXI : X ≤ normalizer (I : Set G) := hXH.trans hHI
  obtain ⟨q, hq, hq2, hq3, Q, hQ, hXQ, hQM⟩ :=
    exists_sylow_not_le hIH hHI hX3 hI3 hXI hodd hIM
  have hQp : IsPGroup q Q := hQ.isPGroup
  have hQH : Q ≤ H := hQ.le.trans hIH
  have hQb : Q ⊓ D.M = ⊥ := h.inf_eq_bot h1422 hSg hperm hq hq2 hq3 hQp hQM
  have hQ1 : Q ≠ ⊥ := fun h0 => hQM (h0 ▸ bot_le)
  obtain ⟨V, hVQ, hVe, hV1, hVN⟩ := exists_elemAbelian_char hq hQp hQ1
  have hVcard : Nat.card V ≤ q ^ 3 := hrank q hq hq2 V (hVQ.trans hQH) hVe
  have hXV : (X ⊓ L₁) ⊔ (X ⊓ L₂) ≤ normalizer (V : Set G) := by
    rw [← h.X_eq_sup]
    exact fun x hx => hVN x (hXQ hx)
  have hk : ∀ s₁ s₂ : Bool, ∃ n ∈ normalizer (V : Set G),
      (∀ x ∈ X ⊓ L₁, n * x * n⁻¹ = if s₁ then x⁻¹ else x) ∧
      (∀ x ∈ X ⊓ L₂, n * x * n⁻¹ = if s₂ then x⁻¹ else x) := by
    intro s₁ s₂
    obtain ⟨n, hn, hn₁, hn₂⟩ := h.exists_inversion s₁ s₂
    obtain ⟨m, hm, hmx⟩ := hAut n hn
    obtain ⟨m', hm', hm'x⟩ := exists_mem_normalizer_acts_as hq hX3 hI3 hIH hHI hQ hXQ hm hXI
    refine ⟨m', hVN m' hm'.1.2, fun x hx => ?_, fun x hx => ?_⟩
    · rw [hm'x x hx.1, hmx x hx.1]
      exact hn₁ x hx
    · rw [hm'x x hx.1, hmx x hx.1]
      exact hn₂ x hx
  have hXab : IsElemAbelian 3 ((X ⊓ L₁) ⊔ (X ⊓ L₂) : Subgroup G) := by
    rw [← h.X_eq_sup]
    exact h.isElemAbelian_X
  have hX9 : Nat.card ((X ⊓ L₁) ⊔ (X ⊓ L₂) : Subgroup G) = 9 := by
    rw [← h.X_eq_sup]
    exact h.card_X
  have hCQ : ∀ L ∈ ({L₁, L₂} : Set (Subgroup G)),
      V ⊓ centralizer ((X ⊓ L : Subgroup G) : Set G) = ⊥ := by
    intro L hL
    rw [eq_bot_iff_forall]
    intro v hv
    have hvN : v ∈ normalizer ((X ⊓ L : Subgroup G) : Set G) :=
      Subgroup.centralizer_le_normalizer _ hv.2
    have hvM : v ∈ D.M := h.normalizer_inf_le h1421 hL hvN
    have : v ∈ Q ⊓ D.M := ⟨hVQ hv.1, hvM⟩
    rw [hQb] at this
    exact Subgroup.mem_bot.1 this
  rcases abelian_338 hq hq3 hVe hV1 hVcard h.card_inf_left h.card_inf_right hXab hX9 hXV hk with
    h1 | h2
  · exact h1 (hCQ L₁ (Set.mem_insert _ _))
  · exact h2 (hCQ L₂ (Set.mem_insert_of_mem _ rfl))

end Hyp141

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
