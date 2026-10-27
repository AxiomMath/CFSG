module

public import CFSG.LocalAnalysis.StandardType.GGSixStepOneInputs
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Input

@[expose] def GGLinearTorusComponentInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (t : StatedLieTag) (n f : ℕ)
    (ψ : (ggU t n f).K →* G) (G₀ : Subgroup G), GGPresentsG0 G₀ (ggU t n f).D t n f ψ →
    p.Prime → GGSixLinearCase p t n f →
    ∀ E : Subgroup G, IsElemAbelian p E → Nat.card E = p ^ (p - 1) →
      E ≤ Subgroup.normalizer (G₀ : Set G) → (∀ e ∈ E, GGPsiInnerDiag (ggU t n f).D ψ e) →
      E ⊓ Subgroup.centralizer (G₀ : Set G) = ⊥ →
      ∀ E₀ : Subgroup G, E₀ ≤ E → ∀ J : Subgroup G,
        IsComponentOf J (G₀ ⊓ Subgroup.centralizer (E₀ : Set G)) →
        p ^ 2 ≤ (Subgroup.centralizer (J : Set G)).relIndex E →
          ∀ e ∈ E₀, e ≠ 1 → ∃ K : Subgroup G,
            IsComponentOf K (G₀ ⊓ Subgroup.centralizer {e}) ∧ J ≤ K ∧ GGTypeAk f K

theorem ggSixLinearJInput_of_torus (hT : GGLinearTorusComponentInput) : GGSixLinearJInput := by
  intro G _ _ p B Bs x L D J t n f ψ h hlin hcard d hd hd1
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hpres : GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f ψ :=
    ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1.1, h.2.2.2.2.2.1.2⟩
  have hBs := h.bstar
  have hEC : Bs ⊓ Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥ := by
    have hnd := not_dvd_card_centralizer_ggG0_of_stdSub hp h.sstar h.stdType h.stdSub
    have hpg : IsPGroup p ↥(Bs ⊓ Subgroup.centralizer (ggG0 p B x L D J : Set G)) := fun g =>
      ⟨1, Subtype.ext (by simpa using hBs.2.1.2 g (Subgroup.mem_inf.mp g.2).1)⟩
    obtain ⟨k, hk⟩ := hpg.exists_card_eq
    have hdvd := Subgroup.card_dvd_of_le
      (inf_le_right : Bs ⊓ Subgroup.centralizer (ggG0 p B x L D J : Set G) ≤ _)
    rw [hk] at hdvd
    have hk0 : k = 0 := by
      by_contra hk0
      exact hnd ((dvd_pow_self p hk0).trans hdvd)
    rw [hk0, pow_zero] at hk
    exact Subgroup.card_eq_one.mp hk
  have hJc : IsComponentOf J (ggG0 p B x L D J ⊓ Subgroup.centralizer (D : Set G)) :=
    CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le h.j_isComponentOf_centralizer
      (le_inf h.le_ggG0 (h.j_le_inf.trans inf_le_right)) inf_le_right
  have hidx : p ^ 2 ≤ (Subgroup.centralizer (J : Set G)).relIndex Bs := by
    have hDeq : D = B ⊓ Subgroup.centralizer (J : Set G) := h.stdSub.1.2.2.2.2.2.2
    have hB : Nat.card B = p ^ LargeEvenTwoLocalRank p G := h.sstar.1.2.1
    have h4 : 4 ≤ LargeEvenTwoLocalRank p G := h.beta.2.2.2
    obtain ⟨m, hm⟩ : ∃ m, LargeEvenTwoLocalRank p G = m + 4 :=
      ⟨LargeEvenTwoLocalRank p G - 4, by omega⟩
    have h1 := Subgroup.relIndex_mul_card (Subgroup.centralizer (J : Set G)) B
    rw [inf_comm, ← hDeq, h.card_d, hB, hm,
      show p ^ (m + 4) = p ^ (m + 2) * p ^ 2 by ring] at h1
    have hr : (Subgroup.centralizer (J : Set G)).relIndex B = p ^ (m + 2) :=
      Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos 2) h1
    have hne : (Subgroup.centralizer (J : Set G)).relIndex Bs ≠ 0 := by
      intro h0
      have := Subgroup.relIndex_mul_card (Subgroup.centralizer (J : Set G)) Bs
      rw [h0, zero_mul] at this
      exact Nat.card_pos.ne' this.symm
    calc p ^ 2 ≤ p ^ (m + 2) := Nat.pow_le_pow_right hp.pos (by omega)
      _ = (Subgroup.centralizer (J : Set G)).relIndex B := hr.symm
      _ ≤ (Subgroup.centralizer (J : Set G)).relIndex Bs :=
        Subgroup.relIndex_le_of_le_right hBs.1 hne
  obtain ⟨K, hK, -, hKA⟩ := hT G p t n f ψ _ hpres hp hlin Bs hBs.2.1 hcard
    h.bstar_le_normalizer h.2.2.2.2.2.2.1.2 hEC D h.d_le_bstar J hJc hidx d hd hd1
  exact ⟨K, hK, hKA⟩

end Input

end CFSG.StandardType
