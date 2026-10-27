module

public import CFSG.LocalAnalysis.StandardType.GGRoundFourSmallALinearBlock
public import CFSG.LocalAnalysis.StandardType.GGSixStepThreeCFSeventeen

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits

section Inputs

theorem ggTypeAk_of_isComponentOf_PSL {G : Type} [Group G] [Finite G] {p n f : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hnp : n = p) (hf : 1 ≤ f) (hpf : p ∣ 2 ^ f - 1)
    (ψ : (ggU .PSL n f).K →* G) (hker : ψ.ker ≤ Subgroup.center (ggU .PSL n f).K)
    {E : Subgroup G} (hE : IsElemAbelian p E) (hbig : p ^ 2 < Nat.card E)
    (hEdiag : ∀ e ∈ E, GGPsiInnerDiag (ggU .PSL n f).D ψ e)
    (hEC : E ⊓ Subgroup.centralizer (ψ.range : Set G) = ⊥) {b : G} (hb : b ∈ E)
    {L₁ : Subgroup G} (hL : IsComponentOf L₁ (ψ.range ⊓ Subgroup.centralizer {b}))
    (hex : ¬ LieModel (↥L₁ ⧸ Subgroup.center ↥L₁) .PSL 2 2 f) : GGTypeAk f L₁ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact LinTypeAk.ggTypeAk_of_isComponentOf_sl hp hp5 hnp hf hpf hker hE hbig hEdiag hEC hb hL
    hex

theorem ggTypeAk_of_isComponentOf_PSU {G : Type} [Group G] [Finite G] {p n f : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hnp : n = p) (hf : 1 ≤ f) (hpf : p ∣ 2 ^ f + 1) :
    ∀ ψ : (ggU .PSU n f).K →* G, ψ.ker ≤ Subgroup.center (ggU .PSU n f).K →
      ∀ E : Subgroup G, IsElemAbelian p E → p ^ 2 < Nat.card E →
        (∀ e ∈ E, GGPsiInnerDiag (ggU .PSU n f).D ψ e) →
        E ⊓ Subgroup.centralizer (ψ.range : Set G) = ⊥ → ∀ b ∈ E, ∀ L₁ : Subgroup G,
          IsComponentOf L₁ (ψ.range ⊓ Subgroup.centralizer {b}) →
          ¬ LieModel (↥L₁ ⧸ Subgroup.center ↥L₁) .PSL 2 2 f → GGTypeAk f L₁ := by
  have hU : ggU .PSU n f =
      ⟨Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
        Unitary.rootDatum (card_galoisField_two_mul 2 f hf) n⟩ := by
    simp only [ggU, lieUniversal, hf, ↓reduceDIte]
  rw [hU]
  intro ψ hker E hE hbig hEdiag hEC b hb L₁ hL hex
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact LinTypeAk.ggTypeAk_of_isComponentOf_su hp hp5 hnp hf hpf hker hE hbig hEdiag hEC hb hL
    hex

theorem ggSixSeventeenLinearTypeInput_holds : GGSixSeventeenLinearTypeInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx hcent hlin b L₁ hpair
  obtain ⟨hp5, hnp, hcase⟩ := hlin
  have hβ := hctx.1.2.2.2.2.2.1
  have hp : p.Prime := hβ.1
  have hBs := hctx.2.1
  have hbig : p ^ 2 < Nat.card Bs := by
    have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hctx.1.2.2.2.2.2.2.1.1.2.1
    have h4r : 4 ≤ LargeEvenTwoLocalRank p G := hβ.2.2.2
    have hBle : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hBs.1
    calc p ^ 2 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
      _ ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hp.pos h4r
      _ = Nat.card B := hBcard.symm
      _ ≤ Nat.card Bs := hBle
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hdiag := hctx.2.2.2.2.2.2.1.2
  have hEC : Bs ⊓ Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange, hcent, inf_bot_eq]
  obtain ⟨hb, -, hL, hnex⟩ := hpair
  rw [← hrange] at hL
  rcases hcase with ⟨rfl, hpf⟩ | ⟨rfl, hpf⟩
  · have hex : ¬ LieModel (↥L₁ ⧸ Subgroup.center ↥L₁) .PSL 2 2 f := fun hm =>
      hnex (Or.inr (Or.inr (Or.inl ⟨rfl, hpf, hm⟩)))
    exact ggTypeAk_of_isComponentOf_PSL hp hp5 hnp hf hpf ψ hker hBs.2.1 hbig hdiag hEC hb hL hex
  · have hex : ¬ LieModel (↥L₁ ⧸ Subgroup.center ↥L₁) .PSL 2 2 f := fun hm =>
      hnex (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hpf, hm⟩))))
    exact ggTypeAk_of_isComponentOf_PSU hp hp5 hnp hf hpf ψ hker Bs hBs.2.1 hbig hdiag hEC b hb
      L₁ hL hex

end Inputs

end CFSG.StandardType
