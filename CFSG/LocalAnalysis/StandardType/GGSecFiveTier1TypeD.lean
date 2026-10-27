module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Defs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Subtype
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Weyl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1PresD
public import CFSG.ClassicalInvolution.WeakCT.TwistedTransport
public import CFSG.ClassicalInvolution.WeakCT.SpPair
public import CFSG.ClassicalInvolution.WeakCT.TwistedE6Basic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld

section TypeD

variable {G : Type} [Group G] [Finite G]

theorem ggSecFiveIdentD_of_tier1 (hT : GGSecFiveTier1Input) {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hsplit : GGSplitLie p L) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) {n : ℕ} (hn : 4 ≤ n)
    (e' : Fin n ≃ ι) (hM : M = (ggCoxeterMatrixD n).reindex e') :
    ∃ (t : StatedLieTag) (n' f : ℕ) (ψ : (ggU t n' f).K →* G), 3 ≤ bnRank t n' ∧
      GGPresentsG0 (L ⊔ ⨆ K ∈ 𝒦, K) (ggU t n' f).D t n' f ψ := by
  have hWeyl : GGIsWeylMatrixAD M := Or.inr ⟨n, e', hn, hM⟩
  obtain ⟨F, hF, hFin, hchar, h4, hcomm, hpair, hgen⟩ :=
    hT G p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres
      (fun i j hij => GGIsWeylMatrixAD.le_three hWeyl i j hij)
  letI : Field F := hF
  letI : Finite F := hFin
  letI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := hchar
  obtain ⟨m, -, hmcard⟩ := FiniteField.card F 2
  have hmne : (m : ℕ) ≠ 0 := m.pos.ne'
  haveI : NeZero (m : ℕ) := ⟨hmne⟩
  letI : Fintype (GaloisField 2 (m : ℕ)) := Fintype.ofFinite _
  have hFcard : Nat.card F = 2 ^ (m : ℕ) := by
    rw [Nat.card_eq_fintype_card, hmcard]
  have hGFcard : Nat.card (GaloisField 2 (m : ℕ)) = 2 ^ (m : ℕ) :=
    GaloisField.card 2 (m : ℕ) hmne
  have hcardEq : Fintype.card F = Fintype.card (GaloisField 2 (m : ℕ)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hFcard, hGFcard]
  let eF : F ≃+* GaloisField 2 (m : ℕ) := FiniteField.ringEquivOfCardEq hcardEq
  let S : ι → Subgroup G := fun i =>
    ggRankOnePerf Bs ((e (M.simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)
  let H : Subgroup G := L ⊔ ⨆ K ∈ 𝒦, K
  have hpairGF : ∀ i j : ι, M.M i j = 3 →
      ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 2 (m : ℕ)) W (S i) (S j) := by
    intro i j hij
    obtain ⟨W, hW⟩ := hpair i j hij
    exact ⟨W, LinearBlockStandardPair.of_ringEquiv eF hW⟩
  have hlabel2 : ∀ i j : Fin n, i ≠ j → ¬ edgeD n i j → ¬ edgeD n j i →
      M.M (e' i) (e' j) = 2 := by
    intro i j hij h1 h2
    rw [hM, coxeterMatrix_reindex_apply_equiv]
    exact ggCoxeterMatrixD_eq_two hn i j hij h1 h2
  have hlabel3 : ∀ i j : Fin n, edgeD n i j → M.M (e' i) (e' j) = 3 := by
    intro i j h
    rw [hM, coxeterMatrix_reindex_apply_equiv]
    exact ggCoxeterMatrixD_eq_three hn i j h
  obtain ⟨hgen_sub, hcomm_sub, hpair_sub⟩ :=
    tier1_subtype_system (X := G) S H hgen e'
      (fun i j => i ≠ j ∧ ¬ edgeD n i j ∧ ¬ edgeD n j i)
      (fun i j => edgeD n i j)
      (fun i j hij a ha b hb =>
        hcomm (e' i) (e' j) (fun he => hij.1 (e'.injective he))
          (hlabel2 i j hij.1 hij.2.1 hij.2.2) a ha b hb)
      (fun i j hij => hpairGF (e' i) (e' j) (hlabel3 i j hij))
  have hq : 4 ≤ 2 ^ (m : ℕ) := by
    rw [← hFcard]; exact h4
  obtain ⟨ψ, hpresentation⟩ :=
    ggPresentsG0_typeD_of_system hn hq
      (fun i j hij h1 h2 => hcomm_sub i j ⟨hij, h1, h2⟩)
      (fun i j hij => hpair_sub i j hij)
      hgen_sub
  exact ⟨.POmegaPlus, n, (m : ℕ), ψ, by simp only [bnRank]; omega, hpresentation⟩

end TypeD

end CFSG.StandardType

end
