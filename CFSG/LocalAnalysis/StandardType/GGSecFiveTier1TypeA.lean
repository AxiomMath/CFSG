module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Defs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Subtype
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Weyl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1PresA
public import CFSG.ClassicalInvolution.WeakCT.TwistedTransport
public import CFSG.ClassicalInvolution.WeakCT.SpPair
public import CFSG.ClassicalInvolution.WeakCT.TwistedE6Basic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.WeakCT

section TypeA

variable {G : Type} [Group G] [Finite G]

theorem ggSecFiveIdentA_of_tier1 (hT : GGSecFiveTier1Input) {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hsplit : GGSplitLie p L) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) {n : ℕ} (hn : 3 ≤ n)
    (e' : Fin n ≃ ι) (hM : M = (CoxeterMatrix.A n).reindex e') :
    ∃ (t : StatedLieTag) (n' f : ℕ) (ψ : (ggU t n' f).K →* G), 3 ≤ bnRank t n' ∧
      GGPresentsG0 (L ⊔ ⨆ K ∈ 𝒦, K) (ggU t n' f).D t n' f ψ := by
  have hsl : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 :=
    GGIsWeylMatrixAD.le_three (Or.inl ⟨n, e', hn, hM⟩)
  obtain ⟨F, hF, hFfin, hchar, h4, hcomm, hpair, hgen⟩ :=
    hT G p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hsl
  letI : Field F := hF
  letI : Finite F := hFfin
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := hchar
  obtain ⟨m, -, hcard⟩ := FiniteField.card F 2
  let f : ℕ := (m : ℕ)
  have hf : f ≠ 0 := by
    simp only [f]
    exact Nat.pos_iff_ne_zero.mp m.pos
  have hcard' : Fintype.card F = 2 ^ f := hcard
  have hq : 4 ≤ 2 ^ f := by
    rw [Nat.card_eq_fintype_card, hcard'] at h4
    exact h4
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  have hcardGF : Fintype.card (GaloisField 2 f) = 2 ^ f := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 f hf
  have hcard_eq : Fintype.card F = Fintype.card (GaloisField 2 f) := by
    rw [hcard', hcardGF]
  let ε : F ≃+* GaloisField 2 f := FiniteField.ringEquivOfCardEq hcard_eq
  let S : ι → Subgroup G := fun i =>
    ggRankOnePerf Bs ((e (M.simple i) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)
  let H : Subgroup G := L ⊔ ⨆ K ∈ 𝒦, K
  have hgenH : ⨆ i, S i = H := hgen
  have hlabel2 : ∀ i j : Fin n, (i : ℕ) + 1 < j → M.M (e' i) (e' j) = 2 := by
    intro i j hij
    rw [hM, coxeterMatrix_reindex_apply_equiv]
    exact coxeterMatrixA_eq_two n i j hij
  have hlabel3 : ∀ i j : Fin n, (j : ℕ) = i + 1 → M.M (e' i) (e' j) = 3 := by
    intro i j hij
    rw [hM, coxeterMatrix_reindex_apply_equiv]
    exact coxeterMatrixA_eq_three n i j hij
  have hcommBase : ∀ i j : Fin n, (i : ℕ) + 1 < j →
      ∀ a ∈ S (e' i), ∀ b ∈ S (e' j), a * b = b * a := by
    intro i j hij a ha b hb
    refine hcomm (e' i) (e' j) (fun h => ?_) (hlabel2 i j hij) a ha b hb
    exact absurd (e'.injective h) (by omega)
  have hpairBase : ∀ i j : Fin n, (j : ℕ) = i + 1 →
      ∃ W, LinearBlockStandardPair F W (S (e' i)) (S (e' j)) :=
    fun i j hij => hpair (e' i) (e' j) (hlabel3 i j hij)
  obtain ⟨hgenH', hcommH, hpairH⟩ :=
    tier1_subtype_system (K := F) S H hgenH e'
      (fun i j : Fin n => (i : ℕ) + 1 < j)
      (fun i j : Fin n => (j : ℕ) = i + 1) hcommBase hpairBase
  let U : Fin n → Subgroup ↥H := fun i => (S (e' i)).subgroupOf H
  have hgenU : ⨆ i, U i = ⊤ := hgenH'
  have hcommU : ∀ i j : Fin n, (i : ℕ) + 1 < j →
      ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x := fun i j hij => hcommH i j hij
  have hpairU : ∀ i j : Fin n, (j : ℕ) = i + 1 →
      ∃ W, LinearBlockStandardPair (GaloisField 2 f) W (U i) (U j) := by
    intro i j hij
    obtain ⟨W, hW⟩ := hpairH i j hij
    exact ⟨W, LinearBlockStandardPair.of_ringEquiv ε hW⟩
  obtain ⟨ψ, hψ⟩ := ggPresentsG0_typeA_of_system (H := H) hn hq hcommU hpairU hgenU
  exact ⟨.PSL, n + 1, f, ψ, by simp only [bnRank]; omega, hψ⟩

end TypeA

end CFSG.StandardType

end
