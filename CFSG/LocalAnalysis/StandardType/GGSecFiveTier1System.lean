module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Defs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Subtype
public import CFSG.ClassicalInvolution.WeakCT.TwistedTransport
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.ClassicalInvolution.WeakCT.SpPair
public import CFSG.ClassicalInvolution.WeakCT.TwistedE6Basic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.WeakCT

section System

variable {G : Type} [Group G] [Finite G]

theorem tier1_system (hT : GGSecFiveTier1Input) {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hsplit : GGSplitLie p L) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hsl : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {k : ℕ} (e' : Fin k ≃ ι)
    (Pc Pp : Fin k → Fin k → Prop) (hPc : ∀ i j, Pc i j → i ≠ j ∧ M.M (e' i) (e' j) = 2)
    (hPp : ∀ i j, Pp i j → M.M (e' i) (e' j) = 3) :
    ∃ (f : ℕ) (U : Fin k → Subgroup ↥(L ⊔ ⨆ K ∈ 𝒦, K)), 4 ≤ 2 ^ f ∧ ⨆ i, U i = ⊤ ∧
      (∀ i j, Pc i j → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a) ∧
      (∀ i j, Pp i j → ∃ W, LinearBlockStandardPair (GaloisField 2 f) W (U i) (U j)) ∧
      (∀ i, (U i).map (L ⊔ ⨆ K ∈ 𝒦, K).subtype =
        ggRankOnePerf Bs ((e (M.simple (e' i)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) := by
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
  have hS : ∀ i : Fin k, S (e' i) ≤ H := fun i => by
    rw [← hgenH]
    exact le_iSup S (e' i)
  have hcommBase : ∀ i j : Fin k, Pc i j → ∀ a ∈ S (e' i), ∀ b ∈ S (e' j), a * b = b * a := by
    intro i j hij a ha b hb
    obtain ⟨hne, hl⟩ := hPc i j hij
    exact hcomm (e' i) (e' j) (fun h => hne (e'.injective h)) hl a ha b hb
  have hpairBase : ∀ i j : Fin k, Pp i j →
      ∃ W, LinearBlockStandardPair F W (S (e' i)) (S (e' j)) :=
    fun i j hij => hpair (e' i) (e' j) (hPp i j hij)
  obtain ⟨hgenH', hcommH, hpairH⟩ :=
    tier1_subtype_system (K := F) S H hgenH e' Pc Pp hcommBase hpairBase
  refine ⟨f, fun i => (S (e' i)).subgroupOf H, hq, hgenH', hcommH, ?_, ?_⟩
  · intro i j hij
    obtain ⟨W, hW⟩ := hpairH i j hij
    exact ⟨W, LinearBlockStandardPair.of_ringEquiv ε hW⟩
  · intro i
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr (hS i)

end System

end CFSG.StandardType

end
