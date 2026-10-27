module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosFinal

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

theorem nsJA2_card_le_mul_card_inf {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {B Bs H : Subgroup G} (hB : B ≤ Bs) (hrel : H.relIndex Bs = p) :
    Nat.card B ≤ p * Nat.card ↥(H ⊓ B) := by
  have hrelB : H.relIndex B ≤ p :=
    (Subgroup.relIndex_le_of_le_right hB (by rw [hrel]; exact hp.ne_zero)).trans (le_of_eq hrel)
  calc Nat.card B = H.relIndex B * Nat.card ↥(H ⊓ B) := (Subgroup.relIndex_mul_card H B).symm
    _ ≤ p * Nat.card ↥(H ⊓ B) := Nat.mul_le_mul_right _ hrelB

theorem nsJA2_false_of_le_pairBlock
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ) (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs)
    {a b : Fin n} (hab : a ≠ b) (hJ : J ≤ (ggSuPairBlock K 2 f n a b).map ψ) : False := by
  obtain ⟨ε, hrefl, hblock⟩ := ggNSDiag_position h hd
  let r : MulAut ↥Bs := (ε (Equiv.swap a b) : ↥(ggAutomizer ψ.range Bs))
  have hr : GGIsReflection p r := hrefl a b hab
  have hS : ggRankOneIn ψ.range Bs r = (ggSuPairBlock K 2 f n a b).map ψ := hblock a b hab
  have hJH : J ≤ Subgroup.centralizer (ggHyperplane Bs r : Set G) := by
    have hJle : J ≤ ggRankOneIn ψ.range Bs r := by
      rw [hS]
      exact hJ
    refine hJle.trans ?_
    rw [ggRankOneIn]
    exact (ggOTwoPrime_le _).trans inf_le_right
  have hHleCJ : ggHyperplane Bs r ≤ Subgroup.centralizer (J : Set G) :=
    Subgroup.le_centralizer_iff.mpr hJH
  have hpre : LargeEvenStdSubPre p B x L D J := hcfg.1.1.2.2.1
  have hDcard : Nat.card D = p ^ 2 := hpre.2.2.1
  have hDBJ : D = B ⊓ Subgroup.centralizer (J : Set G) := hpre.2.2.2.2.2.2
  have hBHleD : ggHyperplane Bs r ⊓ B ≤ D := by
    rw [inf_comm, hDBJ]
    exact le_inf inf_le_left (inf_le_right.trans hHleCJ)
  have hp : p.Prime := h.prime
  have hHrel : (ggHyperplane Bs r).relIndex Bs = p := by
    have hHle : ggHyperplane Bs r ≤ Bs := by
      rw [ggHyperplane]
      exact Subgroup.map_subtype_le _
    have hcardH : Nat.card ↥(ggHyperplane Bs r) = Nat.card {b : ↥Bs // r b = b} := by
      rw [ggHyperplane, Subgroup.card_map_of_injective Bs.subtype_injective]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
    have h1 : (ggHyperplane Bs r).relIndex Bs * Nat.card ↥(ggHyperplane Bs r) = Nat.card Bs := by
      have h := Subgroup.relIndex_mul_card (H := ggHyperplane Bs r) (K := Bs)
      rwa [inf_eq_left.mpr hHle] at h
    rw [hcardH] at h1
    have h2 : Nat.card {b : ↥Bs // r b = b} * p = Nat.card Bs := hr.2
    haveI : Nonempty {b : ↥Bs // r b = b} := ⟨⟨1, map_one r⟩⟩
    have hpos : 0 < Nat.card {b : ↥Bs // r b = b} := Nat.card_pos
    rw [Nat.mul_comm] at h1
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)
  have hcardB : Nat.card B ≤ p * Nat.card ↥(ggHyperplane Bs r ⊓ B) :=
    nsJA2_card_le_mul_card_inf hp h.bstar.1 hHrel
  have hcardInf : Nat.card ↥(ggHyperplane Bs r ⊓ B) ≤ p ^ 2 := by
    calc Nat.card ↥(ggHyperplane Bs r ⊓ B) ≤ Nat.card D := Subgroup.card_le_of_le hBHleD
      _ = p ^ 2 := hDcard
  have hcontra : p ^ 4 ≤ p ^ 3 := by
    calc p ^ 4 ≤ Nat.card B := h.rank
      _ ≤ p * Nat.card ↥(ggHyperplane Bs r ⊓ B) := hcardB
      _ ≤ p * p ^ 2 := Nat.mul_le_mul_left p hcardInf
      _ = p ^ 3 := by ring
  have hple : p ≤ 1 := by
    have h1 : p ^ 3 * p ≤ p ^ 3 * 1 := by
      calc p ^ 3 * p = p ^ 4 := by ring
        _ ≤ p ^ 3 := hcontra
        _ = p ^ 3 * 1 := by ring
    exact Nat.le_of_mul_le_mul_left h1 (pow_pos hp.pos 3)
  exact absurd hple (not_le.mpr hp.one_lt)

end CFSG.StandardType

end
