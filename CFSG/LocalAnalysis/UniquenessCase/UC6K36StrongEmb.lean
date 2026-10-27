module

public import CFSG.LocalAnalysis.StronglyEmbedded.OfCentralizers
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LocalAnalysis.StronglyEmbedded.GammaOne
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

private theorem one_le_pRank_of_isPGroup {q : ℕ} [Fact q.Prime] {S : Subgroup G} (hS : IsPGroup q S)
    (hS1 : S ≠ ⊥) : 1 ≤ CFSG.Open.pRank q S := by
  have hdvd : q ∣ Nat.card S :=
    hS.card_eq_or_dvd.resolve_left fun h => hS1 (Subgroup.card_eq_one.mp h)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥S) q hdvd
  have hxq : (x : G) ^ q = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    exact congrArg Subtype.val this
  have hx1 : (x : G) ≠ 1 := by
    intro h
    have : x = 1 := Subtype.ext h
    rw [this, orderOf_one] at hx
    exact (Fact.out : q.Prime).one_lt.ne hx
  have hz : Subgroup.zpowers (x : G) ≤ S := Subgroup.zpowers_le.2 x.2
  have hel : IsElemAbelian q (Subgroup.zpowers (x : G)) := CFSG.Open.isElemAbelian_zpowers hxq
  have hcard : Nat.card (Subgroup.zpowers (x : G)) = q ^ 1 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hxq hx1, pow_one]
  exact CFSG.SectionRank.le_pRank (Fact.out : q.Prime).one_lt hz hel hcard

theorem isStronglyPEmbedded_of_rankThreeGamma_le_sylow {q : ℕ} [Fact q.Prime] {S H : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf q S ⊤) (hS1 : S ≠ ⊥)
    (hΓ : rankThreeGamma 1 q S ≤ H) (hH : H ≠ ⊤) : IsStronglyPEmbedded q H := by
  have hNS : normalizer (S : Set G) ≤ H :=
    (CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore (p := q) (k := 1) le_rfl
      (one_le_pRank_of_isPGroup hS.isPGroup hS1)).trans hΓ
  have hSH : S ≤ H := (Subgroup.le_normalizer (H := S)).trans hNS
  exact CFSG.RankThree.PartOne.isStronglyPEmbedded_of_normalizer_sylow_le hH
    (hS.of_le hSH le_top) hS1 hNS fun x hx hxo =>
      CFSG.RankThree.PartOne.centralizer_le_of_rankThreeGamma_le hΓ hx hxo

@[expose] noncomputable def star36Sup (q : ℕ) (S : Subgroup G) : Subgroup G :=
  rankThreeGamma 1 q S ⊔ ⨆ (Y : Subgroup G) (_ : Y ≤ S) (_ : 1 < CFSG.Open.pRank q Y), ⨆ N ∈ calMOf Y, N

theorem le_star36Sup_of_mem_calMOf {q : ℕ} {S Y N : Subgroup G} (hYS : Y ≤ S) (hY : 1 < CFSG.Open.pRank q Y)
    (hN : N ∈ calMOf Y) : N ≤ star36Sup q S :=
  le_sup_of_le_right (le_iSup_of_le Y (le_iSup_of_le hYS (le_iSup_of_le hY
    (le_iSup₂_of_le N hN le_rfl))))

theorem isStronglyPEmbedded_star36Sup {q : ℕ} [Fact q.Prime] {S : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf q S ⊤) (hS1 : S ≠ ⊥) (ha : star36Sup q S ≠ ⊤) :
    IsStronglyPEmbedded q (star36Sup q S) :=
  isStronglyPEmbedded_of_rankThreeGamma_le_sylow hS hS1 le_sup_left ha

end CFSG.LocalAnalysis.UniquenessCase.UCK
