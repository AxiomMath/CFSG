module

public import CFSG.RankThree.PartOne.S11.FivePlusInner
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingOutsideSix
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Blueprint CFSG.ComponentClassification
open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def OuterPrimeTwoTrivial (S : Type) [Group S] : Prop :=
  ∀ (p : ℕ) (P Q : Subgroup (Outer S)), p.Prime → 3 < p → IsPGroup p P → IsPGroup 2 Q →
    P ≤ Subgroup.normalizer (Q : Set (Outer S)) → ⁅Q, P⁆ = Q → Q = ⊥

@[expose] def ClassicalOuterPrimeTwoTrivial : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    Milestones.ClassicalRep S → OuterPrimeTwoTrivial S

@[expose] def ExceptionalOuterPrimeTwoTrivial : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ExceptionalRep S → OuterPrimeTwoTrivial S

@[expose] def SporadicOuterOrderLeTwo : Prop :=
  ∀ s : TauCeti.SporadicName, Nat.card (Outer (NativeSporadic.Carrier s)) ≤ 2

theorem outerPrimeTwoTrivial_of_card_le_four {S : Type} [Group S] [Finite S]
    (h : Nat.card (Outer S) ≤ 4) : OuterPrimeTwoTrivial S := by
  intro p P Q hp hp3 hP _ _ hcomm
  have : Fact p.Prime := ⟨hp⟩
  have hPbot : P = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hP ⟨x, hx⟩
    have hdvd : orderOf x ∣ Nat.card (Outer S) := orderOf_dvd_natCard x
    have hle : orderOf x ≤ 4 := (Nat.le_of_dvd Nat.card_pos hdvd).trans h
    have hord : orderOf x = p ^ k := by rw [← Subgroup.orderOf_mk x hx]; exact hk
    have hp5 : 5 ≤ p := by
      by_contra hlt
      have h4 : p = 4 := by omega
      rw [h4] at hp
      norm_num at hp
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · rw [hk0, pow_zero] at hord
      exact orderOf_eq_one_iff.mp hord
    · exfalso
      have : p ≤ p ^ k := Nat.le_self_pow (by omega) p
      omega
  rw [← hcomm, hPbot, Subgroup.commutator_bot_right]

theorem outerPrimeTwoTrivial_alternating {S : Type} [Group S] [Finite S] {n : ℕ} (hn : 5 ≤ n)
    (e : S ≃* alternatingGroup (Fin n)) : OuterPrimeTwoTrivial S := by
  apply outerPrimeTwoTrivial_of_card_le_four
  by_cases h6 : n = 6
  · subst h6
    exact CatalogueSchreierAlternating.DegreeSix.outer_card_le_four_of_equiv e
  · exact (Nat.le_of_dvd (by norm_num)
      (CatalogueSchreierAlternating.outer_card_dvd_two_of_equiv_outside_six (by omega) e)).trans
      (by norm_num)

theorem outerPrimeTwoTrivial_sporadic (hsp : SporadicOuterOrderLeTwo) {S : Type} [Group S]
    [Finite S] (hS : NativeSporadic.SporadicRep S) : OuterPrimeTwoTrivial S := by
  obtain ⟨s, ⟨e⟩⟩ := hS
  apply outerPrimeTwoTrivial_of_card_le_four
  rw [Nat.card_congr (equivalence e).toEquiv]
  exact (hsp s).trans (by norm_num)

theorem outerPrimeTwoTrivial_of_catalog (hcl : ClassicalOuterPrimeTwoTrivial)
    (hex : ExceptionalOuterPrimeTwoTrivial) (hsp : SporadicOuterOrderLeTwo) {S : Type}
    [Group S] [Finite S] (hsimple : IsSimpleGroup S) (hnonab : ∃ a b : S, a * b ≠ b * a)
    (hcat : Catalog S) : OuterPrimeTwoTrivial S := by
  rcases hcat with ⟨q, hq, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | hclass | hexc | hspor
  ·
    exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    apply hab
    have h1 : e (a * b) = e (b * a) := by
      rw [map_mul, map_mul]
      exact mul_comm _ _
    exact e.injective h1
  · exact outerPrimeTwoTrivial_alternating hn e
  · exact hcl S hsimple hnonab hclass
  · exact hex S hsimple hnonab hexc
  · exact outerPrimeTwoTrivial_sporadic hsp hspor

theorem catalogPrimeTwoAutomorphismsInner_of_outer
    (h : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Catalog S → OuterPrimeTwoTrivial S) : CatalogPrimeTwoAutomorphismsInner := by
  intro J _ _ hq hcat p P Q hp hp3 hP hQ hPQ hcomm
  have hperf : Group.IsPerfect J := hq.1
  have hsimple : IsSimpleGroup (J ⧸ Subgroup.center J) := hq.2.1
  have hS := h (J ⧸ Subgroup.center J) hsimple hq.2.2 hcat
  set Φ : MulAut J →* Outer (J ⧸ Subgroup.center J) :=
    (centerQuotientOuterHom J).comp (QuotientGroup.mk' (inner J)) with hΦ
  have hPΦ : IsPGroup p (P.map Φ) := hP.map Φ
  have hQΦ : IsPGroup 2 (Q.map Φ) := hQ.map Φ
  have hnorm : P.map Φ ≤ Subgroup.normalizer ((Q.map Φ : Subgroup _) : Set _) :=
    (Subgroup.map_mono hPQ).trans (Subgroup.le_normalizer_map Φ)
  have hc : ⁅Q.map Φ, P.map Φ⁆ = Q.map Φ := by
    rw [← Subgroup.map_commutator, hcomm]
  have hbot := hS p (P.map Φ) (Q.map Φ) hp hp3 hPΦ hQΦ hnorm hc
  intro q hq'
  have h1 : Φ q ∈ Q.map Φ := Subgroup.mem_map_of_mem Φ hq'
  rw [hbot, Subgroup.mem_bot] at h1
  have hinj := centerQuotient_outer_injective J
  have h2 : (QuotientGroup.mk' (inner J)) q = 1 := hinj (by
    rw [map_one]
    exact h1)
  have h3 : q ∈ inner J := (QuotientGroup.eq_one_iff q).mp h2
  exact h3

theorem catalogPrimeTwoAutomorphismsInner_of_inspections (hcl : ClassicalOuterPrimeTwoTrivial)
    (hex : ExceptionalOuterPrimeTwoTrivial) (hsp : SporadicOuterOrderLeTwo) :
    CatalogPrimeTwoAutomorphismsInner :=
  catalogPrimeTwoAutomorphismsInner_of_outer fun _ _ _ hsimple hnonab hcat =>
    outerPrimeTwoTrivial_of_catalog hcl hex hsp hsimple hnonab hcat

end CFSG.RankThree.PartOne
