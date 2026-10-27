module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.RankThree.PartOne.CTP.StrongPGlue
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
import CFSG.GroupTheory.ABGLocalTools.Constraint
import CFSG.GroupTheory.PGroup.ElemAbelianSq

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.Open
open scoped Pointwise
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem pPrimeCore_le {M H : Subgroup G} {p : ℕ} (hM : IsStronglyPEmbedded p M)
    (hp : p.Prime) (hrank : 2 ≤ CFSG.Open.pRank p (H ⊓ M)) :
    (CFSG.pPrimeCore p ↥H).map H.subtype ≤ M := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, hEHM, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (H ⊓ M)
  have hEM : E ≤ M := hEHM.trans inf_le_right
  have hEH : E ≤ H := hEHM.trans inf_le_left
  have hE2 : p ^ 2 ≤ Nat.card E := by
    rw [hEcard]
    exact Nat.pow_le_pow_right hp.pos hrank
  have hXcop : Nat.Coprime p (Nat.card ((CFSG.pPrimeCore p ↥H).map H.subtype)) := by
    rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  have hAX : E ≤
      Subgroup.normalizer (((CFSG.pPrimeCore p ↥H).map H.subtype : Subgroup G) : Set G) :=
    hEH.trans (CFSG.ABGLocalTools.le_normalizer_map_subtype H (CFSG.pPrimeCore p ↥H))
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity (G := G) hp
    hE hE2 hAX hXcop
  rw [← hgen]
  refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
  exact inf_le_right.trans (hM.centralizer_le ha1 (hE.2 a ha) (hEM ha))

theorem odd_card_pPrimeCore {M H : Subgroup G} {p : ℕ} (hM : IsStronglyPEmbedded p M)
    (hp : p.Prime)
    (huniq : ∀ D : Subgroup G, D ≠ ⊥ → IsPGroup 2 D →
      2 ≤ CFSG.Open.pRank p (Subgroup.normalizer (D : Set G) ⊓ M) →
      Subgroup.normalizer (D : Set G) ≤ M)
    (hHM : ¬ H ≤ M) (hrank : 2 ≤ CFSG.Open.pRank p (H ⊓ M)) :
    Odd (Nat.card (CFSG.pPrimeCore p ↥H)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro h2dvd
  set K : Subgroup ↥H := CFSG.pPrimeCore p ↥H
  have hKcop' : ¬ p ∣ Nat.card K :=
    (hp.coprime_iff_not_dvd).mp CFSG.pPrimeCore_coprime_card
  obtain ⟨E, hEHM, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (H ⊓ M)
  have hEM : E ≤ M := hEHM.trans inf_le_right
  have hKM : K.map H.subtype ≤ M := pPrimeCore_le hM hp hrank
  have hEp : IsPGroup p ↥(E.subgroupOf H) := (hE.subgroupOf H).isPGroup
  have hEnorm : E.subgroupOf H ≤ Subgroup.normalizer (K : Set ↥H) :=
    Subgroup.le_normalizer_of_normal (H := K) (K := E.subgroupOf H)
  obtain ⟨S, hS⟩ := CFSG.GroupTheory.exists_sylow_le_normalizer_of_isPGroup
    (G := ↥H) hp Nat.prime_two hEp hEnorm hKcop'
  let D : Subgroup G := ((S : Subgroup ↥K).map K.subtype).map H.subtype
  have hD2 : IsPGroup 2 D := ((S.isPGroup').map K.subtype).map H.subtype
  have hSne : (S : Subgroup ↥K) ≠ ⊥ := Sylow.ne_bot_of_dvd_card S h2dvd
  have hDne : D ≠ ⊥ := by
    have h1 : (S : Subgroup ↥K).map K.subtype ≠ ⊥ := by
      intro hbot
      exact hSne ((Subgroup.map_eq_bot_iff_of_injective (S : Subgroup ↥K)
        K.subtype_injective).1 hbot)
    have h2 : ((S : Subgroup ↥K).map K.subtype).map H.subtype ≠ ⊥ := by
      intro hbot
      exact h1 ((Subgroup.map_eq_bot_iff_of_injective ((S : Subgroup ↥K).map K.subtype)
        H.subtype_injective).1 hbot)
    exact h2
  have hEN : E ≤ Subgroup.normalizer (D : Set G) := by
    have h1 : (E.subgroupOf H).map H.subtype ≤
        (Subgroup.normalizer (((S : Subgroup ↥K).map K.subtype : Subgroup ↥H) : Set ↥H)).map
          H.subtype := Subgroup.map_mono hS
    have h2 : (Subgroup.normalizer
          (((S : Subgroup ↥K).map K.subtype : Subgroup ↥H) : Set ↥H)).map H.subtype ≤
        Subgroup.normalizer (D : Set G) := Subgroup.le_normalizer_map H.subtype
    have h3 : (E.subgroupOf H).map H.subtype = E :=
      Subgroup.map_subgroupOf_eq_of_le (hEHM.trans inf_le_left)
    rw [h3] at h1
    exact h1.trans h2
  have hpRank : 2 ≤ CFSG.Open.pRank p (Subgroup.normalizer (D : Set G) ⊓ M) := by
    have hle : CFSG.Open.pRank p (H ⊓ M) ≤
        CFSG.Open.pRank p (Subgroup.normalizer (D : Set G) ⊓ M) :=
      CFSG.SectionRank.le_pRank hp.one_lt (le_inf hEN hEM) hE hEcard
    exact hrank.trans hle
  have hNle : Subgroup.normalizer (D : Set G) ≤ M := huniq D hDne hD2 hpRank
  have hfr : Subgroup.normalizer
      (((S : Subgroup ↥K).map K.subtype : Subgroup ↥H) : Set ↥H) ⊔ K = ⊤ :=
    Sylow.normalizer_sup_eq_top (p := 2) (G := ↥H) (N := K) S
  have hsplit : (Subgroup.normalizer
        (((S : Subgroup ↥K).map K.subtype : Subgroup ↥H) : Set ↥H)).map H.subtype ⊔
      K.map H.subtype = H := by
    have h := congrArg (Subgroup.map H.subtype) hfr
    rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype] at h
    exact h
  have hNHM : (Subgroup.normalizer
        (((S : Subgroup ↥K).map K.subtype : Subgroup ↥H) : Set ↥H)).map H.subtype ≤ M :=
    (Subgroup.le_normalizer_map H.subtype).trans hNle
  exact hHM (hsplit ▸ sup_le hNHM hKM)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
