module

public import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.RankThree.PartTwo.Census.Criteria
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.S58

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.Assembly.RankThreeEven (localRank)

@[expose] def A5Abs (C : Type) [Group C] [Finite C] : Prop :=
  ∀ B : Subgroup C, CFSG.Open.IsElemAbelian 3 B →
    (∃ T : Subgroup C, IsPGroup 2 T ∧ T ≠ ⊥ ∧ B ≤ Subgroup.normalizer (T : Set C)) →
    Nat.card B = 3 ^ localRank 3 C →
    ∃ T : Subgroup C, IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set C) ∧
      ¬ B ≤ Subgroup.centralizer (T : Set C)

theorem A5Abs.of_mulEquiv {C C' : Type} [Group C] [Group C'] [Finite C] [Finite C']
    (e : C ≃* C') (h : A5Abs C) : A5Abs C' := by
  intro B' hB' hT' hcard
  obtain ⟨T', hT'2, hT'1, hB'N⟩ := hT'
  have hBel : CFSG.Open.IsElemAbelian 3 (B'.map e.symm.toMonoidHom) := hB'.map _
  have hBN : ∃ T : Subgroup C, IsPGroup 2 T ∧ T ≠ ⊥ ∧
      B'.map e.symm.toMonoidHom ≤ Subgroup.normalizer (T : Set C) := by
    refine ⟨T'.map e.symm.toMonoidHom, hT'2.map _, ?_, ?_⟩
    · intro h0
      exact hT'1 ((Subgroup.map_eq_bot_iff_of_injective T'
        (f := e.symm.toMonoidHom) e.symm.injective).mp h0)
    · exact (Subgroup.map_mono hB'N).trans (Subgroup.map_equiv_normalizer_eq T' e.symm).le
  have hcardB : Nat.card (B'.map e.symm.toMonoidHom) = 3 ^ localRank 3 C := by
    rw [Subgroup.card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective, hcard,
      CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e Nat.prime_three]
  obtain ⟨T, hT2, hBT, hnc⟩ := h _ hBel hBN hcardB
  refine ⟨T.map e.toMonoidHom, hT2.map _, ?_, ?_⟩
  · intro y hy
    have h1 : e.symm y ∈ Subgroup.normalizer (T : Set C) :=
      hBT (Subgroup.mem_map_of_mem e.symm.toMonoidHom hy)
    have h2 : e (e.symm y) ∈ (Subgroup.normalizer (T : Set C)).map e.toMonoidHom :=
      Subgroup.mem_map_of_mem e.toMonoidHom h1
    rw [Subgroup.map_equiv_normalizer_eq T e] at h2
    simpa using h2
  · intro hc
    apply hnc
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have key := Subgroup.mem_centralizer_iff.mp (hc hy) (e t)
      (Subgroup.mem_map_of_mem e.toMonoidHom ht)
    apply e.injective
    simpa [map_mul] using key

theorem A5Abs.of_ffHypA5 {G : Type} [Group G] [Finite G] {b : G} (h : FFHypA5 b) :
    A5Abs ↥(Cen b) := by
  intro B' hB' hT' hcard
  obtain ⟨T', hT'2, hT'1, hB'N⟩ := hT'
  have hBC : B'.map (Cen b).subtype ≤ Cen b := Subgroup.map_subtype_le B'
  have hBel : CFSG.Open.IsElemAbelian 3 (B'.map (Cen b).subtype) := hB'.map _
  have hBN : ∃ T : Subgroup G, T ≤ Cen b ∧ IsPGroup 2 T ∧ T ≠ ⊥ ∧
      B'.map (Cen b).subtype ≤ Subgroup.normalizer (T : Set G) := by
    refine ⟨T'.map (Cen b).subtype, Subgroup.map_subtype_le T', hT'2.map _, ?_, ?_⟩
    · intro h0
      exact hT'1 ((Subgroup.map_eq_bot_iff_of_injective T'
        (f := (Cen b).subtype) (Cen b).subtype_injective).mp h0)
    · exact (Subgroup.map_mono hB'N).trans (Subgroup.le_normalizer_map (Cen b).subtype)
  have hcardB : Nat.card (B'.map (Cen b).subtype) = 3 ^ localRank 3 ↥(Cen b) := by
    rw [Subgroup.card_map_of_injective (f := (Cen b).subtype) (Cen b).subtype_injective]
    exact hcard
  obtain ⟨T, hTC, hT2, hBT, hnc⟩ := h _ hBC hBel hBN hcardB
  refine ⟨T.subgroupOf (Cen b), hT2.comap_of_injective (Cen b).subtype Subtype.coe_injective,
    ?_, ?_⟩
  · intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro n
    have hxN : (x : G) ∈ Subgroup.normalizer (T : Set G) :=
      hBT (Subgroup.mem_map_of_mem (Cen b).subtype hx)
    rw [Subgroup.mem_normalizer_iff] at hxN
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hxN n
  · intro hc
    apply hnc
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have key := Subgroup.mem_centralizer_iff.mp (hc hx) ⟨t, hTC ht⟩
      (Subgroup.mem_subgroupOf.mpr ht)
    have := congrArg Subtype.val key
    simpa using this

theorem ffHypA5_of_A5Abs {G : Type} [Group G] [Finite G] {b : G} (h : A5Abs ↥(Cen b)) :
    FFHypA5 b := by
  intro B hBC hB hT hcard
  obtain ⟨T, hTC, hT2, hT1, hBN⟩ := hT
  have hB' : CFSG.Open.IsElemAbelian 3 (B.subgroupOf (Cen b)) := hB.subgroupOf (Cen b)
  have hcard' : Nat.card (B.subgroupOf (Cen b)) = 3 ^ localRank 3 ↥(Cen b) := by
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv
  have hT' : ∃ T' : Subgroup ↥(Cen b), IsPGroup 2 T' ∧ T' ≠ ⊥ ∧
      B.subgroupOf (Cen b) ≤ Subgroup.normalizer (T' : Set ↥(Cen b)) := by
    refine ⟨T.subgroupOf (Cen b), hT2.comap_of_injective (Cen b).subtype Subtype.coe_injective,
      ?_, ?_⟩
    · intro h0
      apply hT1
      refine eq_bot_iff.mpr fun x hx => ?_
      have : (⟨x, hTC hx⟩ : Cen b) ∈ T.subgroupOf (Cen b) := Subgroup.mem_subgroupOf.mpr hx
      rw [h0, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    · intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro n
      have hxN : (x : G) ∈ Subgroup.normalizer (T : Set G) := hBN (Subgroup.mem_subgroupOf.mp hx)
      rw [Subgroup.mem_normalizer_iff] at hxN
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hxN n
  obtain ⟨T'', hT''2, hBT'', hnc''⟩ := h _ hB' hT' hcard'
  have hBeq : (B.subgroupOf (Cen b)).map (Cen b).subtype = B := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hBC]
  refine ⟨T''.map (Cen b).subtype, Subgroup.map_subtype_le T'', hT''2.map _, ?_, ?_⟩
  · exact hBeq.symm.le.trans
      ((Subgroup.map_mono hBT'').trans (Subgroup.le_normalizer_map (Cen b).subtype))
  · intro hc
    apply hnc''
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have key := Subgroup.mem_centralizer_iff.mp (hc (Subgroup.mem_subgroupOf.mp hx)) (t : G)
      (Subgroup.mem_map_of_mem (Cen b).subtype ht)
    apply Subtype.ext
    simpa using key

end CFSG.RankThree.PartTwo.Sec21.FF81.S58
