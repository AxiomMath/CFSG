module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P2Idx
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223Ord3
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P2V2Lift

public section

namespace CFSG.Quasithin.S15223

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_eq_of_block {I S X : Subgroup G}
    (hC19 : DistinctBlocksCommuteStatement (G := G)) (hchar : CharTwo I)
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥I) ≤ 2) (hS : IsSylowTwoOf S I)
    (hX : IsBlock2 I X) (hX3 : 3 ∣ Nat.card X) :
    ∀ g ∈ I, ∃ s ∈ S, conjByElt g X = conjByElt s X := by
  intro g hg
  set N : Subgroup G := Subgroup.normalizer (X : Set G) ⊓ I with hN
  have hidx : (N.subgroupOf I).index ≤ 2 := index_normalizer_le_two hC19 hchar hrank hX hX3
  by_cases hgN : g ∈ N
  · refine ⟨1, S.one_mem, ?_⟩
    rw [C2Eleven.conjByElt_one]
    exact C2Eleven.mem_normalizer_iff_conjByElt.1 hgN.1
  ·
    have hidx2 : (N.subgroupOf I).index = 2 := by
      have hpos : 0 < (N.subgroupOf I).index :=
        Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
      have hne1 : (N.subgroupOf I).index ≠ 1 := by
        intro h1
        have hIN : I ≤ N := Subgroup.subgroupOf_eq_top.mp (Subgroup.index_eq_one.mp h1)
        exact hgN (hIN hg)
      omega
    obtain ⟨s, hsS, hsN⟩ : ∃ s ∈ S, s ∉ N := by
      by_contra hcon
      push Not at hcon
      have hSN : S ≤ N := fun s hs => hcon s hs
      have h1 := Subgroup.relIndex_mul_relIndex S N I hSN inf_le_right
      have h2 : 2 ∣ S.relIndex I := by
        rw [← h1]
        exact Dvd.dvd.mul_left (by rw [Subgroup.relIndex, hidx2]) _
      exact hS.2.2 h2
    have hsI : s ∈ I := hS.1 hsS
    have hor := mem_of_index_le_two hidx (1 : ↥I) ⟨g, hg⟩ ⟨s, hsI⟩
    have hgs : g⁻¹ * s ∈ N := by
      rcases hor with h | h | h
      · exact absurd (by simpa using Subgroup.mem_subgroupOf.mp h) hgN
      · exact absurd (by simpa using Subgroup.mem_subgroupOf.mp h) hsN
      · simpa using Subgroup.mem_subgroupOf.mp h
    refine ⟨s, hsS, ?_⟩
    have h3 : conjByElt (g⁻¹ * s) X = X := C2Eleven.mem_normalizer_iff_conjByElt.1 hgs.1
    calc conjByElt g X = conjByElt g (conjByElt (g⁻¹ * s) X) := by rw [h3]
      _ = conjByElt (g * (g⁻¹ * s)) X := (C2Eleven.conjByElt_mul _ _ _).symm
      _ = conjByElt s X := by rw [mul_inv_cancel_left]

omit [Finite G] in
theorem conj_le_normalizer_of_block {I X : Subgroup G}
    (hC19 : DistinctBlocksCommuteStatement (G := G)) (hchar : CharTwo I) (hX : IsBlock2 I X)
    {g : G} (hg : g ∈ I) : conjByElt g X ≤ Subgroup.normalizer (X : Set G) := by
  by_cases hne : conjByElt g X = X
  · rw [hne]
    exact Subgroup.le_normalizer
  · have hX' : IsBlock2 I (conjByElt g X) :=
      isBlock2_conjByElt_of_normalizer1515c hX (Subgroup.le_normalizer hg)
    have h := hC19 I X (conjByElt g X) hchar hX hX' (Ne.symm hne)
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h
    exact h.trans (Subgroup.centralizer_le_normalizer _)

theorem not_le_of_block {I S X Mc K : Subgroup G}
    (hC19 : DistinctBlocksCommuteStatement (G := G)) (hchar : CharTwo I)
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥I) ≤ 2) (hS : IsSylowTwoOf S I)
    (hX : IsBlock2 I X) (hX3 : 3 ∣ Nat.card X) (hSMc : S ≤ Mc)
    (hP1 : ∀ Y : Subgroup G, GenByOrderThree Y → Y ≤ I →
      I ≤ Subgroup.normalizer (Y : Set G) → Y ≤ Mc → ¬ Y ≤ K → quasithinV2 Y = ⊥)
    (hKsolv : Group.IsSolvable ↥K) (hgen : GenByOrderThree X)
    (hns : ¬ Group.IsSolvable ↥X) (hV2 : quasithinV2 X ≠ ⊥) : ¬ X ≤ Mc := by
  intro hXMc
  have hres : X = oPrimeResidualOf 3 X := hgen.eq_oPrimeResidualOf
  have hXI : X ≤ I := hX.2.1
  have hconj := exists_conj_eq_of_block hC19 hchar hrank hS hX hX3
  set X₀ := conjClosure X I with hX₀
  have hX₀I : X₀ ≤ I := conjClosure_le fun g hg x hx =>
    I.mul_mem (I.mul_mem hg (hXI hx)) (I.inv_mem hg)
  have hIN : I ≤ Subgroup.normalizer (X₀ : Set G) := le_normalizer_conjClosure X I
  have hXX₀ : X ≤ X₀ := le_conjClosure X I
  have hX₀Mc : X₀ ≤ Mc := conjClosure_le fun g hg x hx => by
    obtain ⟨s, hs, hgs⟩ := hconj g hg
    have h1 : g * x * g⁻¹ ∈ conjByElt s X := hgs ▸ C2Eleven.conj_mem_conjByElt hx
    have h2 : s⁻¹ * (g * x * g⁻¹) * s ∈ X := mem_conjByElt.mp h1
    have h3 : s * (s⁻¹ * (g * x * g⁻¹) * s) * s⁻¹ ∈ Mc :=
      Mc.mul_mem (Mc.mul_mem (hSMc hs) (hXMc h2)) (Mc.inv_mem (hSMc hs))
    simpa [mul_assoc] using h3
  have hX₀N : X₀ ≤ Subgroup.normalizer (X : Set G) := conjClosure_le fun g hg x hx =>
    conj_le_normalizer_of_block hC19 hchar hX hg (C2Eleven.conj_mem_conjByElt hx)
  have hgen' : GenByOrderThree X₀ := genByOrderThree_conjClosure hgen
  have hXK : ¬ X₀ ≤ K := by
    intro h
    exact hns (Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (hXX₀.trans h) : Function.Injective
        (Subgroup.inclusion (hXX₀.trans h))))
  have hV := hP1 X₀ hgen' hX₀I hIN hX₀Mc hXK
  exact quasithinV2_ne_bot_of_normal hres hXX₀ hX₀N hV2 hV

end CFSG.Quasithin.S15223
