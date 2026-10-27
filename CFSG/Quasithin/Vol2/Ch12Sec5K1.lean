module

public import CFSG.Quasithin.Vol2.Ch12Sec5K6

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125

@[expose] def K1Bad125 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (F : Frame125 T L V) (K₁ : Subgroup G),
    Hyp125 G T L V → quasithinIsCComponent K₁ (Subgroup.normalizer (F.V1 : Set G)) →
    li L F.V1 < K₁ → Subgroup.normalizer (F.V1 : Set G) ≤ Subgroup.normalizer (K₁ : Set G) →
    False

namespace S125K1

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem T_le_normalizer_l1 (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    T ≤ Subgroup.normalizer (li L F.V1 : Set G) :=
  S125K6.le_normalizer_li hH.hyp.normalizes
    (S125L2G.T_le_V F (S125Ex.Facts125.of h1222 hH).T_le).1

theorem l1_mem_lFamily (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    li L F.V1 ∈ lFamily T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTL₁ := T_le_normalizer_l1 h1222 F hH
  obtain ⟨e⟩ := S125Fin.lOne_quot_equiv h1222 hH (lemma12_5_2_of h1222 G T L V F hH) hTL₁
  rw [lFamily, Set.mem_ofPred_eq]
  refine mem_cComp_of_quasisimple_quotient (fun N _ hN => ?_)
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm (isQuasisimple_sl_zmod_two (by omega)).1)
    (A3.subnormal_of_normal le_sup_left ?_)
  · have : Group.IsPerfect ↥(li L F.V1) := Subgroup.isPerfect_iff.mpr (S125K6.commutator_li L _)
    by_contra hne
    have : Nontrivial (↥(li L F.V1) ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    have : Group.IsNilpotent (↥(li L F.V1) ⧸ N) := hN.isNilpotent
    exact Group.IsPerfect.not_isNilpotent (↥(li L F.V1) ⧸ N) ‹_›
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    exact sup_le Subgroup.le_normalizer hTL₁

theorem exists_k1 (h1222 : Stmt12_2_2) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    ∃ K₁ : Subgroup G, li L F.V1 ≤ K₁ ∧
      quasithinIsCComponent K₁ (Subgroup.normalizer (F.V1 : Set G)) ∧
      Subgroup.normalizer (F.V1 : Set G) ≤ Subgroup.normalizer (K₁ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf := S125Ex.Facts125.of h1222 hH
  have hyp := hH.hyp
  have hTV₁ : T ≤ Subgroup.normalizer (F.V1 : Set G) := (S125L2G.T_le_V F hf.T_le).1
  have hTL₁ := T_le_normalizer_l1 h1222 F hH
  have hL₁G₁ : li L F.V1 ≤ Subgroup.normalizer (F.V1 : Set G) := S125K6.li_le_normalizer L _
  have hS : QuasithinUnique.IsSylowTwoOf T (Subgroup.normalizer (F.V1 : Set G)) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hTV₁
  have hcard := S125L9a.card_V1 F
  have hO : pCoreOf 2 (Subgroup.normalizer (F.V1 : Set G)) ≠ ⊥ := by
    intro hb
    have h1 := LieType.BorelTits.le_pCoreOf_normalizer 2 F.V1 (IsPGroup.of_card (n := 1)
      (by rw [hcard, pow_one]))
    rw [hb, le_bot_iff] at h1
    rw [h1, Subgroup.card_bot] at hcard
    norm_num at hcard
  have hB := l1_mem_lFamily h1222 F hH
  obtain ⟨K, hK, hLK⟩ := lemma_1_2_4_exists hyp.qtke hyp.simple hyp.nonabelian h37 h39 hO hS
    hL₁G₁ hB
  have hn := lemma_1_2_4_normal hyp.qtke hyp.simple hyp.nonabelian h37 h38 hO hS hB hLK hK hTL₁
  exact ⟨K, hLK, hK,
    (Subgroup.normal_subgroupOf_iff_le_normalizer (A3.subnormal_le hK.2.2.1)).1 hn⟩

theorem l1_cComp_of (h1222 : Stmt12_2_2) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hK₁ : K1Bad125) (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    quasithinIsCComponent (li L F.V1) (Subgroup.normalizer (F.V1 : Set G)) ∧
      Subgroup.normalizer (F.V1 : Set G) ≤ Subgroup.normalizer (li L F.V1 : Set G) := by
  obtain ⟨K₁, hLK, hK, hN⟩ := exists_k1 h1222 h37 h38 h39 F hH
  rcases eq_or_lt_of_le hLK with h | h
  · rw [h]
    exact ⟨hK, hN⟩
  · exact (hK₁ G T L V F K₁ hH hK h hN).elim

end S125K1

end CFSG.Quasithin.H13
