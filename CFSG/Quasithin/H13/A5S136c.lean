module

public import CFSG.Quasithin.H13.A6Inputs13_3
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.CharacterTheory.Burnside
public import CFSG.Quasithin.Background.F8G2
public import CFSG.Quasithin.H13.A5F91

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped Pointwise commutatorElement

section Conj

variable {G : Type} [Group G]

theorem ncard_conjSubgroupsBy_eq_index (H K : Subgroup G) :
    (conjSubgroupsBy H K).ncard = ((Subgroup.normalizer (K : Set G)).subgroupOf H).index := by
  let φ : ↥H →* MulAut G := MulAut.conj.comp H.subtype
  let _ : MulAction ↥H (Subgroup G) := MulAction.compHom (Subgroup G) φ
  have hsmul : ∀ (h : ↥H) (X : Subgroup G), h • X = X.map (MulAut.conj (h : G)).toMonoidHom :=
    fun h X => rfl
  have hstab : MulAction.stabilizer ↥H K = (Subgroup.normalizer (K : Set G)).subgroupOf H := by
    ext h
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, hsmul,
      Subgroup.mem_normalizer_iff_map_conj_eq]
    exact Iff.rfl
  have horb : MulAction.orbit ↥H K = conjSubgroupsBy H K := by
    ext X
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h, h.2, hsmul h K⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, hsmul ⟨t, ht⟩ K⟩
  rw [← hstab, MulAction.index_stabilizer, horb]

theorem exists_not_mem_normalizer_of_ncard_two {T H K : Subgroup G} (hT : IsSylowTwoOf T H)
    (hK : (conjSubgroupsBy H K).ncard = 2) :
    ∃ t ∈ T, t ∉ Subgroup.normalizer (K : Set G) := by
  by_contra h
  push Not at h
  rw [ncard_conjSubgroupsBy_eq_index] at hK
  have hle : T.subgroupOf H ≤ (Subgroup.normalizer (K : Set G)).subgroupOf H := fun t ht =>
    Subgroup.mem_subgroupOf.mpr (h t (Subgroup.mem_subgroupOf.mp ht))
  have hdvd := Subgroup.index_dvd_of_le hle
  rw [hK] at hdvd
  exact hT.2.2 hdvd

theorem conjClosure_le_of_two [Finite G] {T H K X : Subgroup G} (hT : IsSylowTwoOf T H)
    (hTX : T ≤ X) (hKH : K ≤ H) (hKX : K ≤ X)
    (hK : (K.subgroupOf H).Normal ∨ (conjSubgroupsBy H K).ncard = 2) :
    conjClosure K H ≤ X := by
  rcases hK with hn | h2
  · refine conjClosure_le fun h hh k hk => hKX ?_
    have := hn.conj_mem ⟨k, hKH hk⟩ (Subgroup.mem_subgroupOf.mpr hk) ⟨h, hh⟩
    exact Subgroup.mem_subgroupOf.mp this
  · obtain ⟨t, htT, htN⟩ := exists_not_mem_normalizer_of_ncard_two hT h2
    set K₁ := K.map (MulAut.conj t).toMonoidHom with hK₁
    have hne : K ≠ K₁ := fun h => htN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm)
    have hsub : ({K, K₁} : Set (Subgroup G)) ⊆ conjSubgroupsBy H K := by
      intro X' hX'
      rcases hX' with rfl | rfl
      · exact ⟨1, H.one_mem, by ext x; simp⟩
      · exact ⟨t, hT.1 htT, rfl⟩
    have hfin : (conjSubgroupsBy H K).Finite := Set.finite_of_ncard_ne_zero (by omega)
    have heq : ({K, K₁} : Set (Subgroup G)) = conjSubgroupsBy H K :=
      Set.eq_of_subset_of_ncard_le hsub (by rw [h2, Set.ncard_pair hne]) hfin
    have hK₁X : K₁ ≤ X := by
      rintro _ ⟨k, hk, rfl⟩
      exact X.mul_mem (X.mul_mem (hTX htT) (hKX hk)) (X.inv_mem (hTX htT))
    refine conjClosure_le fun h hh k hk => ?_
    have hmem : K.map (MulAut.conj h).toMonoidHom ∈ conjSubgroupsBy H K := ⟨h, hh, rfl⟩
    rw [← heq] at hmem
    have hk' : h * k * h⁻¹ ∈ K.map (MulAut.conj h).toMonoidHom := ⟨k, hk, rfl⟩
    rcases hmem with h' | h'
    · rw [h'] at hk'
      exact hKX hk'
    · rw [h'] at hk'
      exact hK₁X hk'

theorem conjClosure_perfect {K H : Subgroup G} (hK : ⁅K, K⁆ = K) :
    ⁅conjClosure K H, conjClosure K H⁆ = conjClosure K H := by
  refine le_antisymm (Subgroup.commutator_le.mpr fun a ha b hb => ?_) ?_
  · rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
      (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
  refine conjClosure_le fun h hh k hk => ?_
  have hKh : K.map (MulAut.conj h).toMonoidHom ≤ conjClosure K H := by
    rintro _ ⟨k', hk', rfl⟩
    exact mem_conjClosure hh hk'
  have hperf : ⁅K.map (MulAut.conj h).toMonoidHom, K.map (MulAut.conj h).toMonoidHom⁆ =
      K.map (MulAut.conj h).toMonoidHom := by
    rw [← Subgroup.map_commutator, hK]
  have hk' : h * k * h⁻¹ ∈ K.map (MulAut.conj h).toMonoidHom := ⟨k, hk, rfl⟩
  rw [← hperf] at hk'
  exact Subgroup.commutator_mono hKh hKh hk'

theorem oTwoUpper_eq_of_perfect' [Finite G] {K : Subgroup G} (hK : ⁅K, K⁆ = K) :
    oTwoUpper K = K := by
  refine le_antisymm (oTwoUpper_le K) ?_
  let N : Subgroup ↥K := (oTwoUpper K).subgroupOf K
  have hN : N.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := conj_mem_oTwoUpper (X := K) (g := (g : G)) (Subgroup.le_normalizer g.2) hn
    simpa using this⟩
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 hK
  have hP : IsPGroup 2 (↥K ⧸ N) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper K g.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hk
  have : Group.IsNilpotent (↥K ⧸ N) := hP.isNilpotent
  have : Subsingleton (↥K ⧸ N) := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isNilpotent (↥K ⧸ N) ‹_›
  intro g hg
  have : (QuotientGroup.mk ⟨g, hg⟩ : ↥K ⧸ N) = 1 := Subsingleton.elim _ _
  rw [QuotientGroup.eq_one_iff] at this
  exact this

theorem isSolvable_of_isTwoThreeGroup [Finite G] {Y : Subgroup G} (hY : A6.IsTwoThreeGroup Y) :
    Group.IsSolvable ↥Y := by
  have : Fintype ↥Y := Fintype.ofFinite _
  have hn0 : Nat.card Y ≠ 0 := Nat.card_pos.ne'
  have hfac : Nat.card Y =
      2 ^ (Nat.card Y).factorization 2 * 3 ^ (Nat.card Y).factorization 3 := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn0]
    rw [Finsupp.prod_of_support_subset _ (s := {2, 3}) ?_ _ (fun _ _ => pow_zero _)]
    · rw [Finset.prod_pair (by norm_num : (2 : ℕ) ≠ 3)]
    · intro p hp
      rw [Nat.support_factorization] at hp
      rcases hY p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp) with
        rfl | rfl <;> simp
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
    (a := (Nat.card Y).factorization 2) (b := (Nat.card Y).factorization 3) Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card]; exact hfac)

end Conj

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem lemma_13_6_26_one (h1338 : A6.Stmt13_3_8) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G}
    (hK : K ∈ cComp H) : ¬ K ≤ Subgroup.normalizer (L : Set G) := by
  intro hKM
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hO2 : pCoreOf 2 H ≠ ⊥ := hH.1.2
  have hHM : ¬ H ≤ Subgroup.normalizer (L : Set G) := hH.2.2
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_le S.h13.sylow hTH
  have hKH : K ≤ H := le_of_mem_cComp hK
  have : IsSimpleGroup G := S.h13.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat S.h13.nonabelian S.h13.qtke).1
  have h121' : (K.subgroupOf H).Normal ∨ (conjSubgroupsBy H K).ncard = 2 := by
    rcases Vol2Native.lemma_1_2_1_three hloc h37 h38 hO2 hK with h | h
    · exact Or.inl h
    · exact Or.inr h.1
  have hYM : conjClosure K H ≤ Subgroup.normalizer (L : Set G) :=
    conjClosure_le_of_two hTsyl S.T_le_NL hKH hKM h121'
  have hYH : conjClosure K H ≤ H := conjClosure_le fun h hh k hk =>
    H.mul_mem (H.mul_mem hh (hKH hk)) (H.inv_mem hh)
  have hYperf : ⁅conjClosure K H, conjClosure K H⁆ = conjClosure K H :=
    conjClosure_perfect (perfect_of_mem_cComp hK)
  have hYO2 : oTwoRes (conjClosure K H) = conjClosure K H := by
    rw [oTwoRes_eq_oTwoUpper]
    exact oTwoUpper_eq_of_perfect' hYperf
  obtain ⟨-, h23⟩ := h1338 G T L L H (conjClosure K H) S.h13 S.h13.faithful ⟨hTH, hO2⟩ hHM hYO2
    hYH (le_normalizer_conjClosure K H) hYM
  have hsolv := isSolvable_of_isTwoThreeGroup h23
  have hKY : K ≤ conjClosure K H := le_conjClosure K H
  exact not_isSolvable_of_mem_cComp hK
    (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKY)
      (Subgroup.inclusion_injective hKY))

end Setting

end CFSG.Quasithin.H13.A5
