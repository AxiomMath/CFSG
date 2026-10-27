module

public import CFSG.LocalAnalysis.StandardType.GGK1CCoDefs
public import CFSG.LocalAnalysis.StandardType.GGK1CBlDefs
public import CFSG.LocalAnalysis.StandardType.GGK1CBlIdx
public import CFSG.LocalAnalysis.StandardType.GGK1CBlRank

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.Classical (spEnd IsReciprocalTransversal SpPrimaryBlocks spSupported
  symplectic_cross_prime_primary_centralizer_blocks spForm spForm_isAlt spEnd_pow
  altPrimaryData_spLin SpSelfDualBlock primaryComponent_eq_bot_of_not_mem
  irreducible_X_sub_one monic_X_sub_one reciprocalPolynomial_X_sub_one reciprocalOrbits)
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

private theorem ggK1D2_univ_sum_map {α β γ : Type*} [Fintype α] [Fintype β]
    (g : α ⊕ β → γ) :
    (Finset.univ : Finset (α ⊕ β)).val.map g =
      (Finset.univ : Finset α).val.map (fun a => g (Sum.inl a)) +
      (Finset.univ : Finset β).val.map (fun b => g (Sum.inr b)) := by
  have h1 : (Finset.univ : Finset (α ⊕ β)) =
      (Finset.univ.map Function.Embedding.inl).disjUnion (Finset.univ.map Function.Embedding.inr)
        (Finset.disjoint_map_inl_map_inr _ _) := by
    rw [Finset.map_inl_disjUnion_map_inr, Finset.univ_disjSum_univ]
  rw [h1, Finset.disjUnion_val, Finset.map_val, Finset.map_val, Multiset.map_add,
    Multiset.map_map, Multiset.map_map]
  rfl

private theorem ggK1D2_univ_subtype_unit_map {γ : Type*} (c : Prop) [Decidable c]
    (f : Subtype (fun _ : Unit => c) → γ) :
    (Finset.univ : Finset (Subtype (fun _ : Unit => c))).val.map f =
      if h : c then {f ⟨(), h⟩} else 0 := by
  by_cases h : c
  · haveI : Subsingleton (Subtype (fun _ : Unit => c)) := inferInstance
    rw [← Finset.singleton_eq_univ (⟨(), h⟩ : Subtype (fun _ : Unit => c))]
    simp [h]
  · haveI : IsEmpty (Subtype (fun _ : Unit => c)) := ⟨fun x => h x.2⟩
    rw [Finset.univ_eq_empty]
    simp [h]

private theorem ggK1D2_charP_two {K : Type} [Field K] [Finite K] {nf : ℕ}
    (hK : Nat.card K = 2 ^ nf) : CharP K 2 := by
  haveI : Fintype K := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (p := 2) (f := nf)
    (by rw [← Nat.card_eq_fintype_card]; exact hK)

private theorem ggK1D2_prime_ne_two {p nf : ℕ} (hnf : 1 ≤ nf)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1) : p ≠ 2 := by
  rintro rfl
  have hpos : 1 ≤ 2 ^ nf := Nat.one_le_two_pow
  have h2n : 2 ∣ 2 ^ nf := dvd_pow_self 2 (by omega)
  rcases hdvd with h | h
  · have h1 : 2 ∣ 1 := by
      have := Nat.dvd_sub h2n h
      rwa [show 2 ^ nf - (2 ^ nf - 1) = 1 by omega] at this
    exact Nat.prime_two.not_dvd_one h1
  · have h1 : 2 ∣ 1 := by
      have := Nat.dvd_sub h h2n
      rwa [show 2 ^ nf + 1 - 2 ^ nf = 1 by omega] at this
    exact Nat.prime_two.not_dvd_one h1

private theorem ggK1D2_prime_cast_ne_zero {K : Type} [Field K] [Finite K] {p nf : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = 2 ^ nf) : (p : K) ≠ 0 := by
  haveI : CharP K 2 := ggK1D2_charP_two hK
  intro h
  rw [CharP.cast_eq_zero_iff K 2 p] at h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h).symm

private theorem ggK1D2_primaryMultiplicity_pos {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {x : Module.End K V}
    (hsq : Squarefree (minpoly K x)) {h : K[X]} (hh : h ∈ primaryFactors x) :
    0 < primaryMultiplicity x h := by
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  haveI : Nontrivial (primaryComponent x h) :=
    Submodule.nontrivial_iff_ne_bot.mpr (primaryComponent_ne_bot hsq hh)
  exact Module.finrank_pos

private theorem ggK1D2_squarefree_spEnd {p nf r : ℕ} {K : Type} [Field K] [Finite K]
    {x : ↥(StatedSp r K)} (hp : p.Prime) (hnf : 1 ≤ nf)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1) (hK : Nat.card K = 2 ^ nf)
    (hx : x ^ p = 1) : Squarefree (minpoly K (spEnd x)) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hpK : (p : K) ≠ 0 :=
    ggK1D2_prime_cast_ne_zero hp (ggK1D2_prime_ne_two hnf hdvd) hK
  exact (altPrimaryData_spLin hpK hx).squarefree

private theorem ggK1D2_mem_X1_of_headD_ne_zero {p nf r : ℕ} {K : Type} [Field K]
    {x : ↥(StatedSp r K)} {m : List ℕ} (hm : GGK1CMultOf p nf 2 r K x m)
    (h0 : m.headD 0 ≠ 0) : (X - 1 : K[X]) ∈ primaryFactors (spEnd x) := by
  by_contra hmem
  apply h0
  rw [hm.head_eq,
    primaryComponent_eq_bot_of_not_mem irreducible_X_sub_one monic_X_sub_one hmem, finrank_bot]

private theorem ggK1D2_headD_ne_zero_of_mem_X1 {p nf r : ℕ} {K : Type} [Field K] [Finite K]
    {x : ↥(StatedSp r K)} {m : List ℕ} (hm : GGK1CMultOf p nf 2 r K x m)
    (hSq : Squarefree (minpoly K (spEnd x)))
    (hblocks : SpPrimaryBlocks 2 nf p x (proj r K x))
    (hmem : (X - 1 : K[X]) ∈ primaryFactors (spEnd x)) : m.headD 0 ≠ 0 := by
  intro h0
  have hcomp : primaryComponent (spEnd x) (X - 1) ≠ ⊥ :=
    primaryComponent_ne_bot hSq hmem
  haveI : Nontrivial (primaryComponent (spEnd x) (X - 1)) :=
    Submodule.nontrivial_iff_ne_bot.mpr hcomp
  have hpos : 0 < Module.finrank K (primaryComponent (spEnd x) (X - 1)) :=
    Module.finrank_pos
  obtain ⟨s, hs, -⟩ := hblocks.rank
  rw [hm.head_eq, hs, Nat.mul_div_cancel_left s (by norm_num : 0 < 2)] at h0
  omega

theorem ggK1CBl_comm_join_d2 {p nf r : ℕ} {K : Type} [Field K] [Finite K]
    {x : ↥(StatedSp r K)} {m : List ℕ}
    (hnf : 1 ≤ nf) (hp : p.Prime) (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (hK : Nat.card K = 2 ^ nf) (hx : x ^ p = 1)
    (hm : GGK1CMultOf p nf 2 r K x m)
    (hblocks : SpPrimaryBlocks 2 nf p x (proj r K x)) :
    (∀ i j : ggK1CBl_Id2 K x m, i ≠ j →
        ∀ a ∈ ggK1CBl_A2 x m i, ∀ b ∈ ggK1CBl_A2 x m j, Commute a b) ∧
      (⨆ i : ggK1CBl_Id2 K x m, ggK1CBl_A2 x m i) =
        Subgroup.centralizer ({x} : Set (StatedSp r K)) ∧
      iSupIndep (ggK1CBl_A2 x m) := by
  classical
  have hSq : Squarefree (minpoly K (spEnd x)) := ggK1D2_squarefree_spEnd hp hnf hdvd hK hx
  have hrank := ggK1CBl_rank_d2 hdvd hK hm hblocks
  have hmemT : ∀ h : K[X], h ∈ ggK1CSelfDualFactors x ↔
      h ∈ primaryFactors (spEnd x) ∧ h ≠ X - 1 := by
    intro h
    unfold ggK1CSelfDualFactors
    exact Finset.mem_filter
  let B : reciprocalOrbits (spEnd x) → Subgroup (StatedSp r K) :=
    fun O => spSupported x (O : Set K[X])
  have hmemOrb : ∀ h : ↥(ggK1CSelfDualFactors x),
      ({h.1} : Set K[X]) ∈ reciprocalOrbits (spEnd x) := by
    intro h
    unfold reciprocalOrbits
    refine ⟨h.1, ((hmemT h.1).mp h.2).1, ?_⟩
    change ({h.1, reciprocalPolynomial h.1} : Set K[X]) = {h.1}
    rw [hrank.2.1 h.1 ((hmemT h.1).mp h.2).1 ((hmemT h.1).mp h.2).2]
    simp
  have hmemOrbX1 : ∀ u : Subtype (fun _ : Unit => m.headD 0 ≠ 0),
      ({X - 1} : Set K[X]) ∈ reciprocalOrbits (spEnd x) := by
    intro u
    unfold reciprocalOrbits
    refine ⟨X - 1, ggK1D2_mem_X1_of_headD_ne_zero hm u.2, ?_⟩
    change ({X - 1, reciprocalPolynomial (X - 1)} : Set K[X]) = {X - 1}
    rw [reciprocalPolynomial_X_sub_one]
    simp
  let Φ : ggK1CBl_Id2 K x m → reciprocalOrbits (spEnd x) :=
    Sum.elim (fun h => ⟨{h.1}, hmemOrb h⟩) (fun u => ⟨{X - 1}, hmemOrbX1 u⟩)
  have hA : ∀ i, ggK1CBl_A2 x m i = B (Φ i) := by
    intro i
    cases i with
    | inl h =>
      show spSupported x ({h.1} : Set K[X]) = spSupported x ({h.1} : Set K[X])
      rfl
    | inr u =>
      show spSupported x ({X - 1} : Set K[X]) = spSupported x ({X - 1} : Set K[X])
      rfl
  have hΦinj : Function.Injective Φ := by
    intro i j hij
    cases i with
    | inl h =>
      cases j with
      | inl h' =>
        have hset : ({h.1} : Set K[X]) = {h'.1} := by
          have := congrArg Subtype.val hij
          change ({h.1} : Set K[X]) = {h'.1} at this
          exact this
        have heq : h = h' := Subtype.ext (Set.singleton_eq_singleton_iff.mp hset)
        rw [heq]
      | inr u =>
        have hset : ({h.1} : Set K[X]) = {X - 1} := by
          have := congrArg Subtype.val hij
          change ({h.1} : Set K[X]) = {X - 1} at this
          exact this
        exfalso
        exact ((hmemT h.1).mp h.2).2 (Set.singleton_eq_singleton_iff.mp hset)
    | inr u =>
      cases j with
      | inl h =>
        have hset : ({X - 1} : Set K[X]) = {h.1} := by
          have := congrArg Subtype.val hij
          change ({X - 1} : Set K[X]) = {h.1} at this
          exact this
        exfalso
        exact ((hmemT h.1).mp h.2).2 (Set.singleton_eq_singleton_iff.mp hset).symm
      | inr u' =>
        have heq : u = u' := Subsingleton.elim u u'
        rw [heq]
  have hΦsurj : Function.Surjective Φ := by
    rintro ⟨O, hO⟩
    unfold reciprocalOrbits at hO
    obtain ⟨h, hh, hfeq⟩ := hO
    subst O
    simp only []
    by_cases hX1 : h = X - 1
    · subst hX1
      refine ⟨Sum.inr ⟨(), ggK1D2_headD_ne_zero_of_mem_X1 hm hSq hblocks hh⟩, ?_⟩
      apply Subtype.ext
      show ({X - 1} : Set K[X]) = ({X - 1, reciprocalPolynomial (X - 1)} : Set K[X])
      rw [reciprocalPolynomial_X_sub_one, Set.pair_eq_singleton]
    · have hself : reciprocalPolynomial h = h := hrank.2.1 h hh hX1
      refine ⟨Sum.inl ⟨h, (hmemT h).mpr ⟨hh, hX1⟩⟩, ?_⟩
      apply Subtype.ext
      show ({h} : Set K[X]) = ({h, reciprocalPolynomial h} : Set K[X])
      rw [hself, Set.pair_eq_singleton]
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij a ha b hb
    rw [hA i] at ha
    rw [hA j] at hb
    exact hblocks.directProduct.1 (Φ i) (Φ i).2 (Φ j) (Φ j).2
      (fun h => hij (hΦinj (Subtype.ext h))) a ha b hb
  · rw [iSup_congr hA]
    have h1 : (⨆ i, B (Φ i)) = ⨆ O, B O := by
      apply le_antisymm
      · exact iSup_le fun i => le_iSup B (Φ i)
      · refine iSup_le fun O => ?_
        obtain ⟨i, rfl⟩ := hΦsurj O
        exact le_iSup (fun i => B (Φ i)) i
    rw [h1]
    exact hblocks.directProduct.2.2
  · rw [show ggK1CBl_A2 x m = B ∘ Φ from funext hA]
    exact hblocks.directProduct.2.1.comp hΦinj

theorem ggK1CBl_witness_d2 {p nf r : ℕ} {K : Type} [Field K] [Finite K]
    {x : ↥(StatedSp r K)} {m : List ℕ}
    (hnf : 1 ≤ nf) (hp : p.Prime) (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (hK : Nat.card K = 2 ^ nf) (hx : x ^ p = 1)
    (hm : GGK1CMultOf p nf 2 r K x m)
    (hblocks : SpPrimaryBlocks 2 nf p x (proj r K x)) :
    ∀ i : ggK1CBl_Id2 K x m,
      ggK1CBl_KindWitness nf K (ggK1CBl_kind2 x m i) (ggK1CBl_A2 x m i) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hSq : Squarefree (minpoly K (spEnd x)) := ggK1D2_squarefree_spEnd hp hnf hdvd hK hx
  have hrank := ggK1CBl_rank_d2 hdvd hK hm hblocks
  have hmemT : ∀ h : K[X], h ∈ ggK1CSelfDualFactors x ↔
      h ∈ primaryFactors (spEnd x) ∧ h ≠ X - 1 := by
    intro h
    unfold ggK1CSelfDualFactors
    exact Finset.mem_filter
  intro i
  cases i with
  | inl h =>
    have hmem : h.1 ∈ primaryFactors (spEnd x) := ((hmemT h.1).mp h.2).1
    have hne : h.1 ≠ X - 1 := ((hmemT h.1).mp h.2).2
    have hself : reciprocalPolynomial h.1 = h.1 := hrank.2.1 h.1 hmem hne
    have hdeg2 : h.1.natDegree = 2 := hrank.2.2 h.1 hmem hne
    let h' : primaryFactors (spEnd x) := ⟨h.1, hmem⟩
    have hsd : SpSelfDualBlock 2 nf p x h' :=
      hblocks.selfDual h' hne hself
    obtain ⟨d, hd, hpvd, σ, hσpow, hσne, hσinv, hσroot, hσform, hE, hEbar, Hf,
      hHfsymm, hHfsep, htail⟩ := hsd.exists_half
    obtain ⟨hηblock, hrest⟩ := htail
    obtain ⟨η, hηne, hηbar, hηform⟩ := hηblock
    obtain ⟨heblock, hφblock⟩ := hrest
    obtain ⟨e, he⟩ := heblock
    obtain ⟨φ, hφ⟩ := hφblock
    have hd1 : d = 1 := by
      have : h.1.natDegree = 2 * d := by simpa using hd
      omega
    have hmul : nf * d = nf := by rw [hd1, Nat.mul_one]
    haveI : Finite (AdjoinRoot h.1) := hE.finite
    haveI : Fintype (AdjoinRoot h.1) := Fintype.ofFinite _
    unfold ggK1CBl_KindWitness
    rw [← hmul]
    refine ⟨?_, AdjoinRoot (h' : K[X]), inferInstance, inferInstance, hE,
      primaryComponent (spEnd x) (h' : K[X]), inferInstance, inferInstance, inferInstance, Hf,
      hHfsymm, hHfsep, ⟨e, he⟩, ⟨φ⟩⟩
    exact Nat.one_le_iff_ne_zero.mpr
      (ne_of_gt (ggK1D2_primaryMultiplicity_pos hSq hmem))
  | inr u =>
    have hmemX1 : (X - 1 : K[X]) ∈ primaryFactors (spEnd x) :=
      ggK1D2_mem_X1_of_headD_ne_zero hm u.2
    obtain ⟨s, hs, -⟩ := hblocks.rank
    refine ⟨?_, primaryComponent (spEnd x) (X - 1), inferInstance, inferInstance,
      inferInstance, (spForm r K).restrict (primaryComponent (spEnd x) (X - 1)),
      ?_, hblocks.fixed_nondegenerate, ?_, ?_⟩
    · exact Nat.one_le_iff_ne_zero.mpr u.2
    · intro v
      exact spForm_isAlt (v : Fin r ⊕ Fin r → K)
    · rw [hm.head_eq, hs, Nat.mul_div_cancel_left s (by norm_num : 0 < 2)]
    · obtain ⟨φ, -⟩ := hblocks.fixedFactor hmemX1
      exact ⟨φ⟩

theorem ggK1CBl_kind_multiset_d2 {p nf r : ℕ} {K : Type} [Field K]
    {x : ↥(StatedSp r K)} {m : List ℕ}
    (hm : GGK1CMultOf p nf 2 r K x m)
    (hmult : Multiset.ofList (m.tail.filter (fun j => decide (j ≠ 0))) =
      (ggK1CSelfDualFactors x).val.map (primaryMultiplicity (spEnd x))) :
    (Finset.univ : Finset (ggK1CBl_Id2 K x m)).val.map (ggK1CBl_kind2 x m) =
      ggK1CCo_expectedKinds p nf 2 m := by
  classical
  rw [ggK1D2_univ_sum_map (α := ↥(ggK1CSelfDualFactors x))
    (β := Subtype (fun _ : Unit => m.headD 0 ≠ 0)) (g := ggK1CBl_kind2 x m)]
  have hExp : ggK1CCo_expectedKinds p nf 2 m =
      (↑(if m.headD 0 = 0 then [] else [ggK1CCo_Kind.sp (m.headD 0)]) :
          Multiset ggK1CCo_Kind) +
      ↑(((List.range ((p - 1) / 2 + 1)).filter
          (fun j => decide (1 ≤ j ∧ 1 ≤ m.getD j 0))).map
          (fun j => ggK1CCo_Kind.su (m.getD j 0))) := by
    rw [ggK1CCo_expectedKinds, ggK1CCo_expectedKindList, Multiset.coe_add]
    rfl
  have hA : (Finset.univ : Finset ↥(ggK1CSelfDualFactors x)).val.map
        (fun h => ggK1CCo_Kind.su (primaryMultiplicity (spEnd x) h.1)) =
      (↑(((List.range ((p - 1) / 2 + 1)).filter
          (fun j => decide (1 ≤ j ∧ 1 ≤ m.getD j 0))).map
          (fun j => ggK1CCo_Kind.su (m.getD j 0))) : Multiset ggK1CCo_Kind) := by
    rw [ggK1CBl_univ_map_subtype_val (ggK1CSelfDualFactors x)
      (fun h => ggK1CCo_Kind.su (primaryMultiplicity (spEnd x) h))]
    rw [show (ggK1CSelfDualFactors x).val.map
          (fun h => ggK1CCo_Kind.su (primaryMultiplicity (spEnd x) h))
        = (ggK1CSelfDualFactors x).val.map
            (ggK1CCo_Kind.su ∘ primaryMultiplicity (spEnd x)) from rfl]
    rw [← Multiset.map_map]
    rw [← hmult]
    rw [Multiset.map_coe]
    congr 1
    rw [← hm.length_eq]
    rw [ggK1CBl_tail_filter_map m (fun j => ggK1CCo_Kind.su j)]
    rw [List.drop_one]
  have hB : (Finset.univ : Finset (Subtype (fun _ : Unit => m.headD 0 ≠ 0))).val.map
        (fun _ => ggK1CCo_Kind.sp (m.headD 0)) =
      (↑(if m.headD 0 = 0 then [] else [ggK1CCo_Kind.sp (m.headD 0)]) :
        Multiset ggK1CCo_Kind) := by
    rw [ggK1D2_univ_subtype_unit_map (c := m.headD 0 ≠ 0)
      (f := fun _ => ggK1CCo_Kind.sp (m.headD 0))]
    by_cases h0 : m.headD 0 = 0
    · have hc : ¬ (m.headD 0 ≠ 0) := fun h => h h0
      rw [dif_neg hc, if_pos h0, Multiset.coe_nil]
    · have hc : m.headD 0 ≠ 0 := h0
      rw [dif_pos hc, if_neg h0, Multiset.coe_singleton]
  change (Finset.univ : Finset ↥(ggK1CSelfDualFactors x)).val.map
        (fun h => ggK1CCo_Kind.su (primaryMultiplicity (spEnd x) h.1)) +
      (Finset.univ : Finset (Subtype (fun _ : Unit => m.headD 0 ≠ 0))).val.map
        (fun _ => ggK1CCo_Kind.sp (m.headD 0)) = ggK1CCo_expectedKinds p nf 2 m
  rw [hExp, hA, hB, add_comm]

end CFSG.StandardType

end
