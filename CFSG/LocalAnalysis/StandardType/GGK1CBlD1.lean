module

public import CFSG.LocalAnalysis.StandardType.GGK1CCoDefs
public import CFSG.LocalAnalysis.StandardType.GGK1CBlDefs
public import CFSG.LocalAnalysis.StandardType.GGK1CBlIdx
public import CFSG.LocalAnalysis.StandardType.GGK1CBlRank

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.Classical (spEnd spForm spForm_isAlt IsReciprocalTransversal SpPrimaryBlocks
  spSupported reciprocalOrbits symplectic_cross_prime_primary_centralizer_blocks)
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)
open _root_.Classical

private lemma ggK1D1_selfDualSum_zero {p nf r : ℕ} {K : Type} [Field K] [Finite K]
    {x : ↥(StatedSp r K)} {m : List ℕ} {P₀ : Finset K[X]}
    (hm : GGK1CMultOf p nf 1 r K x m) (hP₀ : IsReciprocalTransversal (spEnd x) P₀)
    (hmult₀ : Multiset.ofList (m.tail.filter (fun j => decide (j ≠ 0))) =
      P₀.val.map (primaryMultiplicity (spEnd x)))
    (hblocks : SpPrimaryBlocks 2 nf p x (proj r K x)) :
    (∑ h ∈ (primaryFactors (spEnd x)).filter
        (fun h => reciprocalPolynomial h = h ∧ h ≠ X - 1),
        h.natDegree / 2 * primaryMultiplicity (spEnd x) h) = 0 := by
  classical
  obtain ⟨s, hs, -, hrank⟩ := hblocks.rank
  have hm0 : m.headD 0 = s := by rw [hm.head_eq, hs]; omega
  have hfilter : ∀ l : List ℕ, (l.filter (fun j => decide (j ≠ 0))).sum = l.sum := by
    intro l
    induction l with
    | nil => rfl
    | cons a t ih =>
        by_cases ha : a = 0
        · subst ha
          rw [List.filter_cons_of_neg (p := fun j : ℕ => decide (j ≠ 0)) (by decide)]
          simp only [List.sum_cons, zero_add]
          exact ih
        · rw [List.filter_cons_of_pos (p := fun j : ℕ => decide (j ≠ 0))
            (decide_eq_true_eq.mpr ha)]
          simp only [List.sum_cons]
          rw [ih]
  have htail : (m.tail.filter (fun j => decide (j ≠ 0))).sum =
      ∑ h ∈ P₀, primaryMultiplicity (spEnd x) h := by
    have h2 : (Multiset.ofList (m.tail.filter (fun j => decide (j ≠ 0)))).sum =
        (P₀.val.map (primaryMultiplicity (spEnd x))).sum := congrArg Multiset.sum hmult₀
    simpa using h2
  have hmsum : m.sum = m.headD 0 + (m.tail.filter (fun j => decide (j ≠ 0))).sum := by
    cases m with
    | nil => simp
    | cons a t =>
        simp only [List.sum_cons, List.headD_cons, List.tail_cons]
        rw [hfilter t]
  have hr := hrank P₀ hP₀
  have hr2 : r = s + ∑ h ∈ P₀, primaryMultiplicity (spEnd x) h := by
    have h2 : m.sum = s + ∑ h ∈ P₀, primaryMultiplicity (spEnd x) h := by
      rw [hmsum, hm0, htail]
    exact hm.sum_eq.symm.trans h2
  have hCA : (∑ h ∈ P₀, primaryMultiplicity (spEnd x) h) ≤
      ∑ h ∈ P₀, h.natDegree * primaryMultiplicity (spEnd x) h := by
    apply Finset.sum_le_sum
    intro h hh
    have h1 : 1 ≤ h.natDegree := by
      have h0 : h.natDegree ≠ 0 := fun h0 =>
        (irreducible_of_mem_primaryFactors (hP₀.1 h hh).1).not_isUnit
          (CFSG.RankThree.PartOne.KCOrthogonal.isUnit_of_natDegree_eq_zero_of_ne_zero
            (irreducible_of_mem_primaryFactors (hP₀.1 h hh).1).ne_zero h0)
      omega
    calc primaryMultiplicity (spEnd x) h = 1 * primaryMultiplicity (spEnd x) h := (one_mul _).symm
      _ ≤ h.natDegree * primaryMultiplicity (spEnd x) h :=
          Nat.mul_le_mul_right _ h1
  have hB0 : (∑ h ∈ (primaryFactors (spEnd x)).filter
      (fun h => reciprocalPolynomial h = h ∧ h ≠ X - 1),
      h.natDegree / 2 * primaryMultiplicity (spEnd x) h) = 0 := by
    omega
  exact hB0

private lemma ggK1D1_primaryComponent_ne_bot {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {y : Module.End K V} {a : K[X]} (hirr : Irreducible a) (hmon : a.Monic)
    (hdvd : a ∣ minpoly K y) : primaryComponent y a ≠ ⊥ := by
  intro hbot
  have hinj : Function.Injective (aeval y a) := by
    rw [← LinearMap.ker_eq_bot]
    exact hbot
  have hbij : Function.Bijective (aeval y a) :=
    ⟨hinj, (LinearMap.injective_iff_surjective).mp hinj⟩
  have hunit : IsUnit (aeval y a) := (Module.End.isUnit_iff _).mpr hbij
  obtain ⟨b, hb⟩ := hdvd
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hb
    exact minpoly_ne_zero y hb
  have hzero : aeval y a * aeval y b = 0 := by
    rw [← map_mul, ← hb, minpoly.aeval]
  have hq0 : aeval y b = 0 := (IsUnit.mul_right_eq_zero hunit).mp hzero
  have hdvd2 : minpoly K y ∣ b := minpoly.dvd K y hq0
  have hlt : b.natDegree < (minpoly K y).natDegree := by
    rw [hb, natDegree_mul hmon.ne_zero hb0]
    have ha0 : a.natDegree ≠ 0 := fun h =>
      hirr.not_isUnit
        (CFSG.RankThree.PartOne.KCOrthogonal.isUnit_of_natDegree_eq_zero_of_ne_zero hirr.ne_zero h)
    have ha1 : 0 < a.natDegree := Nat.pos_of_ne_zero ha0
    omega
  exact (Polynomial.not_dvd_of_natDegree_lt hb0 hlt) hdvd2

private lemma ggK1D1_primaryMultiplicity_pos {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {y : Module.End K V} {a : K[X]}
    (ha : a ∈ primaryFactors y) : 1 ≤ primaryMultiplicity y a := by
  haveI : Fact (Irreducible a) := ⟨irreducible_of_mem_primaryFactors ha⟩
  have hne : primaryComponent y a ≠ ⊥ :=
    ggK1D1_primaryComponent_ne_bot (irreducible_of_mem_primaryFactors ha)
      (monic_of_mem_primaryFactors ha) (mem_primaryFactors.mp ha).2.2
  haveI : Nontrivial ↥(primaryComponent y a) := Submodule.nontrivial_iff_ne_bot.mpr hne
  change 1 ≤ Module.finrank (AdjoinRoot a) (primaryComponent y a)
  exact Module.finrank_pos_iff.mpr inferInstance

private lemma ggK1D1_coeff_zero_ne_of_reciprocal_ne_zero {K : Type} [Field K] {h : K[X]}
    (hne : reciprocalPolynomial h ≠ 0) : h.coeff 0 ≠ 0 := by
  intro hc
  exact hne (by rw [reciprocalPolynomial, hc, inv_zero, C_0, zero_mul])

private lemma ggK1D1_reciprocal_reciprocal {K : Type} [Field K] {h : K[X]} (hmon : h.Monic)
    (h0 : h.coeff 0 ≠ 0) : reciprocalPolynomial (reciprocalPolynomial h) = h :=
  CFSG.RankThree.PartOne.KCOrthogonal.reciprocalPolynomial_reciprocalPolynomial hmon h0

private lemma ggK1D1_headD_ne_zero_of_mem_X_sub_one {p nf r : ℕ} {K : Type} [Field K] [Finite K]
    {x : ↥(StatedSp r K)} {m : List ℕ}
    (hm : GGK1CMultOf p nf 1 r K x m) (hblocks : SpPrimaryBlocks 2 nf p x (proj r K x))
    (hX : (X - 1 : K[X]) ∈ primaryFactors (spEnd x)) : m.headD 0 ≠ 0 := by
  intro h0
  have hne : primaryComponent (spEnd x) (X - 1) ≠ ⊥ :=
    ggK1D1_primaryComponent_ne_bot CFSG.RankThree.Classical.irreducible_X_sub_one
      CFSG.RankThree.Classical.monic_X_sub_one (mem_primaryFactors.mp hX).2.2
  have hpos : 1 ≤ Module.finrank K (primaryComponent (spEnd x) (X - 1)) :=
    Submodule.one_le_finrank_iff.mpr hne
  obtain ⟨s, hs, _⟩ := hblocks.rank
  have hs' : m.headD 0 = s := by
    rw [hm.head_eq, hs]
    omega
  omega

private noncomputable def ggK1D1_adjoinRootEquiv {K : Type} [Field K] {h : K[X]}
    (hmon : h.Monic) (hdeg : h.natDegree = 1) : AdjoinRoot h ≃ₐ[K] K := by
  set a : K := -(h.coeff 0) with ha
  have hh : h = X - C a := by
    have hle : h.degree ≤ 1 := by
      rw [Polynomial.degree_eq_natDegree hmon.ne_zero, hdeg]
      simp
    have h1 := Polynomial.eq_X_add_C_of_degree_le_one hle
    rw [← hdeg, hmon.coeff_natDegree] at h1
    rw [h1, ha]
    simp [C_1, map_neg, sub_eq_add_neg]
  have hroot : algebraMap K (AdjoinRoot h) a = AdjoinRoot.root h := by
    have h0 : AdjoinRoot.mk h (X - C a) = 0 := by
      rw [← hh]
      exact AdjoinRoot.mk_self
    have h1 : AdjoinRoot.root h - AdjoinRoot.of h a = 0 := by
      simpa only [map_sub, AdjoinRoot.mk_X, AdjoinRoot.mk_C] using h0
    rw [AdjoinRoot.algebraMap_eq]
    exact (sub_eq_zero.mp h1).symm
  refine AlgEquiv.ofAlgHom
    (AdjoinRoot.liftAlgHom h (AlgHom.id K K) a ?_)
    (Algebra.ofId K (AdjoinRoot h)) ?_ ?_
  · rw [hh]
    simp
  · ext
  · apply AdjoinRoot.algHom_ext
    rw [AlgHom.comp_apply, AlgHom.id_apply, AdjoinRoot.liftAlgHom_root]
    exact hroot

theorem ggK1CBl_comm_join_d1 {p nf r : ℕ} {K : Type} [Field K] [Finite K]
    {x : ↥(StatedSp r K)} {m : List ℕ} {P : Finset K[X]}
    (hnf : 1 ≤ nf) (hp : p.Prime) (hK : Nat.card K = 2 ^ nf) (hx : x ^ p = 1)
    (hm : GGK1CMultOf p nf 1 r K x m) (hP : IsReciprocalTransversal (spEnd x) P)
    (hblocks : SpPrimaryBlocks 2 nf p x (proj r K x)) :
    (∀ i j : ggK1CBl_Id1 K P m, i ≠ j →
        ∀ a ∈ ggK1CBl_A1 x P m i, ∀ b ∈ ggK1CBl_A1 x P m j, Commute a b) ∧
      (⨆ i : ggK1CBl_Id1 K P m, ggK1CBl_A1 x P m i) =
        Subgroup.centralizer ({x} : Set (StatedSp r K)) ∧
      iSupIndep (ggK1CBl_A1 x P m) := by
  classical
  rcases hm.blocks_eq with ⟨hd1, P₀, hP₀, hmult₀⟩ | ⟨hd2, _⟩
  · have hmemX : m.headD 0 ≠ 0 → (X - 1 : K[X]) ∈ primaryFactors (spEnd x) := by
      intro h0
      by_contra hnot
      have hbot := CFSG.RankThree.Classical.primaryComponent_eq_bot_of_not_mem
        (y := spEnd x) (a := X - 1) CFSG.RankThree.Classical.irreducible_X_sub_one
        CFSG.RankThree.Classical.monic_X_sub_one hnot
      have : m.headD 0 = 0 := by rw [hm.head_eq, hbot]; simp
      exact h0 this
    have hheadX : (X - 1 : K[X]) ∈ primaryFactors (spEnd x) → m.headD 0 ≠ 0 :=
      ggK1D1_headD_ne_zero_of_mem_X_sub_one hm hblocks
    let orb : ggK1CBl_Id1 K P m → reciprocalOrbits (spEnd x) := fun i =>
      match i with
      | Sum.inl h => ⟨{h.1, reciprocalPolynomial h.1}, ⟨h.1, (hP.1 h.1 h.2).1, rfl⟩⟩
      | Sum.inr u => ⟨{X - 1}, ⟨X - 1, hmemX u.2,
          by simp [CFSG.RankThree.Classical.reciprocalPolynomial_X_sub_one]⟩⟩
    have hinj : Function.Injective orb := by
      intro i j hij
      cases i with
      | inl h =>
          cases j with
          | inl k =>
              have hset : ({h.1, reciprocalPolynomial h.1} : Set K[X]) =
                  {k.1, reciprocalPolynomial k.1} := congrArg Subtype.val hij
              have hmem : h.1 ∈ ({k.1, reciprocalPolynomial k.1} : Set K[X]) := by
                rw [← hset]
                exact Set.mem_insert_iff.mpr (Or.inl rfl)
              rcases hmem with hk | hk
              · exact congrArg Sum.inl (Subtype.ext hk)
              · exact absurd (hk ▸ h.2) (hP.2.2 k.1 k.2)
          | inr u =>
              have hset : ({h.1, reciprocalPolynomial h.1} : Set K[X]) = {X - 1} :=
                congrArg Subtype.val hij
              have hmem : h.1 ∈ ({X - 1} : Set K[X]) := by
                rw [← hset]
                exact Set.mem_insert_iff.mpr (Or.inl rfl)
              have hhX : h.1 = X - 1 := by simpa using hmem
              exact absurd (by rw [hhX, CFSG.RankThree.Classical.reciprocalPolynomial_X_sub_one])
                (hP.1 h.1 h.2).2
      | inr u =>
          cases j with
          | inl k =>
              have hset : ({X - 1} : Set K[X]) = {k.1, reciprocalPolynomial k.1} :=
                congrArg Subtype.val hij
              have hmem : X - 1 ∈ ({k.1, reciprocalPolynomial k.1} : Set K[X]) := by
                rw [← hset]
                exact Set.mem_singleton_iff.mpr rfl
              rcases hmem with hk | hk
              · exact absurd (by rw [← hk, CFSG.RankThree.Classical.reciprocalPolynomial_X_sub_one])
                  (hP.1 k.1 k.2).2
              · have hcoeff : k.1.coeff 0 ≠ 0 :=
                  ggK1D1_coeff_zero_ne_of_reciprocal_ne_zero
                    (by rw [← hk]
                        exact CFSG.RankThree.Classical.monic_X_sub_one.ne_zero)
                have hinv := ggK1D1_reciprocal_reciprocal
                  (monic_of_mem_primaryFactors (hP.1 k.1 k.2).1) hcoeff
                have hk1 : k.1 = X - 1 := by
                  rw [← hinv, ← hk]
                  exact CFSG.RankThree.Classical.reciprocalPolynomial_X_sub_one
                exact absurd (by rw [hk1, CFSG.RankThree.Classical.reciprocalPolynomial_X_sub_one])
                  (hP.1 k.1 k.2).2
          | inr v => exact congrArg Sum.inr (Subsingleton.elim u v)
    have hsurj : Function.Surjective orb := by
      intro O
      obtain ⟨h, hh, hO⟩ : ∃ h : K[X], h ∈ primaryFactors (spEnd x) ∧
          ({h, reciprocalPolynomial h} : Set K[X]) = O.1 := by
        simpa [reciprocalOrbits, Set.mem_image] using O.2
      by_cases hX : h = X - 1
      · have hmemX' : (X - 1 : K[X]) ∈ primaryFactors (spEnd x) := by rw [← hX]; exact hh
        have hm0 : m.headD 0 ≠ 0 := hheadX hmemX'
        refine ⟨Sum.inr ⟨(), hm0⟩, ?_⟩
        apply Subtype.ext
        show ({X - 1} : Set K[X]) = O.1
        rw [← hO, hX]
        simp [CFSG.RankThree.Classical.reciprocalPolynomial_X_sub_one]
      · by_cases hself : reciprocalPolynomial h = h
        · exfalso
          have hB0 := ggK1D1_selfDualSum_zero hm hP₀ hmult₀ hblocks
          have hmem : h ∈ (primaryFactors (spEnd x)).filter
              (fun h => reciprocalPolynomial h = h ∧ h ≠ X - 1) := by
            rw [Finset.mem_filter]
            exact ⟨hh, hself, hX⟩
          have hterm : 0 < h.natDegree / 2 * primaryMultiplicity (spEnd x) h := by
            obtain ⟨d, hd, _⟩ := (hblocks.selfDual ⟨h, hh⟩ hX hself).exists_half
            have hdpos : 1 ≤ d := by
              have hpos : 0 < h.natDegree := by
                have h0 : h.natDegree ≠ 0 := fun h0 =>
                  (irreducible_of_mem_primaryFactors hh).not_isUnit
                    (CFSG.RankThree.PartOne.KCOrthogonal.isUnit_of_natDegree_eq_zero_of_ne_zero
                      (irreducible_of_mem_primaryFactors hh).ne_zero h0)
                exact Nat.pos_of_ne_zero h0
              apply Nat.pos_of_ne_zero
              intro hd0
              rw [hd, hd0, mul_zero] at hpos
              exact Nat.lt_irrefl 0 hpos
            have hmult1 : 1 ≤ primaryMultiplicity (spEnd x) h := ggK1D1_primaryMultiplicity_pos hh
            have h2 : 2 ≤ h.natDegree := by
              rw [hd]
              exact Nat.mul_le_mul_left 2 hdpos
            have hdiv : 1 ≤ h.natDegree / 2 := by
              rw [hd, Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
              simpa using Nat.mul_le_mul_left 2 hdpos
            calc 0 < 1 * 1 := by norm_num
              _ ≤ (h.natDegree / 2) * primaryMultiplicity (spEnd x) h :=
                  Nat.mul_le_mul hdiv hmult1
          have hle := Finset.single_le_sum
            (f := fun h => h.natDegree / 2 * primaryMultiplicity (spEnd x) h)
            (fun _ _ => Nat.zero_le _) hmem
          omega
        · rcases hP.2.1 h hh (Ne.symm hself) with hmemP | hmemP
          · refine ⟨Sum.inl ⟨h, hmemP⟩, ?_⟩
            apply Subtype.ext
            show ({h, reciprocalPolynomial h} : Set K[X]) = O.1
            exact hO
          · have hneq : reciprocalPolynomial h ≠ 0 :=
              (irreducible_of_mem_primaryFactors (hP.1 (reciprocalPolynomial h) hmemP).1).ne_zero
            have hcoeff : h.coeff 0 ≠ 0 := ggK1D1_coeff_zero_ne_of_reciprocal_ne_zero hneq
            have hinv := ggK1D1_reciprocal_reciprocal (monic_of_mem_primaryFactors hh) hcoeff
            refine ⟨Sum.inl ⟨reciprocalPolynomial h, hmemP⟩, ?_⟩
            apply Subtype.ext
            show ({reciprocalPolynomial h, reciprocalPolynomial (reciprocalPolynomial h)} :
              Set K[X]) = O.1
            rw [← hO, hinv, Set.pair_comm]
    have hbij : Function.Bijective orb := ⟨hinj, hsurj⟩
    let e : ggK1CBl_Id1 K P m ≃ reciprocalOrbits (spEnd x) := Equiv.ofBijective orb hbij
    have horb_apply : ∀ i, ggK1CBl_A1 x P m i = spSupported x (e i : Set K[X]) := by
      intro i
      cases i <;> rfl
    refine ⟨?_, ?_, ?_⟩
    · intro i j hij a ha b hb
      have hne : (e i : Set K[X]) ≠ (e j : Set K[X]) := fun h => hij (e.injective (Subtype.ext h))
      refine hblocks.directProduct.1 (e i : Set K[X]) (e i).2 (e j : Set K[X]) (e j).2 hne a ?_ b ?_
      · rw [horb_apply i] at ha; exact ha
      · rw [horb_apply j] at hb; exact hb
    · rw [show ggK1CBl_A1 x P m = fun i => spSupported x (e i : Set K[X]) from funext horb_apply]
      rw [Equiv.iSup_comp
        (g := fun O : reciprocalOrbits (spEnd x) => spSupported x (O : Set K[X])) e]
      exact hblocks.directProduct.2.2
    · rw [show ggK1CBl_A1 x P m = fun i => spSupported x (e i : Set K[X]) from funext horb_apply]
      have ht : iSupIndep
          ((fun i : ggK1CBl_Id1 K P m => spSupported x (e i : Set K[X])) ∘ e.symm) := by
        rw [show ((fun i : ggK1CBl_Id1 K P m => spSupported x (e i : Set K[X])) ∘ e.symm) =
            fun O : reciprocalOrbits (spEnd x) => spSupported x (O : Set K[X]) from by
          funext O
          simp [Function.comp_apply, Equiv.apply_symm_apply]]
        exact hblocks.directProduct.2.1
      exact iSupIndep.comp'
        (t := fun i : ggK1CBl_Id1 K P m => spSupported x (e i : Set K[X]))
        (f := e.symm) ht e.symm.surjective
  · exact absurd hd2 (by decide)

theorem ggK1CBl_witness_d1 {p nf r : ℕ} {K : Type} [Field K] [Finite K]
    {x : ↥(StatedSp r K)} {m : List ℕ} {P : Finset K[X]}
    (hnf : 1 ≤ nf) (hp : p.Prime) (hK : Nat.card K = 2 ^ nf)
    (hm : GGK1CMultOf p nf 1 r K x m) (hP : IsReciprocalTransversal (spEnd x) P)
    (hblocks : SpPrimaryBlocks 2 nf p x (proj r K x)) :
    ∀ i : ggK1CBl_Id1 K P m,
      ggK1CBl_KindWitness nf K (ggK1CBl_kind1 1 x P m i) (ggK1CBl_A1 x P m i) := by
  classical
  rcases hm.blocks_eq with ⟨hd1, P₀, hP₀, hmult₀⟩ | ⟨hd2, _⟩
  · have hdeg₀ : ∀ h ∈ P₀, h.natDegree = 1 := (ggK1CBl_rank_d1 hm hP₀ hmult₀ hblocks).2
    have hdegP : ∀ h ∈ P, h.natDegree = 1 := by
      intro h hh
      have hne : h ≠ reciprocalPolynomial h := (hP.1 h hh).2
      rcases hP₀.2.1 h (hP.1 h hh).1 hne with hm₀ | hm₀
      · exact hdeg₀ h hm₀
      · have hcoeff : h.coeff 0 ≠ 0 := ggK1D1_coeff_zero_ne_of_reciprocal_ne_zero
          (irreducible_of_mem_primaryFactors (hP₀.1 (reciprocalPolynomial h) hm₀).1).ne_zero
        have hcur := hdeg₀ (reciprocalPolynomial h) hm₀
        rwa [CFSG.RankThree.PartOne.KCOrthogonal.natDegree_reciprocalPolynomial hcoeff] at hcur
    intro i
    cases i with
    | inl h =>
        have hhP := h.2
        have hhprim : h.1 ∈ primaryFactors (spEnd x) := (hP.1 h.1 hhP).1
        have hpair : h.1 ≠ reciprocalPolynomial h.1 := (hP.1 h.1 hhP).2
        have hkind : ggK1CBl_kind1 1 x P m (Sum.inl h) =
            ggK1CCo_Kind.sl (primaryMultiplicity (spEnd x) h.1) := rfl
        rw [hkind]
        unfold ggK1CBl_KindWitness
        haveI : Fact (Irreducible h.1) := ⟨irreducible_of_mem_primaryFactors hhprim⟩
        have hpos : 1 ≤ primaryMultiplicity (spEnd x) h.1 := ggK1D1_primaryMultiplicity_pos hhprim
        obtain ⟨eM⟩ := (hblocks.paired ⟨h.1, hhprim⟩ hpair).matrixFactor
        have eAR := ggK1D1_adjoinRootEquiv (monic_of_mem_primaryFactors hhprim) (hdegP h.1 hhP)
        let eGL : GL (Fin (primaryMultiplicity (spEnd x) h.1)) (AdjoinRoot h.1) ≃*
            GL (Fin (primaryMultiplicity (spEnd x) h.1)) K :=
          Units.mapEquiv (RingEquiv.mapMatrix eAR.toRingEquiv).toMulEquiv
        exact ⟨hpos, ⟨eM.trans eGL⟩⟩
    | inr u =>
        have hkind : ggK1CBl_kind1 1 x P m (Sum.inr u) = ggK1CCo_Kind.sp (m.headD 0) := rfl
        rw [hkind]
        unfold ggK1CBl_KindWitness
        have hmemX : (X - 1 : K[X]) ∈ primaryFactors (spEnd x) := by
          by_contra hnot
          have hbot := CFSG.RankThree.Classical.primaryComponent_eq_bot_of_not_mem
            (y := spEnd x) (a := X - 1) CFSG.RankThree.Classical.irreducible_X_sub_one
            CFSG.RankThree.Classical.monic_X_sub_one hnot
          have : m.headD 0 = 0 := by rw [hm.head_eq, hbot]; simp
          exact u.2 this
        have hpos : 1 ≤ m.headD 0 := Nat.pos_of_ne_zero u.2
        obtain ⟨s, hs, _⟩ := hblocks.rank
        have hs' : s = m.headD 0 := by
          rw [hm.head_eq, hs]
          omega
        refine ⟨hpos, primaryComponent (spEnd x) (X - 1), inferInstance, inferInstance,
          inferInstance, (spForm r K).restrict (primaryComponent (spEnd x) (X - 1)),
          ?_, hblocks.fixed_nondegenerate, ?_, ?_⟩
        · intro v
          exact spForm_isAlt (v : Fin r ⊕ Fin r → K)
        · rw [hs, hs']
        · obtain ⟨φ, _⟩ := hblocks.fixedFactor hmemX
          exact ⟨φ⟩
  · exact absurd hd2 (by decide)

theorem ggK1CBl_kind_multiset_d1 {p nf r : ℕ} {K : Type} [Field K]
    {x : ↥(StatedSp r K)} {m : List ℕ} {P : Finset K[X]}
    (hm : GGK1CMultOf p nf 1 r K x m) (hP : IsReciprocalTransversal (spEnd x) P)
    (hmult : Multiset.ofList (m.tail.filter (fun j => decide (j ≠ 0))) =
      P.val.map (primaryMultiplicity (spEnd x))) :
    (Finset.univ : Finset (ggK1CBl_Id1 K P m)).val.map (ggK1CBl_kind1 1 x P m) =
      ggK1CCo_expectedKinds p nf 1 m := by
  classical
  have hA : (Finset.univ : Finset ↥P).val.map
        (fun z => ggK1CBl_kind1 1 x P m (Sum.inl z)) =
      Multiset.ofList (((List.range m.length).filter
          (fun j => decide (1 ≤ j ∧ 1 ≤ m.getD j 0))).map
        (fun j => ggK1CCo_Kind.sl (m.getD j 0))) := by
    rw [show (fun z : ↥P => ggK1CBl_kind1 1 x P m (Sum.inl z)) =
        (fun z : ↥P => ggK1CCo_Kind.sl (primaryMultiplicity (spEnd x) z.val)) from by
      funext z; rfl]
    rw [ggK1CBl_univ_map_subtype_val P
      (fun h => ggK1CCo_Kind.sl (primaryMultiplicity (spEnd x) h))]
    have hmap : P.val.map (fun h => ggK1CCo_Kind.sl (primaryMultiplicity (spEnd x) h)) =
        (P.val.map (primaryMultiplicity (spEnd x))).map ggK1CCo_Kind.sl :=
      (Multiset.map_map ggK1CCo_Kind.sl (primaryMultiplicity (spEnd x)) P.val).symm
    rw [hmap, ← hmult]
    rw [Multiset.map_coe]
    rw [← List.drop_one]
    exact congrArg Multiset.ofList
      (ggK1CBl_tail_filter_map m (fun j => ggK1CCo_Kind.sl j)).symm
  have hB : (Finset.univ : Finset (Subtype (fun _ : Unit => m.headD 0 ≠ 0))).val.map
        (fun z => ggK1CBl_kind1 1 x P m (Sum.inr z)) =
      (if m.headD 0 = 0 then 0 else {ggK1CCo_Kind.sp (m.headD 0)}) := by
    rw [show (fun z : Subtype (fun _ : Unit => m.headD 0 ≠ 0) =>
          ggK1CBl_kind1 1 x P m (Sum.inr z)) =
        (fun _ => ggK1CCo_Kind.sp (m.headD 0)) from by funext z; rfl]
    by_cases h0 : m.headD 0 = 0
    · rw [if_pos h0]
      haveI : IsEmpty (Subtype (fun _ : Unit => m.headD 0 ≠ 0)) := ⟨fun z => z.2 h0⟩
      rw [Finset.univ_eq_empty]
      simp
    · rw [if_neg h0]
      have hsub : (Finset.univ : Finset (Subtype (fun _ : Unit => m.headD 0 ≠ 0))) =
          {⟨(), h0⟩} := by
        rw [Finset.eq_singleton_iff_unique_mem]
        exact ⟨Finset.mem_univ _, fun z _ => Subtype.ext (Subsingleton.elim _ _)⟩
      rw [hsub]
      simp
  have hExp : ggK1CCo_expectedKinds p nf 1 m =
      (if m.headD 0 = 0 then 0 else {ggK1CCo_Kind.sp (m.headD 0)}) +
      Multiset.ofList (((List.range m.length).filter
          (fun j => decide (1 ≤ j ∧ 1 ≤ m.getD j 0))).map
        (fun j => ggK1CCo_Kind.sl (m.getD j 0))) := by
    rw [ggK1CCo_expectedKinds, ggK1CCo_expectedKindList, hm.length_eq.symm]
    by_cases h0 : m.headD 0 = 0
    · rw [if_pos h0, if_pos h0]
      simp
    · rw [if_neg h0, if_neg h0]
      simp
  rw [← Finset.univ_disjSum_univ (α := ↥P)
        (β := Subtype (fun _ : Unit => m.headD 0 ≠ 0))]
  rw [Finset.val_disjSum, Multiset.map_disjSum, hA, hB, hExp]
  exact add_comm _ _

end CFSG.StandardType

end
