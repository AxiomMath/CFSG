module

public import CFSG.LocalAnalysis.StandardType.GGK1CCoDefs
public import CFSG.LocalAnalysis.StandardType.GGK1CBlFF

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.Classical (spEnd IsReciprocalTransversal SpPrimaryBlocks spSupported
  symplectic_cross_prime_primary_centralizer_blocks)
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

@[expose] noncomputable def ggK1CBl_selfDualFactors {r : ℕ} {K : Type} [Field K]
    (x : ↥(StatedSp r K)) : Finset K[X] := by
  classical
  exact (primaryFactors (spEnd x)).filter (fun h => reciprocalPolynomial h = h ∧ h ≠ X - 1)

private theorem ggK1Rk_sum_eq_headD_add_sum_tail (m : List ℕ) :
    m.sum = m.headD 0 + m.tail.sum := by
  cases m <;> rfl

private theorem ggK1Rk_sum_filter_ne_zero (l : List ℕ) :
    (l.filter (fun j => decide (j ≠ 0))).sum = l.sum := by
  have hcongr : l.filter (fun j => decide (j ≠ 0)) =
      l.filter (fun j => !decide (j = 0)) :=
    List.filter_congr fun j _ => by
      by_cases h : j = 0 <;> simp [h]
  rw [hcongr]
  induction l with
  | nil => rfl
  | cons a t ih =>
      rw [List.filter_cons]
      by_cases ha : a = 0
      · subst ha
        simp [ih]
      · simp [ha, ih]

private theorem ggK1Rk_primaryComponent_ne_bot {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {x : Module.End K V} {h : K[X]}
    (hh : h ∈ primaryFactors x) : primaryComponent x h ≠ ⊥ := by
  intro hbot
  have hinj : Function.Injective (aeval x h) := by
    rw [← LinearMap.ker_eq_bot]
    exact hbot
  obtain ⟨hirr, -, hdvd⟩ := mem_primaryFactors.mp hh
  obtain ⟨g, hg⟩ := hdvd
  have hg0 : aeval x g = 0 := by
    have h0 : aeval x (h * g) = 0 := by rw [← hg, minpoly.aeval]
    rw [map_mul] at h0
    ext v
    apply hinj
    have := congrArg (fun f : Module.End K V => f v) h0
    simpa [Module.End.mul_apply] using this
  have hdvdg : minpoly K x ∣ g := minpoly.dvd K x hg0
  have hgne : g ≠ 0 := by
    intro hg'
    rw [hg', mul_zero] at hg
    exact minpoly_ne_zero x hg
  have hle : (minpoly K x).natDegree ≤ g.natDegree := natDegree_le_of_dvd hdvdg hgne
  have hdeg : (minpoly K x).natDegree = h.natDegree + g.natDegree := by
    rw [hg, natDegree_mul hirr.ne_zero hgne]
  have hpos : 0 < h.natDegree := hirr.natDegree_pos
  omega

private theorem ggK1Rk_primaryMultiplicity_pos {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {x : Module.End K V} {h : K[X]}
    (hh : h ∈ primaryFactors x) : 0 < primaryMultiplicity x h := by
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  haveI : Nontrivial (primaryComponent x h) :=
    Submodule.nontrivial_iff_ne_bot.mpr (ggK1Rk_primaryComponent_ne_bot hh)
  exact Module.finrank_pos

private theorem ggK1Rk_dvd_cyclotomic {K : Type} [Field K] {p : ℕ} {h : K[X]}
    {r : ℕ} {x : ↥(StatedSp r K)}
    (hh : h ∈ primaryFactors (spEnd x)) (hne : h ≠ X - 1)
    (hord : orderOf (AdjoinRoot.root h) = p) (hp0 : 0 < p) :
    h ∣ cyclotomic p K := by
  classical
  have hirr := irreducible_of_mem_primaryFactors hh
  have hmon := monic_of_mem_primaryFactors hh
  haveI : Fact (Irreducible h) := ⟨hirr⟩
  have hmin : minpoly K (AdjoinRoot.root h) = h := by
    rw [AdjoinRoot.minpoly_root hirr.ne_zero, hmon.leadingCoeff, inv_one, C_1, mul_one]
  have hprim : IsPrimitiveRoot (AdjoinRoot.root h) p := by
    rw [← hord]
    exact IsPrimitiveRoot.orderOf _
  rw [← hmin]
  apply minpoly.dvd
  have h1 : (cyclotomic p (AdjoinRoot h)).eval (AdjoinRoot.root h) = 0 :=
    Polynomial.IsRoot.def.mp (IsPrimitiveRoot.isRoot_cyclotomic hp0 hprim)
  rw [← map_cyclotomic p (algebraMap K (AdjoinRoot h))] at h1
  rwa [aeval_def, ← eval_map]

private theorem ggK1Rk_natDegree_eq_orderOf {K : Type} [Field K] [Finite K]
    {p nf : ℕ} {r : ℕ} {x : ↥(StatedSp r K)} {h : K[X]}
    (hK : Nat.card K = 2 ^ nf) (hp0 : 0 < p) (hpodd : (2 : ℕ).Coprime p)
    (hh : h ∈ primaryFactors (spEnd x)) (hne : h ≠ X - 1)
    (hord : orderOf (AdjoinRoot.root h) = p) :
    h.natDegree = orderOf ((Nat.card K : ℕ) : ZMod p) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hKf : Fintype.card K = 2 ^ nf := by rw [← Nat.card_eq_fintype_card]; exact hK
  have hirr := irreducible_of_mem_primaryFactors hh
  have hdvdΦ : h ∣ cyclotomic p K := ggK1Rk_dvd_cyclotomic hh hne hord hp0
  have hdeg := natDegree_of_dvd_cyclotomic_of_irreducible (K := K) (p := 2) (f := nf)
    (n := p) hKf hpodd hdvdΦ hirr
  rw [hdeg, ← orderOf_units, ZMod.coe_unitOfCoprime]
  congr 1
  rw [← hKf, Nat.card_eq_fintype_card]

private theorem ggK1Rk_coeff_zero_ne_zero {K : Type} [Field K] {p : ℕ}
    {r : ℕ} {x : ↥(StatedSp r K)} {h : K[X]} (hp0 : 0 < p)
    (hh : h ∈ primaryFactors (spEnd x))
    (hord : orderOf (AdjoinRoot.root h) = p) : h.coeff 0 ≠ 0 := by
  intro h0
  have hirr := irreducible_of_mem_primaryFactors hh
  have hmon := monic_of_mem_primaryFactors hh
  haveI : Fact (Irreducible h) := ⟨hirr⟩
  have hmin : minpoly K (AdjoinRoot.root h) = h := by
    rw [AdjoinRoot.minpoly_root hirr.ne_zero, hmon.leadingCoeff, inv_one, C_1, mul_one]
  have hdvd : h ∣ (X ^ p - 1 : K[X]) := by
    rw [← hmin]
    apply minpoly.dvd
    rw [map_sub, map_pow, aeval_X, map_one, ← hord, pow_orderOf_eq_one, sub_self]
  have hX : X ∣ h := X_dvd_iff.mpr h0
  have hX' : X ∣ (X ^ p - 1 : K[X]) := hX.trans hdvd
  have hthis : (X ^ p - 1 : K[X]).coeff 0 = 0 := X_dvd_iff.mp hX'
  have hcoeff : (X ^ p - 1 : K[X]).coeff 0 = -1 := by
    rw [coeff_sub, coeff_X_pow, coeff_one]
    simp [hp0.ne', Ne.symm hp0.ne']
  rw [hcoeff] at hthis
  exact one_ne_zero (neg_eq_zero.mp hthis)

private theorem ggK1Rk_selfDual_of_dvd_add {K : Type} [Field K] [Finite K]
    {p nf : ℕ} {r : ℕ} {x : ↥(StatedSp r K)} {h : K[X]}
    (hp0 : 0 < p) (hK : Nat.card K = 2 ^ nf) (hpq : p ∣ 2 ^ nf + 1)
    (hh : h ∈ primaryFactors (spEnd x)) (hne : h ≠ X - 1)
    (hord : orderOf (AdjoinRoot.root h) = p) :
    reciprocalPolynomial h = h := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hmon := monic_of_mem_primaryFactors hh
  have hirr := irreducible_of_mem_primaryFactors hh
  haveI : Fact (Irreducible h) := ⟨hirr⟩
  have h0 : h.coeff 0 ≠ 0 := ggK1Rk_coeff_zero_ne_zero hp0 hh hord
  let E := AdjoinRoot h
  let lam : E := AdjoinRoot.root h
  have hroot : aeval lam h = 0 := by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hqroot : aeval (lam ^ Nat.card K) h = 0 := by
    rw [Nat.card_eq_fintype_card, ← expand_aeval, FiniteField.Polynomial.expand_card, map_pow,
      hroot, zero_pow Fintype.card_ne_zero]
  have hpqK : p ∣ Nat.card K + 1 := by rw [hK]; exact hpq
  have hpow : lam ^ (Nat.card K + 1) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hord]
    exact hpqK
  have hmul : lam ^ Nat.card K * lam = 1 := by rw [← pow_succ, hpow]
  have hinv : lam ^ Nat.card K = lam⁻¹ := eq_inv_of_mul_eq_one_left hmul
  have hrootinv : aeval (lam⁻¹) h = 0 := by rw [← hinv]; exact hqroot
  let u : Eˣ := Units.mk0 lam (CFSG.RankThree.PartOne.KCUnitary.root_ne_zero h0)
  have hrec : aeval lam (reciprocalPolynomial h) = 0 := by
    have hu := CFSG.RankThree.PartOne.KCOrthogonal.aeval_reciprocalPolynomial_of_unit u h
    rw [show (u : E) = lam from rfl,
      show ((u⁻¹ : Eˣ) : E) = lam⁻¹ by rw [Units.val_inv_eq_inv_val]; rfl,
      hrootinv, mul_zero, smul_zero] at hu
    exact hu
  have hrec_monic : (reciprocalPolynomial h).Monic :=
    CFSG.RankThree.PartOne.KCOrthogonal.monic_reciprocalPolynomial h0
  have hrec_irr : Irreducible (reciprocalPolynomial h) :=
    CFSG.RankThree.PartOne.KCOrthogonal.irreducible_reciprocalPolynomial hirr h0
  have hmin : minpoly K lam = h := by
    rw [AdjoinRoot.minpoly_root hirr.ne_zero, hmon.leadingCoeff, inv_one, C_1, mul_one]
  have hdvd : h ∣ reciprocalPolynomial h := by
    nth_rewrite 1 [← hmin]
    rw [minpoly.dvd_iff]
    exact hrec
  exact eq_of_monic_of_associated hrec_monic hmon (hirr.associated_of_dvd hrec_irr hdvd).symm

theorem ggK1CBl_rank_d1 {p nf r : ℕ} {K : Type} [Field K] [Finite K]
    {x : ↥(StatedSp r K)} {m : List ℕ} {P : Finset K[X]}
    (hm : GGK1CMultOf p nf 1 r K x m) (hP : IsReciprocalTransversal (spEnd x) P)
    (hmult : Multiset.ofList (m.tail.filter (fun j => decide (j ≠ 0))) =
      P.val.map (primaryMultiplicity (spEnd x)))
    (hblocks : SpPrimaryBlocks 2 nf p x (proj r K x)) :
    ggK1CBl_selfDualFactors x = ∅ ∧ ∀ h ∈ P, h.natDegree = 1 := by
  classical
  let M : K[X] → ℕ := fun h => primaryMultiplicity (spEnd x) h
  let SD : Finset K[X] :=
    (primaryFactors (spEnd x)).filter (fun h => reciprocalPolynomial h = h ∧ h ≠ X - 1)
  have hSDdef : SD = (primaryFactors (spEnd x)).filter
      (fun h => reciprocalPolynomial h = h ∧ h ≠ X - 1) := rfl
  obtain ⟨s, hfin, -, hrank⟩ := hblocks.rank
  have hs : m.headD 0 = s := by
    rw [hm.head_eq, hfin, Nat.mul_div_cancel_left s (by norm_num : 0 < 2)]
  have hMsum : m.tail.sum = ∑ h ∈ P, M h := by
    have h1 : m.tail.sum = (m.tail.filter (fun j => decide (j ≠ 0))).sum :=
      (ggK1Rk_sum_filter_ne_zero m.tail).symm
    have h2 : (Multiset.ofList (m.tail.filter (fun j => decide (j ≠ 0)))).sum =
        (m.tail.filter (fun j => decide (j ≠ 0))).sum := Multiset.sum_coe _
    have h3 : (Multiset.ofList (m.tail.filter (fun j => decide (j ≠ 0)))).sum =
        ∑ h ∈ P, M h := by
      rw [hmult]
      exact (Finset.sum_eq_multiset_sum P M).symm
    rw [h1, ← h2]
    exact h3
  have hsum1 : r = s + ∑ h ∈ P, M h := by
    rw [← hm.sum_eq, ggK1Rk_sum_eq_headD_add_sum_tail m, hs, hMsum]
  have hrankP := hrank P hP
  rw [← hSDdef] at hrankP
  have hrankP' := hrankP
  rw [Nat.add_assoc] at hrankP'
  have hEq : ∑ h ∈ P, M h = (∑ h ∈ P, h.natDegree * M h) +
      ∑ h ∈ SD, h.natDegree / 2 * M h := by
    apply Nat.add_left_cancel (n := s)
    rw [← hsum1]
    exact hrankP'
  have hdecomp : ∀ h ∈ P, h.natDegree * M h = (h.natDegree - 1) * M h + M h := by
    intro h hh
    have hd1 : 1 ≤ h.natDegree :=
      (irreducible_of_mem_primaryFactors (hP.1 h hh).1).natDegree_pos
    calc h.natDegree * M h = ((h.natDegree - 1) + 1) * M h := by
          rw [Nat.sub_add_cancel hd1]
      _ = (h.natDegree - 1) * M h + 1 * M h := by rw [add_mul]
      _ = (h.natDegree - 1) * M h + M h := by rw [one_mul]
  have hcombine : (∑ h ∈ P, h.natDegree * M h) =
      (∑ h ∈ P, (h.natDegree - 1) * M h) + ∑ h ∈ P, M h := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun h hh => hdecomp h hh
  rw [hcombine] at hEq
  have hzero : (∑ h ∈ P, (h.natDegree - 1) * M h) +
      ∑ h ∈ SD, h.natDegree / 2 * M h = 0 := by omega
  have hA : (∑ h ∈ P, (h.natDegree - 1) * M h) = 0 := (Nat.add_eq_zero.mp hzero).1
  have hB : (∑ h ∈ SD, h.natDegree / 2 * M h) = 0 := (Nat.add_eq_zero.mp hzero).2
  have hdegP : ∀ h ∈ P, h.natDegree = 1 := by
    intro h hh
    have hterm : (h.natDegree - 1) * M h = 0 := by
      have := (Finset.sum_eq_zero_iff.mp hA) h hh
      simpa using this
    have hposM : 0 < M h :=
      ggK1Rk_primaryMultiplicity_pos (hP.1 h hh).1
    have hsub : h.natDegree - 1 = 0 :=
      (Nat.mul_eq_zero.mp hterm).resolve_right (Nat.pos_iff_ne_zero.mp hposM)
    have hposd : 1 ≤ h.natDegree :=
      (irreducible_of_mem_primaryFactors (hP.1 h hh).1).natDegree_pos
    omega
  have hSD : SD = ∅ := by
    rw [← Finset.not_nonempty_iff_eq_empty]
    rintro ⟨h, hh⟩
    have hterm : h.natDegree / 2 * M h = 0 := by
      have := (Finset.sum_eq_zero_iff.mp hB) h hh
      simpa using this
    have hmem := Finset.mem_filter.mp hh
    have hposM : 0 < M h := ggK1Rk_primaryMultiplicity_pos hmem.1
    have hdiv : h.natDegree / 2 = 0 :=
      (Nat.mul_eq_zero.mp hterm).resolve_right (Nat.pos_iff_ne_zero.mp hposM)
    obtain ⟨d, hd, -⟩ := (hblocks.selfDual ⟨h, hmem.1⟩ (by simpa using hmem.2.2)
      (by simpa using hmem.2.1)).exists_half
    have hd2 : h.natDegree / 2 = d := by
      rw [hd, Nat.mul_div_cancel_left d (by norm_num : 0 < 2)]
    have hd0 : d = 0 := by rw [← hd2, hdiv]
    have hposd : 0 < h.natDegree :=
      (irreducible_of_mem_primaryFactors hmem.1).natDegree_pos
    have hzero_deg : h.natDegree = 0 := by rw [hd, hd0, mul_zero]
    exact absurd hzero_deg (Nat.pos_iff_ne_zero.mp hposd)
  refine ⟨?_, hdegP⟩
  show SD = ∅
  exact hSD

theorem ggK1CBl_rank_d2 {p nf r : ℕ} {K : Type} [Field K] [Finite K]
    {x : ↥(StatedSp r K)} {m : List ℕ}
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1) (hK : Nat.card K = 2 ^ nf)
    (hm : GGK1CMultOf p nf 2 r K x m)
    (hblocks : SpPrimaryBlocks 2 nf p x (proj r K x)) :
    (∀ P : Finset K[X], IsReciprocalTransversal (spEnd x) P → P = ∅) ∧
      (∀ h ∈ primaryFactors (spEnd x), h ≠ X - 1 → reciprocalPolynomial h = h) ∧
      (∀ h ∈ primaryFactors (spEnd x), h ≠ X - 1 → h.natDegree = 2) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hcard1 : 1 < Nat.card K := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hnf : 1 ≤ nf := by
    by_contra h
    have h0 : nf = 0 := by omega
    subst h0
    rw [hK] at hcard1
    norm_num at hcard1
  have hpow2 : 2 ≤ 2 ^ nf := by
    rw [← hK]
    exact hcard1
  have hp0 : 0 < p := by
    by_contra hp0'
    have hpz : p = 0 := by omega
    subst hpz
    rcases hdvd with h | h
    · obtain ⟨k, hk⟩ := h; omega
    · obtain ⟨k, hk⟩ := h; omega
  have hodd_sub : Odd (2 ^ nf - 1) := by
    obtain ⟨m', rfl⟩ : ∃ m', nf = m' + 1 := ⟨nf - 1, by omega⟩
    refine ⟨2 ^ m' - 1, ?_⟩
    rw [pow_succ]
    have : 1 ≤ 2 ^ m' := Nat.one_le_two_pow
    omega
  have hodd_add : Odd (2 ^ nf + 1) := by
    obtain ⟨m', rfl⟩ : ∃ m', nf = m' + 1 := ⟨nf - 1, by omega⟩
    refine ⟨2 ^ m', ?_⟩
    rw [pow_succ]
    ring
  have h2p : ¬ 2 ∣ p := by
    rcases hdvd with h | h
    · intro h2
      exact (Nat.not_even_iff_odd.mpr hodd_sub) (even_iff_two_dvd.mpr (h2.trans h))
    · intro h2
      exact (Nat.not_even_iff_odd.mpr hodd_add) (even_iff_two_dvd.mpr (h2.trans h))
  have hpodd : (2 : ℕ).Coprime p :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2p
  by_cases hp1 : p = 1
  ·
    have hTfalse : ∀ h ∈ primaryFactors (spEnd x), h ≠ X - 1 → False := by
      intro h hh hne
      have hord := hblocks.nontrivial h hh hne
      rw [hp1] at hord
      have hroot : AdjoinRoot.root h = 1 := orderOf_eq_one_iff.mp hord
      have hirr := irreducible_of_mem_primaryFactors hh
      have hmon := monic_of_mem_primaryFactors hh
      haveI : Fact (Irreducible h) := ⟨hirr⟩
      have hmin : minpoly K (AdjoinRoot.root h) = h := by
        rw [AdjoinRoot.minpoly_root hirr.ne_zero, hmon.leadingCoeff, inv_one, C_1, mul_one]
      have hdvdX : h ∣ (X - 1 : K[X]) := by
        rw [← hmin]
        apply minpoly.dvd
        rw [map_sub, aeval_X, map_one, hroot, sub_self]
      have hX1 : h = X - 1 := by
        have hh1 := eq_of_monic_of_associated hmon (monic_X_sub_C 1)
          (hirr.associated_of_dvd (irreducible_X_sub_C 1) hdvdX)
        rwa [C_1] at hh1
      exact hne hX1
    refine ⟨?_, fun h hh hne => (hTfalse h hh hne).elim,
      fun h hh hne => (hTfalse h hh hne).elim⟩
    intro P hP
    rw [← Finset.not_nonempty_iff_eq_empty]
    rintro ⟨h, hh⟩
    rcases eq_or_ne h (X - 1) with hX | hne
    · exact (hP.1 h hh).2
        (by rw [hX, CFSG.RankThree.Classical.reciprocalPolynomial_X_sub_one])
    · exact hTfalse h (hP.1 h hh).1 hne
  · rcases hdvd with hsub | hadd
    ·
      have hqc : ((Nat.card K : ℕ) : ZMod p) = 1 := by
        rw [hK]
        have h1 : ((2 ^ nf - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hsub
        rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_one] at h1
        exact sub_eq_zero.mp h1
      have hdegT : ∀ h ∈ primaryFactors (spEnd x), h ≠ X - 1 → h.natDegree = 1 := by
        intro h hh hne
        rw [ggK1Rk_natDegree_eq_orderOf hK hp0 hpodd hh hne (hblocks.nontrivial h hh hne),
          hqc, orderOf_one]
      let M : K[X] → ℕ := fun k => primaryMultiplicity (spEnd x) k
      let SD : Finset K[X] :=
        (primaryFactors (spEnd x)).filter (fun k => reciprocalPolynomial k = k ∧ k ≠ X - 1)
      let T : Finset K[X] := (primaryFactors (spEnd x)).filter (fun k => k ≠ X - 1)
      have hSDdef : SD = (primaryFactors (spEnd x)).filter
          (fun k => reciprocalPolynomial k = k ∧ k ≠ X - 1) := rfl
      obtain ⟨s, hfin, ⟨P₀, hP₀⟩, hrank⟩ := hblocks.rank
      have hmblocks : Multiset.ofList (m.tail.filter (fun j => decide (j ≠ 0))) =
          T.val.map M := by
        rcases hm.blocks_eq with ⟨hd1, -⟩ | ⟨hd2, hbe⟩
        · exact absurd hd1 (by norm_num)
        · exact hbe
      have hsum_head : m.headD 0 = s := by
        rw [hm.head_eq, hfin, Nat.mul_div_cancel_left s (by norm_num : 0 < 2)]
      have hMsum : m.tail.sum = ∑ k ∈ T, M k := by
        have h1 : m.tail.sum = (m.tail.filter (fun j => decide (j ≠ 0))).sum :=
          (ggK1Rk_sum_filter_ne_zero m.tail).symm
        have h2 : (Multiset.ofList (m.tail.filter (fun j => decide (j ≠ 0)))).sum =
            (m.tail.filter (fun j => decide (j ≠ 0))).sum := Multiset.sum_coe _
        have h3 : (Multiset.ofList (m.tail.filter (fun j => decide (j ≠ 0)))).sum =
            ∑ k ∈ T, M k := by
          rw [hmblocks]
          exact (Finset.sum_eq_multiset_sum T M).symm
        rw [h1, ← h2]
        exact h3
      have hsum1 : r = s + ∑ k ∈ T, M k := by
        rw [← hm.sum_eq, ggK1Rk_sum_eq_headD_add_sum_tail m, hsum_head, hMsum]
      have hrankP := hrank P₀ hP₀
      rw [← hSDdef] at hrankP
      have hrankP' := hrankP
      rw [Nat.add_assoc] at hrankP'
      have hEq : ∑ k ∈ T, M k = (∑ k ∈ P₀, k.natDegree * M k) +
          ∑ k ∈ SD, k.natDegree / 2 * M k := by
        apply Nat.add_left_cancel (n := s)
        rw [← hsum1]
        exact hrankP'
      have hdegP : ∀ k ∈ P₀, k.natDegree = 1 := by
        intro k hk
        exact hdegT k (hP₀.1 k hk).1
          (fun hX => (hP₀.1 k hk).2
            (by rw [hX, CFSG.RankThree.Classical.reciprocalPolynomial_X_sub_one]))
      have hdegSD : ∀ k ∈ SD, k.natDegree / 2 = 0 := by
        intro k hk
        have hk' := Finset.mem_filter.mp hk
        rw [hdegT k hk'.1 hk'.2.2]
      have hsumP : (∑ k ∈ P₀, k.natDegree * M k) = ∑ k ∈ P₀, M k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hdegP k hk, one_mul]
      have hsumSD : (∑ k ∈ SD, k.natDegree / 2 * M k) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        rw [hdegSD k hk, zero_mul]
      have hEq' : ∑ k ∈ T, M k = ∑ k ∈ P₀, M k := by
        rw [hEq, hsumP, hsumSD, add_zero]
      have hP₀T : P₀ ⊆ T := by
        intro k hk
        refine Finset.mem_filter.mpr ⟨(hP₀.1 k hk).1, ?_⟩
        intro hX
        exact (hP₀.1 k hk).2
          (by rw [hX, CFSG.RankThree.Classical.reciprocalPolynomial_X_sub_one])
      have hP₀'T : P₀.image reciprocalPolynomial ⊆ T := by
        intro k hk
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
        have hjm := (hP₀.1 j hj).1
        have hjm' : reciprocalPolynomial j ∈ primaryFactors (spEnd x) :=
          hblocks.bijOn.mapsTo hjm
        refine Finset.mem_filter.mpr ⟨hjm', ?_⟩
        intro hX
        have hXmem : (X - 1 : K[X]) ∈ primaryFactors (spEnd x) := by rwa [hX] at hjm'
        have heq : reciprocalPolynomial j = reciprocalPolynomial (X - 1) := by
          rw [hX, CFSG.RankThree.Classical.reciprocalPolynomial_X_sub_one]
        have hjeq : j = X - 1 := hblocks.bijOn.injOn hjm hXmem heq
        exact (hP₀.1 j hj).2
          (by rw [hjeq, CFSG.RankThree.Classical.reciprocalPolynomial_X_sub_one])
      have hdisj : Disjoint P₀ (P₀.image reciprocalPolynomial) := by
        rw [Finset.disjoint_left]
        intro k hk hk'
        obtain ⟨j, hj, hjkeq⟩ := Finset.mem_image.mp hk'
        rw [← hjkeq] at hk
        exact hP₀.2.2 j hj hk
      have hinj : ∀ a ∈ P₀, ∀ b ∈ P₀,
          reciprocalPolynomial a = reciprocalPolynomial b → a = b :=
        fun a ha b hb hab => hblocks.bijOn.injOn (hP₀.1 a ha).1 (hP₀.1 b hb).1 hab
      have hMeq : ∑ k ∈ P₀.image reciprocalPolynomial, M k = ∑ k ∈ P₀, M k := by
        rw [Finset.sum_image hinj]
        apply Finset.sum_congr rfl
        intro k hk
        exact (hblocks.paired ⟨k, (hP₀.1 k hk).1⟩ (hP₀.1 k hk).2).multiplicity_eq.symm
      have hle : 2 * ∑ k ∈ P₀, M k ≤ ∑ k ∈ T, M k := by
        have hsub : P₀ ∪ P₀.image reciprocalPolynomial ⊆ T :=
          Finset.union_subset hP₀T hP₀'T
        have h1 : ∑ k ∈ P₀, M k + ∑ k ∈ P₀.image reciprocalPolynomial, M k ≤
            ∑ k ∈ T, M k := by
          calc ∑ k ∈ P₀, M k + ∑ k ∈ P₀.image reciprocalPolynomial, M k
              = ∑ k ∈ P₀ ∪ P₀.image reciprocalPolynomial, M k :=
                (Finset.sum_union hdisj).symm
            _ ≤ ∑ k ∈ T, M k :=
                Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
        rwa [hMeq, ← two_mul] at h1
      have hP₀zero : ∑ k ∈ P₀, M k = 0 := by
        have := hle
        rw [hEq'] at this
        omega
      have hP₀empty : P₀ = ∅ := by
        rw [← Finset.not_nonempty_iff_eq_empty]
        rintro ⟨k, hk⟩
        have hpos : 0 < M k := ggK1Rk_primaryMultiplicity_pos (hP₀.1 k hk).1
        have hle' : M k ≤ ∑ j ∈ P₀, M j :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) hk
        rw [hP₀zero] at hle'
        omega
      have hTempty : T = ∅ := by
        rw [← Finset.not_nonempty_iff_eq_empty]
        rintro ⟨k, hk⟩
        have hpos : 0 < M k := ggK1Rk_primaryMultiplicity_pos (Finset.mem_filter.mp hk).1
        have hle' : M k ≤ ∑ j ∈ T, M j :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) hk
        rw [hEq', hP₀zero] at hle'
        omega
      have hTfalse : ∀ k ∈ primaryFactors (spEnd x), k ≠ X - 1 → False := by
        intro k hk hne
        have hmem : k ∈ T := Finset.mem_filter.mpr ⟨hk, hne⟩
        rw [hTempty] at hmem
        exact Finset.notMem_empty k hmem
      refine ⟨?_, fun k hk hne => (hTfalse k hk hne).elim,
        fun k hk hne => (hTfalse k hk hne).elim⟩
      intro P hP
      rw [← Finset.not_nonempty_iff_eq_empty]
      rintro ⟨k, hk⟩
      rcases eq_or_ne k (X - 1) with hX | hne
      · exact (hP.1 k hk).2
          (by rw [hX, CFSG.RankThree.Classical.reciprocalPolynomial_X_sub_one])
      · exact hTfalse k (hP.1 k hk).1 hne
    ·
      have hqc : ((Nat.card K : ℕ) : ZMod p) = -1 := by
        rw [hK]
        have h1 : ((2 ^ nf + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hadd
        rw [Nat.cast_add, Nat.cast_one] at h1
        exact eq_neg_of_add_eq_zero_left h1
      have hself : ∀ h ∈ primaryFactors (spEnd x), h ≠ X - 1 → reciprocalPolynomial h = h := by
        intro h hh hne
        exact ggK1Rk_selfDual_of_dvd_add hp0 hK hadd hh hne (hblocks.nontrivial h hh hne)
      have hdeg : ∀ h ∈ primaryFactors (spEnd x), h ≠ X - 1 → h.natDegree = 2 := by
        intro h hh hne
        haveI : Fact (1 < p) := ⟨by omega⟩
        have hrc : ringChar (ZMod p) ≠ 2 := by
          rw [ZMod.ringChar_zmod_n]
          intro h2
          exact h2p (by rw [h2])
        rw [ggK1Rk_natDegree_eq_orderOf hK hp0 hpodd hh hne (hblocks.nontrivial h hh hne),
          hqc, orderOf_neg_one, if_neg hrc]
      refine ⟨?_, hself, hdeg⟩
      intro P hP
      rw [← Finset.not_nonempty_iff_eq_empty]
      rintro ⟨h, hh⟩
      have hmem := hP.1 h hh
      rcases eq_or_ne h (X - 1) with hX | hne
      · exact hmem.2
          (by rw [hX, CFSG.RankThree.Classical.reciprocalPolynomial_X_sub_one])
      · exact hmem.2 (hself h hmem.1 hne).symm

end CFSG.StandardType

end
