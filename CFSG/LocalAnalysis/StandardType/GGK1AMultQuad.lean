module

public import CFSG.LocalAnalysis.StandardType.GGK1ADefs
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeRing
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
public import Mathlib.Algebra.Module.Torsion.Field

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.RankThree.PartOne.KCPrimary

private def pairList (m0 : ℕ) (half : List ℕ) : List ℕ :=
  m0 :: (half ++ half.reverse)

private lemma pairList_length (m0 : ℕ) (half : List ℕ) :
    (pairList m0 half).length = 1 + 2 * half.length := by
  simp [pairList, two_mul]
  omega

private lemma pairList_sum (m0 : ℕ) (half : List ℕ) :
    (pairList m0 half).sum = m0 + 2 * half.sum := by
  simp [pairList, two_mul]

private lemma pairList_getD_zero (m0 : ℕ) (half : List ℕ) :
    (pairList m0 half).getD 0 0 = m0 := by
  simp [pairList]

private lemma pairList_getD_le (m0 : ℕ) {half : List ℕ} {j : ℕ} (hj1 : 1 ≤ j)
    (hj : j ≤ half.length) :
    (pairList m0 half).getD j 0 = half.getD (j - 1) 0 := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [pairList, List.getD_cons_succ, List.getD_append _ _ _ _ (by omega)]
  simp

private lemma pairList_getD_gt (m0 : ℕ) {half : List ℕ} {j : ℕ} (hj : half.length < j)
    (hj2 : j ≤ 2 * half.length) :
    (pairList m0 half).getD j 0 = half.getD (2 * half.length - j) 0 := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [pairList, List.getD_cons_succ,
    List.getD_append_right half half.reverse 0 i (by omega)]
  rw [List.getD_reverse (i - half.length) (by omega)]
  rw [show half.length - 1 - (i - half.length) = 2 * half.length - (i + 1) by omega]

private lemma pairList_getD_mirror (m0 : ℕ) {half : List ℕ} {p : ℕ}
    (hp : p = 2 * half.length + 1) (j : ℕ) (hj : j < p) :
    (pairList m0 half).getD ((p - j) % p) 0 = (pairList m0 half).getD j 0 := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp
  have hjle : j ≤ 2 * half.length := by omega
  have hsub : p - j ≤ 2 * half.length := by omega
  have hsub1 : 1 ≤ p - j := by omega
  have hmod : (p - j) % p = p - j := Nat.mod_eq_of_lt (by omega)
  rw [hmod]
  by_cases hjh : j ≤ half.length
  · have hgt : half.length < p - j := by omega
    rw [pairList_getD_gt m0 hgt hsub, pairList_getD_le m0 hj0 hjh]
    rw [show 2 * half.length - (p - j) = j - 1 by omega]
  · have hle : p - j ≤ half.length := by omega
    have hgt : half.length < j := by omega
    rw [pairList_getD_le m0 hsub1 hle, pairList_getD_gt m0 hgt hjle]
    rw [show (p - j) - 1 = 2 * half.length - j by omega]

private lemma pairList_range_map (m0 : ℕ) (half : List ℕ) :
    (List.range half.length).map (fun j => (pairList m0 half).getD (j + 1) 0) = half := by
  apply List.ext_getElem
  · simp
  · intro i hi1 hi2
    rw [List.getElem_map, List.getElem_range]
    change (m0 :: (half ++ half.reverse)).getD (i + 1) 0 = half[i]
    have hmi : i + 1 < (m0 :: (half ++ half.reverse)).length := by
      rw [List.length_cons, List.length_append, List.length_reverse]
      omega
    rw [List.getD_eq_getElem (m0 :: (half ++ half.reverse)) 0 hmi]
    rw [List.getElem_cons_succ, List.getElem_append_left hi2]

private lemma pairList_padded_length (m0 : ℕ) (L : List ℕ) (h : ℕ)
    (hL : L.length ≤ h) :
    (pairList m0 (L ++ List.replicate (h - L.length) 0)).length = 2 * h + 1 := by
  rw [pairList_length, List.length_append, List.length_replicate, Nat.add_sub_cancel' hL]
  omega

private lemma pairList_padded_sum (m0 : ℕ) (L : List ℕ) (h : ℕ) :
    (pairList m0 (L ++ List.replicate (h - L.length) 0)).sum = m0 + 2 * L.sum := by
  rw [pairList_sum, List.sum_append, List.sum_replicate, smul_eq_mul]
  simp

private lemma pairList_padded_filter_range (m0 : ℕ) (L : List ℕ) (h : ℕ)
    (hL : L.length ≤ h) (hLpos : ∀ y ∈ L, y ≠ 0) :
    ((List.range h).map (fun j =>
      (pairList m0 (L ++ List.replicate (h - L.length) 0)).getD (j + 1) 0)).filter
      (fun j => decide (j ≠ 0)) = L := by
  have hhalf : (L ++ List.replicate (h - L.length) 0).length = h := by
    rw [List.length_append, List.length_replicate, Nat.add_sub_cancel' hL]
  have hmap := pairList_range_map m0 (L ++ List.replicate (h - L.length) 0)
  rw [show List.range h = List.range (L ++ List.replicate (h - L.length) 0).length from
    congrArg List.range hhalf.symm, hmap]
  rw [List.filter_append,
    show (List.replicate (h - L.length) 0).filter (fun j => decide (j ≠ 0)) = [] by
      rw [List.filter_replicate]
      simp,
    List.append_nil, List.filter_eq_self.mpr]
  intro y hy
  exact decide_eq_true (hLpos y hy)

private lemma pairList_padded_properties {p h m0 N : ℕ} {L : List ℕ}
    (hL : L.length ≤ h) (hLpos : ∀ y ∈ L, y ≠ 0) (hN : N = m0 + 2 * L.sum)
    (hp : p = 2 * h + 1) :
    let half : List ℕ := L ++ List.replicate (h - L.length) 0
    let m : List ℕ := pairList m0 half
    m.length = p ∧ m.sum = N ∧ m.getD 0 0 = m0 ∧
      (∀ j, j < p → m.getD ((p - j) % p) 0 = m.getD j 0) ∧
      ((List.range h).map (fun j => m.getD (j + 1) 0)).filter
        (fun j => decide (j ≠ 0)) = L := by
  dsimp only
  have hhalf : (L ++ List.replicate (h - L.length) 0).length = h := by
    rw [List.length_append, List.length_replicate, Nat.add_sub_cancel' hL]
  refine ⟨?_, ?_, pairList_getD_zero _ _, ?_, ?_⟩
  · rw [pairList_padded_length _ _ _ hL]
    exact hp.symm
  · rw [pairList_padded_sum]
    exact hN.symm
  · intro j hj
    exact pairList_getD_mirror m0 (by rw [hhalf]; exact hp) j hj
  · exact pairList_padded_filter_range m0 L h hL hLpos

private lemma two_mul_half_add_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p = 2 * ((p - 1) / 2) + 1 := by
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
  have h : (p - 1) / 2 = k := by
    rw [show p - 1 = 2 * k by omega, Nat.mul_div_cancel_left k (by norm_num)]
  omega

private lemma mem_selfDualFactors {N : ℕ} {K : Type} [Field K] {g : GL (Fin N) K}
    {a : K[X]} :
    a ∈ ggK1A_selfDualFactors g ↔
      a ∈ primaryFactors (ggK1A_glEnd g) ∧ a ≠ X - 1 := by
  classical
  simp [ggK1A_selfDualFactors]

private lemma orderOf_cast_two_pow_eq_two {p nf : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hord : ggMultOrd p nf = 2) :
    orderOf ((2 ^ nf : ℕ) : ZMod p) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : p ∣ 2 ^ nf + 1 := by
    by_contra h
    have hsub : ¬ p ∣ 2 ^ nf - 1 := by
      intro h1
      rw [ggMultOrd, if_pos h1] at hord
      omega
    rw [ggMultOrd, if_neg hsub, if_neg h] at hord
    omega
  have hcast : ((2 ^ nf : ℕ) : ZMod p) = -1 := by
    have h0 : ((2 ^ nf + 1 : ℕ) : ZMod p) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact hdvd
    have h1 : ((2 ^ nf : ℕ) : ZMod p) + 1 = 0 := by
      simpa using h0
    calc ((2 ^ nf : ℕ) : ZMod p) = ((2 ^ nf : ℕ) : ZMod p) + 1 - 1 := by ring
      _ = -1 := by rw [h1]; ring
  have hsq : ((2 ^ nf : ℕ) : ZMod p) ^ 2 = 1 := by
    rw [hcast]
    ring
  have hne : ((2 ^ nf : ℕ) : ZMod p) ≠ 1 := by
    rw [hcast]
    intro h
    rcases ZMod.neg_one_eq_one_iff.mp h with h1 | h1
    · exact hp.ne_one h1
    · exact hp2 h1
  exact orderOf_eq_prime hsq hne

private lemma dvd_cyclotomic_of_mem_selfDual {p N : ℕ} {K : Type} [Field K]
    (hp : p.Prime) {g : GL (Fin N) K} (hg : ggK1A_glEnd g ^ p = 1)
    {a : K[X]} (ha : a ∈ ggK1A_selfDualFactors g) :
    a ∣ cyclotomic p K := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨haF, hane⟩ := mem_selfDualFactors.mp ha
  have hirr := irreducible_of_mem_primaryFactors haF
  have hmon := monic_of_mem_primaryFactors haF
  have hmin : minpoly K (ggK1A_glEnd g) ∣ X ^ p - 1 := by
    apply minpoly.dvd
    simp [hg]
  have hdvd0 : a ∣ cyclotomic p K * (X - 1) := by
    rw [cyclotomic_prime_mul_X_sub_one K p]
    exact dvd_trans (mem_primaryFactors.mp haF).2.2 hmin
  have hXirr : Irreducible (X - 1 : K[X]) := by
    simpa using irreducible_X_sub_C (1 : K)
  have hXmon : (X - 1 : K[X]).Monic := by
    simpa using monic_X_sub_C (1 : K)
  have hcop : IsCoprime a (X - 1) := by
    rw [hirr.coprime_iff_not_dvd]
    intro hdvd1
    exact hane (eq_of_monic_of_associated hmon hXmon (hirr.associated_of_dvd hXirr hdvd1))
  exact hcop.dvd_of_dvd_mul_right hdvd0

private lemma natDegree_eq_two_of_mem_selfDual {p nf N : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = 2 ^ nf) (hord : ggMultOrd p nf = 2)
    {g : GL (Fin N) K} (hg : ggK1A_glEnd g ^ p = 1)
    {a : K[X]} (ha : a ∈ ggK1A_selfDualFactors g) :
    a.natDegree = 2 := by
  classical
  let : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Fintype.card K = 2 ^ nf := by rwa [Nat.card_eq_fintype_card] at hK
  have hirr := irreducible_of_mem_primaryFactors (mem_selfDualFactors.mp ha).1
  have hcop2 : Nat.Coprime 2 p :=
    Nat.prime_two.coprime_iff_not_dvd.mpr fun h =>
      hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h).symm
  have hdeg := natDegree_of_dvd_cyclotomic_of_irreducible (K := K) (p := 2) (f := nf)
    (n := p) (P := a) hcard hcop2 (dvd_cyclotomic_of_mem_selfDual hp hg ha) hirr
  rw [hdeg, ← orderOf_units, ZMod.coe_unitOfCoprime]
  exact orderOf_cast_two_pow_eq_two hp hp2 hord

private lemma finrank_primaryComponent_eq_two_mul_primaryMultiplicity {p nf N : ℕ}
    {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = 2 ^ nf) (hord : ggMultOrd p nf = 2)
    {g : GL (Fin N) K} (hg : ggK1A_glEnd g ^ p = 1)
    {a : K[X]} (ha : a ∈ ggK1A_selfDualFactors g) :
    Module.finrank K (primaryComponent (ggK1A_glEnd g) a) =
      2 * primaryMultiplicity (ggK1A_glEnd g) a := by
  have hmem := (mem_selfDualFactors.mp ha).1
  have : Fact (Irreducible a) := ⟨irreducible_of_mem_primaryFactors hmem⟩
  rw [finrank_primaryComponent (ggK1A_glEnd g) a,
    natDegree_eq_two_of_mem_selfDual hp hp2 hK hord hg ha]

private lemma card_selfDualFactors_le {p nf N : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = 2 ^ nf) (hord : ggMultOrd p nf = 2)
    {g : GL (Fin N) K} (hg : ggK1A_glEnd g ^ p = 1) :
    (ggK1A_selfDualFactors g).card ≤ (p - 1) / 2 := by
  classical
  set S := ggK1A_selfDualFactors g with hSdef
  have hpair : (S : Set K[X]).Pairwise IsCoprime := by
    intro a ha b hb hab
    exact isCoprime_of_mem_primaryFactors
      (mem_selfDualFactors.mp ha).1 (mem_selfDualFactors.mp hb).1 hab
  have hdvd : (∏ a ∈ S, a) ∣ cyclotomic p K :=
    Finset.prod_dvd_of_coprime hpair fun a ha =>
      dvd_cyclotomic_of_mem_selfDual hp hg ha
  have hmon : ∀ a ∈ S, a.Monic := fun a ha =>
    monic_of_mem_primaryFactors (mem_selfDualFactors.mp ha).1
  have hdeg_prod : (∏ a ∈ S, a).natDegree = 2 * S.card := by
    rw [natDegree_prod_of_monic S (fun a => a) hmon]
    rw [Finset.sum_const_nat (m := 2)
      (fun a ha => natDegree_eq_two_of_mem_selfDual hp hp2 hK hord hg ha)]
    rw [mul_comm]
  have hle : 2 * S.card ≤ p - 1 := by
    have h := Polynomial.Monic.natDegree_le_of_dvd
      (monic_prod_of_monic S (fun a => a) hmon) (cyclotomic_ne_zero p K) hdvd
    rw [hdeg_prod, natDegree_cyclotomic p K, Nat.totient_prime hp] at h
    exact h
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
  have hpk : p - 1 = 2 * k := by omega
  have hdiv : (p - 1) / 2 = k := by
    rw [hpk, Nat.mul_div_cancel_left k (by norm_num)]
  rw [hdiv]
  omega

private lemma finrank_eq_head_add_two_sum {N : ℕ} {K : Type} [Field K] [DecidableEq K[X]]
    {x : Module.End K (Fin N → K)} (hsq : Squarefree (minpoly K x))
    (S : Finset K[X]) (hS : S = (primaryFactors x).filter (fun a => a ≠ X - 1))
    (hdeg : ∀ a ∈ S, Module.finrank K (primaryComponent x a) =
      2 * primaryMultiplicity x a) :
    N = Module.finrank K (primaryComponent x (X - 1)) +
      2 * ∑ a ∈ S, primaryMultiplicity x a := by
  classical
  have hXirr : Irreducible (X - 1 : K[X]) := by
    simpa using irreducible_X_sub_C (1 : K)
  have hXmon : (X - 1 : K[X]).Monic := by
    simpa using monic_X_sub_C (1 : K)
  have hSerase : S = (primaryFactors x).erase (X - 1) := by
    rw [hS, Finset.filter_ne']
  have hN : N = ∑ a ∈ primaryFactors x, Module.finrank K (primaryComponent x a) :=
    (show N = Module.finrank K (Fin N → K) from by simp).trans
      ((finrank_eq_sum_primaryComponent hsq).trans
        (Finset.sum_coe_sort (primaryFactors x)
          (fun a : K[X] => Module.finrank K (primaryComponent x a))))
  by_cases hmem : (X - 1 : K[X]) ∈ primaryFactors x
  · have hsum := Finset.add_sum_erase (primaryFactors x)
      (fun a => Module.finrank K (primaryComponent x a)) hmem
    calc N = ∑ a ∈ primaryFactors x, Module.finrank K (primaryComponent x a) := hN
      _ = Module.finrank K (primaryComponent x (X - 1)) +
            ∑ a ∈ (primaryFactors x).erase (X - 1), Module.finrank K
              (primaryComponent x a) := hsum.symm
      _ = Module.finrank K (primaryComponent x (X - 1)) +
            ∑ a ∈ S, Module.finrank K (primaryComponent x a) := by
            rw [← hSerase]
      _ = Module.finrank K (primaryComponent x (X - 1)) +
            2 * ∑ a ∈ S, primaryMultiplicity x a := by
            congr 1
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun a ha => hdeg a ha
  · have herase : (primaryFactors x).erase (X - 1) = primaryFactors x :=
      Finset.erase_eq_of_notMem hmem
    have hbot : primaryComponent x (X - 1) = ⊥ :=
      CFSG.RankThree.Classical.primaryComponent_eq_bot_of_not_mem hXirr hXmon hmem
    have hSF : S = primaryFactors x := by rw [hSerase, herase]
    calc N = ∑ a ∈ primaryFactors x, Module.finrank K (primaryComponent x a) := hN
      _ = Module.finrank K (primaryComponent x (X - 1)) +
            2 * ∑ a ∈ S, primaryMultiplicity x a := by
            rw [hbot, finrank_bot, zero_add, hSF, Finset.mul_sum]
            exact Finset.sum_congr rfl fun a ha => hdeg a (hSF.symm ▸ ha)

private lemma finrank_eq_selfDualFactors_head_add_two_sum {p nf N : ℕ} {K : Type}
    [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = 2 ^ nf) (hord : ggMultOrd p nf = 2)
    {g : GL (Fin N) K} (hg : ggK1A_glEnd g ^ p = 1)
    (hsq : Squarefree (minpoly K (ggK1A_glEnd g))) :
    N = Module.finrank K (primaryComponent (ggK1A_glEnd g) (X - 1)) +
      2 * ∑ a ∈ ggK1A_selfDualFactors g,
        primaryMultiplicity (ggK1A_glEnd g) a := by
  classical
  exact finrank_eq_head_add_two_sum hsq _ rfl
    (fun a ha =>
      finrank_primaryComponent_eq_two_mul_primaryMultiplicity hp hp2 hK hord hg ha)

private lemma selfDualFactors_toList_map_primaryMultiplicity_ne_zero {N : ℕ} {K : Type}
    [Field K] {g : GL (Fin N) K}
    (hsq : Squarefree (minpoly K (ggK1A_glEnd g))) :
    ∀ y ∈ (ggK1A_selfDualFactors g).toList.map
        (primaryMultiplicity (ggK1A_glEnd g)), y ≠ 0 := by
  intro y hy
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
  exact ne_of_gt (CFSG.RankThree.PartOne.KCUnitaryModel.primaryMultiplicity_pos hsq
    ⟨a, (mem_selfDualFactors.mp (Finset.mem_toList.mp ha)).1⟩)

private lemma multiset_selfDualFactors_toList_map_primaryMultiplicity {N : ℕ} {K : Type}
    [Field K] {g : GL (Fin N) K} :
    (↑((ggK1A_selfDualFactors g).toList.map
        (primaryMultiplicity (ggK1A_glEnd g))) : Multiset ℕ) =
      (ggK1A_selfDualFactors g).val.map (primaryMultiplicity (ggK1A_glEnd g)) := by
  rw [← Multiset.map_coe, Finset.coe_toList]

theorem ggK1A_multOf_of_ggMultOrd_eq_two {p nf N : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = 2 ^ nf) (hord : ggMultOrd p nf = 2)
    {g : GL (Fin N) K} (hg : ggK1A_glEnd g ^ p = 1)
    (hsq : Squarefree (minpoly K (ggK1A_glEnd g))) :
    ∃ m : List ℕ, GGK1AMultOf p nf N false K g m := by
  classical
  let x : Module.End K (Fin N → K) := ggK1A_glEnd g
  let S : Finset K[X] := ggK1A_selfDualFactors g
  let h : ℕ := (p - 1) / 2
  let m0 : ℕ := Module.finrank K (primaryComponent x (X - 1))
  let L : List ℕ := S.toList.map (primaryMultiplicity x)
  let m : List ℕ := pairList m0 (L ++ List.replicate (h - L.length) 0)
  have hsq' : Squarefree (minpoly K x) := hsq
  have hLlen : L.length = S.card := by
    dsimp only [L]
    rw [List.length_map, Finset.length_toList]
  have hSle : S.card ≤ h := card_selfDualFactors_le hp hp2 hK hord hg
  have hLpos : ∀ y ∈ L, y ≠ 0 := by
    dsimp only [L, S, x]
    exact selfDualFactors_toList_map_primaryMultiplicity_ne_zero hsq'
  have hLsum : L.sum = ∑ a ∈ S, primaryMultiplicity x a := by
    dsimp only [L]
    exact Finset.sum_map_toList S (primaryMultiplicity x)
  have hN : N = m0 + 2 * L.sum := by
    dsimp only [m0]
    rw [hLsum]
    exact finrank_eq_selfDualFactors_head_add_two_sum hp hp2 hK hord hg hsq'
  obtain ⟨hmlen, hsum, hhead, hmirror, hfilter⟩ :=
    pairList_padded_properties (by rw [hLlen]; exact hSle) hLpos hN
      (two_mul_half_add_one hp hp2)
  refine ⟨m, hmlen, hsum, by simpa only [m0, x] using hhead,
    Or.inl ⟨⟨hord, rfl⟩, hmirror, ?_⟩⟩
  rw [show (p - 1) / 2 = h from rfl, hfilter]
  dsimp only [L, S, x]
  exact multiset_selfDualFactors_toList_map_primaryMultiplicity

end CFSG.StandardType

end
