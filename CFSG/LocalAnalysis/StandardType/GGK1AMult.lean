module

public import CFSG.LocalAnalysis.StandardType.GGK1ADefs
public import CFSG.LocalAnalysis.StandardType.GGK1AMultQuad
public import CFSG.LocalAnalysis.StandardType.GGK1AMultUni
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusTwistedAFactors
public import CFSG.LinearAlgebra.OddSolvableUnitary.ExtraspecialModule
public import CFSG.RankThree.PartOne.KC.LinearCommutantFactors
public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryAlgebra
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel
public import CFSG.RankThree.PartOne.CTP.Spectrum4
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusTwistedAKit
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryFlag

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.LieType.SemisimpleCentralizers.Held CFSG.LieType.SemisimpleCentralizers.HeldLang

private lemma mem_primaryFactors_iff_exists_isPrimitiveRoot_pow {p N : ℕ} {K : Type} [Field K]
    {x : Module.End K (Fin N → K)} {ζ : K} (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p)
    (hx : x ^ p = 1) (hsq : Squarefree (minpoly K x)) {a : K[X]} :
    a ∈ primaryFactors x ↔
      ∃ j : Fin p, a = X - C (ζ ^ (j : ℕ)) ∧
        primaryComponent x (X - C (ζ ^ (j : ℕ))) ≠ ⊥ := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hx' : aeval x (X ^ p - C (1 : K)) = 0 := by
    simp [hx]
  constructor
  · intro ha
    obtain ⟨ν, hνa, hνpow⟩ :=
      CFSG.AGLEmbedding.ToralCensus.exists_eq_X_sub_C_of_mem_primaryFactors hp.pos hζ
        (one_pow p) hx' ha
    obtain ⟨j, hj, hji⟩ := hζ.eq_pow_of_pow_eq_one hνpow
    refine ⟨⟨j, hj⟩, ?_, ?_⟩
    · rw [hνa, ← hji]
    · rw [hji, ← hνa]
      exact primaryComponent_ne_bot hsq ha
  · rintro ⟨j, rfl, hne⟩
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hxv : x v = (ζ ^ (j : ℕ)) • v := by
      have h0 := mem_primaryComponent.mp hv
      rw [map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] at h0
      simpa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] using h0
    have hev : x.HasEigenvalue (ζ ^ (j : ℕ)) :=
      Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.mpr hxv, hv0⟩
    have hroot : (minpoly K x).IsRoot (ζ ^ (j : ℕ)) :=
      (Module.End.hasEigenvalue_iff_isRoot).mp hev
    exact mem_primaryFactors.mpr
      ⟨irreducible_X_sub_C _, monic_X_sub_C _, dvd_iff_isRoot.mpr hroot⟩

private lemma primaryMultiplicity_X_sub_C_eq_finrank {N : ℕ} {K : Type} [Field K]
    (x : Module.End K (Fin N → K)) (μ : K) :
    primaryMultiplicity x (X - C μ) = Module.finrank K (x.eigenspace μ) := by
  rw [CFSG.RankThree.PartOne.KCSpIsotypic.primaryMultiplicity_X_sub_C_eq]
  rw [Module.End.eigenspace_def, primaryComponent, map_sub, aeval_X, aeval_C,
    Algebra.algebraMap_eq_smul_one]

private lemma sum_finrank_eigenspace_eq_sum_range {p N : ℕ} {K : Type} [Field K]
    (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p) {x : Module.End K (Fin N → K)}
    (hx : x ^ p = 1) :
    (∑ j ∈ Finset.range p, Module.finrank K (x.eigenspace (ζ ^ j))) = N := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have h := CFSG.OddSolvableUnitary.finrank_eq_sum_finrank_eigenspace hp.pos hζ hx
    (F := K) (W := Fin N → K) (b := x)
  have hfin : Module.finrank K (Fin N → K) = N := by simp
  have h2 : (∑ j ∈ Finset.range p, Module.finrank K (x.eigenspace (ζ ^ j))) =
      ∑ μ ∈ nthRootsFinset p 1, Module.finrank K (x.eigenspace μ) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun j : ℕ => Module.finrank K (x.eigenspace (ζ ^ j)))]
    refine Finset.sum_bij (fun j _ => ζ ^ (j : ℕ)) ?_ ?_ ?_ ?_
    · intro j _
      rw [mem_nthRootsFinset hp.pos, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    · intro j _ k _ hjk
      exact Fin.ext (hζ.pow_inj j.2 k.2 hjk)
    · intro μ hμ
      rw [mem_nthRootsFinset hp.pos] at hμ
      obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ
      exact ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩
    · intro j _
      rfl
  calc (∑ j ∈ Finset.range p, Module.finrank K (x.eigenspace (ζ ^ j)))
      = ∑ μ ∈ nthRootsFinset p 1, Module.finrank K (x.eigenspace μ) := h2
    _ = Module.finrank K (Fin N → K) := h.symm
    _ = N := hfin

private lemma primaryMultiplicity_X_sub_C_ne_zero_iff {N : ℕ} {K : Type} [Field K]
    (x : Module.End K (Fin N → K)) (μ : K) :
    primaryMultiplicity x (X - C μ) ≠ 0 ↔ primaryComponent x (X - C μ) ≠ ⊥ := by
  have hcomp : primaryComponent x (X - C μ) = x.eigenspace μ := by
    rw [Module.End.eigenspace_def, primaryComponent]
    simp [Algebra.algebraMap_eq_smul_one]
  rw [primaryMultiplicity_X_sub_C_eq_finrank, hcomp]
  exact not_congr Submodule.finrank_eq_zero

private lemma mem_selfDualFactors_iff {p N : ℕ} {K : Type} [Field K]
    {g : GL (Fin N) K} {ζ : K} (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p)
    (hx : ggK1A_glEnd g ^ p = 1) (hsq : Squarefree (minpoly K (ggK1A_glEnd g)))
    {a : K[X]} :
    a ∈ ggK1A_selfDualFactors g ↔
      ∃ j, j ∈ Finset.Ico 1 p ∧
        primaryMultiplicity (ggK1A_glEnd g) (X - C (ζ ^ j)) ≠ 0 ∧
          a = X - C (ζ ^ j) := by
  classical
  rw [ggK1A_selfDualFactors]
  simp only [Finset.mem_filter, Finset.mem_Ico,
    mem_primaryFactors_iff_exists_isPrimitiveRoot_pow hp hζ hx hsq]
  constructor
  · rintro ⟨⟨j, rfl, hcomp⟩, hne⟩
    have hj : (j : ℕ) < p := j.2
    have hj1 : 0 < (j : ℕ) := by
      rcases Nat.eq_zero_or_pos (j : ℕ) with h | h
      · exfalso
        apply hne
        rw [h]
        simp
      · exact h
    refine ⟨(j : ℕ), ⟨hj1, hj⟩, ?_, rfl⟩
    rw [primaryMultiplicity_X_sub_C_ne_zero_iff]
    exact hcomp
  · rintro ⟨j, ⟨hj1, hj⟩, hfj, rfl⟩
    refine ⟨⟨⟨j, hj⟩, rfl, ?_⟩, ?_⟩
    · rw [← primaryMultiplicity_X_sub_C_ne_zero_iff]
      exact hfj
    · intro h
      have hζj : ζ ^ j = 1 := by
        have := congrArg (fun q : K[X] => q.eval 0) h
        simpa using this
      have h0 : j = 0 := hζ.pow_inj hj (Nat.zero_lt_of_lt hp.pos) (by simpa using hζj)
      omega

private lemma selfDualFactors_val_eq {p N : ℕ} {K : Type} [Field K]
    {g : GL (Fin N) K} {ζ : K} (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p)
    (hx : ggK1A_glEnd g ^ p = 1) (hsq : Squarefree (minpoly K (ggK1A_glEnd g))) :
    (ggK1A_selfDualFactors g).val =
      ((Finset.Ico 1 p).filter (fun j =>
        primaryMultiplicity (ggK1A_glEnd g) (X - C (ζ ^ j)) ≠ 0)).val.map
        (fun j => X - C (ζ ^ j)) := by
  classical
  have hset : ggK1A_selfDualFactors g =
      ((Finset.Ico 1 p).filter (fun j =>
        primaryMultiplicity (ggK1A_glEnd g) (X - C (ζ ^ j)) ≠ 0)).image
        (fun j => X - C (ζ ^ j)) := by
    ext a
    rw [mem_selfDualFactors_iff hp hζ hx hsq]
    constructor
    · rintro ⟨j, hjIco, hfj, rfl⟩
      exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨hjIco, hfj⟩, rfl⟩
    · intro ha
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨hjIco, hfj⟩ := Finset.mem_filter.mp hj
      exact ⟨j, hjIco, hfj, rfl⟩
  rw [hset]
  have hinj : Set.InjOn (fun j => X - C (ζ ^ j))
      ↑((Finset.Ico 1 p).filter (fun j =>
        primaryMultiplicity (ggK1A_glEnd g) (X - C (ζ ^ j)) ≠ 0)) := by
    intro i hi k hk hik
    have hi' : i < p := (Finset.mem_Ico.mp (Finset.mem_filter.mp hi).1).2
    have hk' : k < p := (Finset.mem_Ico.mp (Finset.mem_filter.mp hk).1).2
    have h : ζ ^ i = ζ ^ k := by
      have := congrArg (fun q : K[X] => q.eval 0) hik
      simpa using this
    exact hζ.pow_inj hi' hk' h
  rw [Finset.image_val_of_injOn hinj]

private lemma selfDualFactors_multiplicity_eq {p N : ℕ} {K : Type} [Field K]
    {g : GL (Fin N) K} {ζ : K} (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p)
    (hx : ggK1A_glEnd g ^ p = 1) (hsq : Squarefree (minpoly K (ggK1A_glEnd g))) :
    (ggK1A_selfDualFactors g).val.map (primaryMultiplicity (ggK1A_glEnd g)) =
      ((Finset.Ico 1 p).filter (fun j =>
        primaryMultiplicity (ggK1A_glEnd g) (X - C (ζ ^ j)) ≠ 0)).val.map
        (fun j => primaryMultiplicity (ggK1A_glEnd g) (X - C (ζ ^ j))) := by
  classical
  rw [selfDualFactors_val_eq hp hζ hx hsq, Multiset.map_map]
  rfl

private lemma sum_map_primaryMultiplicity_eq {p N : ℕ} {K : Type} [Field K]
    {x : Module.End K (Fin N → K)} {ζ : K} (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p)
    (hx : x ^ p = 1) :
    ((List.range p).map (fun j => primaryMultiplicity x (X - C (ζ ^ j)))).sum = N := by
  have h1 : ((List.range p).map (fun j => primaryMultiplicity x (X - C (ζ ^ j)))).sum =
      ∑ j ∈ Finset.range p, Module.finrank K (x.eigenspace (ζ ^ j)) := by
    rw [Finset.sum_eq_multiset_sum, Finset.range_val, ← Multiset.coe_range, Multiset.map_coe,
      Multiset.sum_coe]
    refine congrArg List.sum (List.map_congr_left fun j _ => ?_)
    exact primaryMultiplicity_X_sub_C_eq_finrank x (ζ ^ j)
  rw [h1, sum_finrank_eigenspace_eq_sum_range hp hζ hx]

private lemma split_multiset_eq {p N : ℕ} {K : Type} [Field K]
    {g : GL (Fin N) K} {ζ : K} (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p)
    (hx : ggK1A_glEnd g ^ p = 1) (hsq : Squarefree (minpoly K (ggK1A_glEnd g))) :
    Multiset.ofList (((List.range p).map
        (fun j => primaryMultiplicity (ggK1A_glEnd g) (X - C (ζ ^ j)))).tail.filter
        (fun j => decide (j ≠ 0))) =
      (ggK1A_selfDualFactors g).val.map (primaryMultiplicity (ggK1A_glEnd g)) := by
  classical
  have htail : ((List.range p).map
      (fun j => primaryMultiplicity (ggK1A_glEnd g) (X - C (ζ ^ j)))).tail =
      (List.range' 1 (p - 1)).map
        (fun j => primaryMultiplicity (ggK1A_glEnd g) (X - C (ζ ^ j))) := by
    rw [← List.map_tail, List.tail_range]
  have hleft : Multiset.ofList (((List.range p).map
        (fun j => primaryMultiplicity (ggK1A_glEnd g) (X - C (ζ ^ j)))).tail.filter
        (fun j => decide (j ≠ 0))) =
      ((Finset.Ico 1 p).filter (fun j =>
        primaryMultiplicity (ggK1A_glEnd g) (X - C (ζ ^ j)) ≠ 0)).val.map
        (fun j => primaryMultiplicity (ggK1A_glEnd g) (X - C (ζ ^ j))) := by
    rw [htail, ← Multiset.filter_coe (p := fun n => n ≠ 0), ← Multiset.map_coe,
      Multiset.filter_map, Nat.Ico_eq_range', Finset.filter_val]
    rfl
  exact hleft.trans (selfDualFactors_multiplicity_eq hp hζ hx hsq).symm

private lemma blocks_eq_of_isPrimitiveRoot {p nf N : ℕ} {K : Type} [Field K]
    {g : GL (Fin N) K} {ζ : K} {m : List ℕ} {tw : Bool} (hp : p.Prime)
    (hζ : IsPrimitiveRoot ζ p) (hx : ggK1A_glEnd g ^ p = 1)
    (hsq : Squarefree (minpoly K (ggK1A_glEnd g)))
    (hm : m = (List.range p).map
      (fun j => primaryMultiplicity (ggK1A_glEnd g) (X - C (ζ ^ j))))
    (hnot : ¬(ggMultOrd p nf = 2 ∧ tw = false))
    (hsym : ggMultOrd p nf = 1 ∧ tw = true → ∀ j, j < p →
      primaryMultiplicity (ggK1A_glEnd g) (X - C (ζ ^ ((p - j) % p))) =
        primaryMultiplicity (ggK1A_glEnd g) (X - C (ζ ^ j))) :
    (((ggMultOrd p nf = 2 ∧ tw = false) ∧
        (∀ j, j < p → m.getD ((p - j) % p) 0 = m.getD j 0) ∧
        Multiset.ofList (((List.range ((p - 1) / 2)).map (fun j => m.getD (j + 1) 0)).filter
            (fun j => decide (j ≠ 0))) =
          (ggK1A_selfDualFactors g).val.map (primaryMultiplicity (ggK1A_glEnd g))) ∨
      (¬ (ggMultOrd p nf = 2 ∧ tw = false) ∧
        (ggMultOrd p nf = 1 ∧ tw = true →
          ∀ j, j < p → m.getD ((p - j) % p) 0 = m.getD j 0) ∧
        Multiset.ofList (m.tail.filter (fun j => decide (j ≠ 0))) =
          (ggK1A_selfDualFactors g).val.map (primaryMultiplicity (ggK1A_glEnd g)))) := by
  have hget : ∀ j, j < p → m.getD j 0 =
      primaryMultiplicity (ggK1A_glEnd g) (X - C (ζ ^ j)) := by
    intro j hj
    rw [hm, List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hj)]
    simp
  right
  refine ⟨hnot, ?_, ?_⟩
  · intro hsym' j hj
    rw [hget ((p - j) % p) (Nat.mod_lt _ hp.pos), hget j hj]
    exact hsym hsym' j hj
  · rw [hm]
    exact split_multiset_eq hp hζ hx hsq

private lemma exists_mult_of_isPrimitiveRoot {p nf mcard N : ℕ} {K : Type} [Field K]
    [Finite K] {g : GL (Fin N) K} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcard : Nat.card K = 2 ^ mcard)
    (hgp : g ^ p = 1) {ζ : K} (hζ : IsPrimitiveRoot ζ p) (tw : Bool)
    (hnot : ¬(ggMultOrd p nf = 2 ∧ tw = false))
    (hsym : ggMultOrd p nf = 1 ∧ tw = true → ∀ j, j < p →
      primaryMultiplicity (ggK1A_glEnd g) (X - C (ζ ^ ((p - j) % p))) =
        primaryMultiplicity (ggK1A_glEnd g) (X - C (ζ ^ j))) :
    ∃ m : List ℕ, GGK1AMultOf p nf N tw K g m := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxpow : ggK1A_glEnd g ^ p = 1 := by
    rw [← ggK1A_glEnd_pow, hgp, ggK1A_glEnd_one]
  have : CharP K 2 := charP_two_of_card hcard
  have hsq : Squarefree (minpoly K (ggK1A_glEnd g)) :=
    CFSG.RankThree.PartOne.KCLinComm.squarefree_minpoly_of_pow_eq_one
      (TableBSymp.natCast_ne_zero_of_charTwo hp hp2) hxpow
  set x : Module.End K (Fin N → K) := ggK1A_glEnd g with hxdef
  let f : ℕ → ℕ := fun j => primaryMultiplicity x (X - C (ζ ^ j))
  let m : List ℕ := (List.range p).map f
  have hget : ∀ i, i < p → m.getD i 0 = f i := by
    intro i hi
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hi)]
    simp [m, List.getElem_map, List.getElem_range]
  have hlen : m.length = p := by simp [m]
  have hsum : m.sum = N := by
    simpa only [m, f] using sum_map_primaryMultiplicity_eq (x := x) hp hζ hxpow
  have hcomp : primaryComponent x (X - 1) = x.eigenspace (1 : K) := by
    rw [Module.End.eigenspace_def, primaryComponent]
    simp
  have hhead : m.getD 0 0 = Module.finrank K (primaryComponent x (X - 1)) := by
    rw [hget 0 hp.pos]
    show primaryMultiplicity x (X - C (ζ ^ 0)) = _
    rw [pow_zero]
    calc primaryMultiplicity x (X - C (1 : K))
        = Module.finrank K (x.eigenspace (1 : K)) :=
          primaryMultiplicity_X_sub_C_eq_finrank x 1
      _ = Module.finrank K (primaryComponent x (X - 1)) := by rw [hcomp]
  have hblocks := blocks_eq_of_isPrimitiveRoot (m := m) hp hζ hxpow hsq
    (by simp only [m, f, hxdef]) hnot hsym
  exact ⟨m, hlen, hsum, hhead, hblocks⟩

theorem ggK1A_mult_exists {p nf N : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = 2 ^ nf)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    {xhat : ↥(LargeEvenSLGroup (Fin N) K)} (hxp : xhat ^ p = 1) :
    ∃ m : List ℕ, GGK1AMultOf p nf N false K (xhat : GL (Fin N) K) m := by
  classical
  have hgp : (xhat : GL (Fin N) K) ^ p = 1 := by
    simpa using congrArg Subtype.val hxp
  have hxpow : ggK1A_glEnd (xhat : GL (Fin N) K) ^ p = 1 := by
    rw [← ggK1A_glEnd_pow, hgp, ggK1A_glEnd_one]
  have : CharP K 2 := charP_two_of_card hK
  have hsq : Squarefree (minpoly K (ggK1A_glEnd (xhat : GL (Fin N) K))) :=
    CFSG.RankThree.PartOne.KCLinComm.squarefree_minpoly_of_pow_eq_one
      (TableBSymp.natCast_ne_zero_of_charTwo hp hp2) hxpow
  rcases hdvd with h1 | h2
  · have hord : ggMultOrd p nf = 1 := by rw [ggMultOrd, if_pos h1]
    obtain ⟨ζ, hζ⟩ :=
      CFSG.RankThree.PartOne.CTP.exists_isPrimitiveRoot_of_dvd_natCard_sub_one (m := p)
        (by rwa [hK])
    refine exists_mult_of_isPrimitiveRoot hp hp2 hK hgp hζ false ?_ ?_
    · rintro ⟨h, -⟩
      rw [hord] at h
      omega
    · intro h
      exact absurd h.2 (by simp)
  · have hn1 : ¬ p ∣ 2 ^ nf - 1 := by
      intro h0
      have hsub : p ∣ (2 ^ nf + 1) - (2 ^ nf - 1) := Nat.dvd_sub h2 h0
      have htwo : (2 ^ nf + 1) - (2 ^ nf - 1) = 2 := by
        have hle := Nat.one_le_two_pow (n := nf)
        omega
      rw [htwo] at hsub
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hsub)
    have hord : ggMultOrd p nf = 2 := by
      rw [ggMultOrd, if_neg hn1, if_pos h2]
    exact ggK1A_multOf_of_ggMultOrd_eq_two hp hp2 hK hord hxpow hsq

theorem ggK1A_uni_mult_exists {p nf N : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (2 ^ nf) ^ 2)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    {xhat : ↥(LargeEvenSUGroup (Fin N) K (2 ^ nf))} (hxp : xhat ^ p = 1) :
    ∃ m : List ℕ, GGK1AMultOf p nf N true K (xhat : GL (Fin N) K) m := by
  classical
  have hgp : (xhat : GL (Fin N) K) ^ p = 1 := by
    simpa using congrArg Subtype.val hxp
  have hxpow : ggK1A_glEnd (xhat : GL (Fin N) K) ^ p = 1 := by
    rw [← ggK1A_glEnd_pow, hgp, ggK1A_glEnd_one]
  have hcard : Nat.card K = 2 ^ (2 * nf) := by
    rw [hK, ← pow_mul, Nat.mul_comm nf 2]
  have : CharP K 2 := charP_two_of_card hcard
  have hsq : Squarefree (minpoly K (ggK1A_glEnd (xhat : GL (Fin N) K))) :=
    CFSG.RankThree.PartOne.KCLinComm.squarefree_minpoly_of_pow_eq_one
      (TableBSymp.natCast_ne_zero_of_charTwo hp hp2) hxpow
  have hfac : (2 ^ nf) ^ 2 - 1 = (2 ^ nf + 1) * (2 ^ nf - 1) := by
    obtain ⟨t, ht⟩ : ∃ t, 2 ^ nf = t + 1 :=
      ⟨2 ^ nf - 1, by have := Nat.one_le_two_pow (n := nf); omega⟩
    rw [ht]
    have h : (t + 1) ^ 2 = (t + 1 + 1) * t + 1 := by ring
    rw [h, Nat.add_sub_cancel, Nat.add_sub_cancel]
  have hdvd' : p ∣ Nat.card K - 1 := by
    rw [hK, hfac]
    rcases hdvd with h | h
    · exact h.mul_left _
    · exact h.mul_right _
  obtain ⟨ζ, hζ⟩ :=
    CFSG.RankThree.PartOne.CTP.exists_isPrimitiveRoot_of_dvd_natCard_sub_one (m := p) hdvd'
  refine exists_mult_of_isPrimitiveRoot hp hp2 hcard hgp hζ true ?_ ?_
  · rintro ⟨-, h⟩
    exact absurd h (by simp)
  · rintro ⟨hord, -⟩ j hj
    have hdvd1 : p ∣ 2 ^ nf - 1 := by
      by_contra h
      rw [ggMultOrd, if_neg h] at hord
      split_ifs at hord; omega
    exact ggK1A_uni_primaryMultiplicity_symm hp hK hdvd1 hxpow hsq hζ hj
