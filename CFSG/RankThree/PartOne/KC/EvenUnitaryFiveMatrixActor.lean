module

public import CFSG.RankThree.PartOne.KC.UnitaryLiftBlocks

public section

namespace CFSG.RankThree.PartOne

open Polynomial Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitaryRegular CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitaryLift
open scoped commutatorElement

namespace KCEvenUnitaryFive

section Scalar

variable {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem odd_two_pow_succ {f : ℕ} (h5 : 5 ∣ 2 ^ f + 1) : Odd (2 ^ f + 1) := by
  have hf : f ≠ 0 := by
    rintro rfl
    norm_num at h5
  exact (Nat.even_pow.mpr ⟨even_two, hf⟩).add_one

theorem scalarKernel_pow_eq_one {d : primeFormUnitary h (idGram K n)}
    (hd : d ∈ idScalarKernel h n) : d ^ (2 ^ f + 1) = 1 := by
  obtain ⟨c, hc, hdc⟩ := hd
  apply Subtype.ext
  rw [Subgroup.coe_pow, hdc, ← map_pow, hc, map_one]
  rfl

theorem exists_involution_lift (hn : 3 ≤ n) (hq : 3 < 2 ^ f) (hodd : Odd (2 ^ f + 1))
    {g : primeFormUnitary h (idGram K n)} (hg : primeFormConjHom h (idGram K n) (g ^ 2) = 1) :
    ∃ g' : primeFormUnitary h (idGram K n),
      primeFormConjHom h (idGram K n) g' = primeFormConjHom h (idGram K n) g ∧ g' ^ 2 = 1 := by
  obtain ⟨k, hk⟩ := hodd
  have hd : g ^ 2 ∈ idScalarKernel h n := (primeFormConjHom_eq_one_iff hn hq _).mp hg
  have hdk : (g ^ 2) ^ (2 * k + 1) = 1 := by
    rw [← hk]
    exact scalarKernel_pow_eq_one h hd
  set e := (g ^ 2) ^ (k + 1) with he
  have he1 : primeFormConjHom h (idGram K n) e = 1 := by
    rw [he, map_pow, hg, one_pow]
  have hec : Commute e g := commute_of_mem_ker hn hq he1 g
  have he2 : e ^ 2 = g ^ 2 := by
    rw [he, ← pow_mul, show (k + 1) * 2 = (2 * k + 1) + 1 by ring, pow_succ, hdk, one_mul]
  refine ⟨g * e⁻¹, ?_, ?_⟩
  · rw [map_mul, map_inv, he1, inv_one, mul_one]
  · have hec' : Commute g e⁻¹ := hec.symm.inv_right
    rw [hec'.mul_pow, inv_pow, he2, mul_inv_cancel]

theorem commute_of_involution_lift (hn : 3 ≤ n) (hq : 3 < 2 ^ f) (hodd : Odd (2 ^ f + 1))
    {u g : primeFormUnitary h (idGram K n)} (hg2 : g ^ 2 = 1)
    (hcomm : primeFormConjHom h (idGram K n) g * primeFormConjHom h (idGram K n) u =
      primeFormConjHom h (idGram K n) u * primeFormConjHom h (idGram K n) g) :
    g * u = u * g := by
  obtain ⟨k, hk⟩ := hodd
  set w := (u * g)⁻¹ * (g * u) with hw
  have hw1 : primeFormConjHom h (idGram K n) w = 1 := by
    rw [hw, map_mul, map_inv, map_mul, map_mul, hcomm, inv_mul_cancel]
  have hwc : ∀ x, Commute w x := commute_of_mem_ker hn hq hw1
  have hgu : g * u = u * g * w := by
    rw [hw]
    group
  have hgg : g * g = 1 := by rw [← sq, hg2]
  have h1 : g * (g * u) = u * (g * g) * (w * w) := by
    calc g * (g * u) = g * (u * g * w) := by rw [hgu]
      _ = (g * u) * g * w := by group
      _ = (u * g * w) * g * w := by rw [hgu]
      _ = u * g * (w * g) * w := by group
      _ = u * g * (g * w) * w := by rw [(hwc g).eq]
      _ = u * (g * g) * (w * w) := by group
  have h2 : g * (g * u) = u := by rw [← mul_assoc, hgg, one_mul]
  rw [h2, hgg, mul_one] at h1
  have h3 : w * w = 1 := by
    have : u * 1 = u * (w * w) := by rw [mul_one]; exact h1
    exact (mul_left_cancel this).symm
  have hw0 : w ∈ idScalarKernel h n := (primeFormConjHom_eq_one_iff hn hq w).mp hw1
  have hwk : w ^ (2 * k + 1) = 1 := by
    rw [← hk]
    exact scalarKernel_pow_eq_one h hw0
  have hw' : w = 1 := by
    have : w ^ (2 * k + 1) = w := by
      rw [pow_succ, pow_mul, sq, h3, one_pow, one_mul]
    rw [← this]
    exact hwk
  rw [hgu, hw', mul_one]

end Scalar

section Primary

variable {f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem squarefree_minpoly_toLinU_of_pow_scalar {u : primeFormUnitary h (idGram K n)} {m : ℕ}
    (hm : (m : K) ≠ 0) (hu : u ^ m ∈ idScalarKernel h n) :
    Squarefree (minpoly K ((toLinU h n u : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K))) := by
  obtain ⟨c, -, hc⟩ := hu
  have hsep : (Polynomial.X ^ m - Polynomial.C (c : K)).Separable :=
    Polynomial.separable_X_pow_sub_C (c : K) hm c.ne_zero
  refine squarefree_minpoly_of_aeval_eq_zero hsep.squarefree ?_
  have h1 : ((toLinU h n u : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) ^ m = (c : K) • (1 : Module.End K (Fin n → K)) := by
    have h2 : ((toLinU h n u : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) ^ m = ((toLinU h n (u ^ m) :
          LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) := by
      rw [map_pow, Units.val_pow_eq_pow_val]
    rw [h2]
    change Matrix.toLin' (((u ^ m : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = _
    rw [hc, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    ext v i
    simp [Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  simp [h1, Algebra.algebraMap_eq_smul_one]

variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem eq_one_of_center_mul_self_eq_one [CharP K 2] {x : Module.End K V}
    (hsq : Squarefree (minpoly K x)) {Y : Module.End K V} (hY : Y ∈ commutant x)
    (hc : (⟨Y, hY⟩ : commutant x) ∈ Subalgebra.center K (commutant x)) (hY2 : Y * Y = 1) :
    Y = 1 := by
  have hscal := (mem_center_commutant_iff hsq ⟨Y, hY⟩).mp hc
  have hid : ∀ a : primaryFactors x, ∀ v : primaryComponent x (a : K[X]), Y (v : V) = v := by
    intro a v
    have : Fact (Irreducible (a : K[X])) := ⟨irreducible_of_mem_primaryFactors a.2⟩
    obtain ⟨c, hc'⟩ := hscal a
    have h1 : Y (v : V) = ((c • v : primaryComponent x (a : K[X])) : V) := hc' v
    have h2 : Y (Y (v : V)) = (((c * c) • v : primaryComponent x (a : K[X])) : V) := by
      rw [h1, hc' (c • v), smul_smul]
    have h3 : ((c * c) • v : primaryComponent x (a : K[X])) = v := by
      apply Subtype.ext
      rw [← h2]
      exact (LinearMap.congr_fun hY2 (v : V)).symm ▸ rfl
    have h2E : (2 : AdjoinRoot (a : K[X])) = 0 := by
      calc (2 : AdjoinRoot (a : K[X])) = algebraMap K (AdjoinRoot (a : K[X])) 2 :=
            (map_ofNat _ 2).symm
        _ = 0 := by rw [CharTwo.two_eq_zero, map_zero]
    have h4 : (c - 1) • ((c - 1) • v) = 0 := by
      rw [smul_smul]
      have : (c - 1) * (c - 1) = c * c - 1 := by linear_combination (1 - c) * h2E
      rw [this, sub_smul, h3, one_smul, sub_self]
    have h5 : (c - 1) • v = 0 := by
      rcases smul_eq_zero.mp h4 with h6 | h6
      · rw [h6, zero_smul]
      · exact h6
    have h6 : c • v = v := by
      rw [sub_smul, one_smul, sub_eq_zero] at h5
      exact h5
    rw [h1, h6]
  refine LinearMap.ext fun v => ?_
  have hsum := LinearMap.congr_fun (sum_primaryProjection hsq) v
  rw [LinearMap.sum_apply] at hsum
  calc Y v = Y (∑ a ∈ primaryFactors x, primaryProjection x a v) := by rw [hsum]; rfl
    _ = ∑ a ∈ primaryFactors x, primaryProjection x a v := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun a ha =>
          hid ⟨a, ha⟩ ⟨_, primaryProjection_mem hsq ha v⟩
    _ = (1 : Module.End K V) v := hsum

end Primary

section Main

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem conj_mem_inSubgroup_core_of_mem {G : Type*} [Group G] (q : ℕ) (C : Subgroup G) {g s : G}
    (hg : g ∈ C)
    (hs : s ∈ CFSG.inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore q) C) :
    g * s * g⁻¹ ∈ CFSG.inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore q) C := by
  obtain ⟨s', hs', rfl⟩ := hs
  refine ⟨⟨g, hg⟩ * s' * ⟨g, hg⟩⁻¹, ?_, by simp⟩
  exact (inferInstance : (CFSG.RankThree.LocalRank.aschbacherSolvableCore q C).Normal).conj_mem
    s' hs' ⟨g, hg⟩

theorem eq_one_of_sq_eq_one_mem_core_inf_D (h5 : 5 ∣ 2 ^ f + 1)
    (B : Subgroup (MulAut (primeFormP h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))))
    (hB : (MulAut.conj : primeFormP h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) →*
      MulAut (primeFormP h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))).range ≤ B)
    {t : MulAut (primeFormP h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))}
    (ht5 : orderOf t = 5) (htD : t ∈ primeFormD h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))
    {z : MulAut (primeFormP h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))}
    (hz : z ∈ CFSG.inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore 5)
      (B ⊓ Subgroup.centralizer ({t} : Set _)) ⊓
        primeFormD h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))
    (hz2 : z ^ 2 = 1) : z = 1 := by
  classical
  have hfinK : Finite K := h.finite
  have hcharK : CharP K 2 := h.charP
  have hn : 3 ≤ 5 := by norm_num
  have hq4 : 4 ≤ 2 ^ f := by
    have := Nat.le_of_dvd (by positivity) h5
    omega
  have hq3 : 3 < 2 ^ f := by omega
  have hodd := odd_two_pow_succ h5
  obtain ⟨u, rfl⟩ := htD
  obtain ⟨g, hg⟩ := hz.2
  have hzS := hz.1
  have hzCB : z ∈ B ⊓ Subgroup.centralizer ({primeFormConjHom h (idGram K 5) u} :
      Set (MulAut (primeFormP h (idGram K 5)))) := Subgroup.map_subtype_le _ hzS
  have hg2 : primeFormConjHom h (idGram K 5) (g ^ 2) = 1 := by rw [map_pow, hg, hz2]
  obtain ⟨g', hg'ρ, hg'2⟩ := exists_involution_lift h hn hq3 hodd hg2
  have hcomm : primeFormConjHom h (idGram K 5) g' * primeFormConjHom h (idGram K 5) u =
      primeFormConjHom h (idGram K 5) u * primeFormConjHom h (idGram K 5) g' := by
    rw [hg'ρ, hg]
    exact Subgroup.mem_centralizer_singleton_iff.mp hzCB.2
  have hg'u : g' * u = u * g' := commute_of_involution_lift h hn hq3 hodd hg'2 hcomm
  have ht5' : primeFormConjHom h (idGram K 5) (u ^ 5) = 1 := by
    rw [map_pow]
    have := pow_orderOf_eq_one (primeFormConjHom h (idGram K 5) u)
    rwa [ht5] at this
  have hu5 : u ^ 5 ∈ idScalarKernel h 5 := (primeFormConjHom_eq_one_iff hn hq3 _).mp ht5'
  have h5K : ((5 : ℕ) : K) ≠ 0 := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have : ((5 : ℕ) : K) = 1 := by
      calc ((5 : ℕ) : K) = 1 + 2 * 2 := by norm_num
        _ = 1 := by rw [h2]; ring
    rw [this]
    exact one_ne_zero
  have hsq := squarefree_minpoly_toLinU_of_pow_scalar h5K hu5
  have H : UnitaryPrimaryData h.bar (idForm h 5) (toLinU h 5 u) :=
    ⟨h.bar_bar, idForm_isSymm h 5, idForm_separatingLeft h 5, toLinU_mem u, hsq⟩
  have hg'c : g' ∈ Subgroup.centralizer ({u} : Set (primeFormUnitary h (idGram K 5))) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hg'u
  have hY : toLinU h 5 g' ∈ unitaryCentralizer (idForm h 5) (toLinU h 5 u) := by
    rw [centralizer_eq_comap] at hg'c
    exact hg'c
  have hcommSB : ∀ a : primaryFactors ((toLinU h 5 u : LinearMap.GeneralLinearGroup K (Fin 5 → K)) :
      Module.End K (Fin 5 → K)),
      2 ≤ primaryMultiplicity ((toLinU h 5 u : LinearMap.GeneralLinearGroup K (Fin 5 → K)) :
        Module.End K (Fin 5 → K)) (a : K[X]) →
      ∀ y ∈ specialBlock (idForm h 5) (toLinU h 5 u) (a : K[X]), Commute (toLinU h 5 g') y := by
    intro a ha y hy
    obtain ⟨y', rfl⟩ := specialBlock_le_range_toLinU u _ hy
    have hQ := isQuasisimple_comap_specialBlock hq4 H a ha
    have hall := commutator_eq_one_of_central
      (F := (specialBlock (idForm h 5) (toLinU h 5 u) (a : K[X])).comap (toLinU h 5))
      (Z := (primeFormConjHom h (idGram K 5)).ker) g' hQ.1
      (fun z' hz' x => commute_of_mem_ker hn hq3 (MonoidHom.mem_ker.mp hz') x)
      (fun y1 hy1 => by
        have hc1 := commute_core_specialBlock hn hq4 H B hB Nat.prime_five hzS a ha hy1
        rw [MonoidHom.mem_ker, map_commutatorElement, hg'ρ, hg]
        exact commutatorElement_eq_one_iff_commute.mpr hc1.symm) y' hy
    exact (commutatorElement_eq_one_iff_commute.mp hall).map (toLinU h 5)
  obtain ⟨-, hz', hcenter⟩ := mem_center_of_commute_specialBlocks H hq4 hY hcommSB
  have hY2 : ((toLinU h 5 g' : LinearMap.GeneralLinearGroup K (Fin 5 → K)) :
      Module.End K (Fin 5 → K)) * ((toLinU h 5 g' : LinearMap.GeneralLinearGroup K
        (Fin 5 → K)) : Module.End K (Fin 5 → K)) = 1 := by
    have h1 := congrArg (toLinU h 5) hg'2
    rw [map_pow, map_one, sq] at h1
    have h2 := congrArg (fun x : LinearMap.GeneralLinearGroup K (Fin 5 → K) =>
      (x : Module.End K (Fin 5 → K))) h1
    simpa using h2
  have hone := eq_one_of_center_mul_self_eq_one hsq hz' hcenter hY2
  have hg'1 : g' = 1 := toLinU_injective (Units.ext (by simpa using hone))
  rw [← hg, ← hg'ρ, hg'1, map_one]

end Main

end KCEvenUnitaryFive

theorem even_unitary_five_matrix_actor_local_core_linear_part_odd {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1)
    (B : Subgroup (MulAut (primeFormP h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))))
    (hB : (MulAut.conj : primeFormP h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) →*
      MulAut (primeFormP h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))).range ≤ B)
    {t : MulAut (primeFormP h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))} (_htB : t ∈ B)
    (htD : t ∈ primeFormD h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))
    (ht5 : orderOf t = 5) :
    ¬ 2 ∣ Nat.card ↥(CFSG.inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore 5)
        (B ⊓ Subgroup.centralizer ({t} : Set (MulAut (primeFormP h
          ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))))) ⊓
      primeFormD h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) ∧
    ∀ A : Subgroup (MulAut (primeFormP h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))),
      A ≤ B ⊓ Subgroup.centralizer ({t} : Set (MulAut (primeFormP h
        ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)))) →
      ¬ 2 ∣ Nat.card ↥⁅CFSG.inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore 5)
        (B ⊓ Subgroup.centralizer ({t} : Set (MulAut (primeFormP h
          ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))))), A⁆ := by
  classical
  have hfinK : Finite K := h.finite
  have hfin : Finite (primeFormP h (idGram K 5)) := finite_primeFormP
  have hn : 3 ≤ 5 := by norm_num
  have hq3 : 3 < 2 ^ f := by
    have := Nat.le_of_dvd (by positivity) h5
    omega
  have hpart1 : ¬ 2 ∣ Nat.card ↥(CFSG.inSubgroup
      (CFSG.RankThree.LocalRank.aschbacherSolvableCore 5)
        (B ⊓ Subgroup.centralizer ({t} : Set (MulAut (primeFormP h (idGram K 5))))) ⊓
      primeFormD h (idGram K 5)) := by
    intro h2
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hx2' : x ^ 2 = 1 := by
      have := pow_orderOf_eq_one x
      rwa [hx] at this
    have hx2 : (x : MulAut (primeFormP h (idGram K 5))) ^ 2 = 1 := by
      have := congrArg Subtype.val hx2'
      simpa using this
    have hx1 : x = 1 :=
      Subtype.ext (KCEvenUnitaryFive.eq_one_of_sq_eq_one_mem_core_inf_D h h5 B hB ht5 htD x.2 hx2)
    rw [hx1, orderOf_one] at hx
    omega
  refine ⟨hpart1, fun A hA h2 => hpart1 ?_⟩
  set S := CFSG.inSubgroup (CFSG.RankThree.LocalRank.aschbacherSolvableCore 5)
    (B ⊓ Subgroup.centralizer ({t} : Set (MulAut (primeFormP h (idGram K 5))))) with hS
  have hle : ⁅S, A⁆ ≤ S ⊓ primeFormD h (idGram K 5) := by
    refine Subgroup.commutator_le.mpr fun s hs a ha => ?_
    have haCB : a ∈ B ⊓ Subgroup.centralizer ({t} : Set (MulAut (primeFormP h (idGram K 5)))) :=
      hA ha
    refine ⟨?_, commutator_mem_primeFormD hn hq3 s a⟩
    have h1 := KCEvenUnitaryFive.conj_mem_inSubgroup_core_of_mem 5 _ haCB (inv_mem hs)
    have h3 : ⁅s, a⁆ = s * (a * s⁻¹ * a⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [h3]
    exact mul_mem hs h1
  exact h2.trans (Subgroup.card_dvd_of_le hle)

end CFSG.RankThree.PartOne
