module

public import CFSG.RankThree.PartOne.KC.EvenUnitaryFiveMatrixActor

public section

namespace CFSG.RankThree.PartOne.KCEvenUnitaryFive

open Polynomial Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCPrimary

section Cyclic

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem isCyclic_of_irreducible_minpoly {E : Module.End K V} (hirr : Irreducible (minpoly K E))
    (hdeg : (minpoly K E).natDegree = Module.finrank K V) {G : Type*} [Group G] [Finite G]
    (ρ : G →* Module.End K V) (hinj : Function.Injective ρ) (hcomm : ∀ g, Commute (ρ g) E) :
    IsCyclic G := by
  classical
  set p := minpoly K E with hp
  have hmonic : p.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral E)
  have hsq : Squarefree p := hirr.squarefree
  have hmem : p ∈ primaryFactors E := mem_primaryFactors.mpr ⟨hirr, hmonic, dvd_rfl⟩
  have hsingle : ∀ a ∈ primaryFactors E, a = p := fun a ha => by
    obtain ⟨hai, ham, hadvd⟩ := mem_primaryFactors.mp ha
    exact eq_of_monic_of_associated ham hmonic (hai.associated_of_dvd hirr hadvd)
  have : Fact (Irreducible p) := ⟨hirr⟩
  have hdim : Module.finrank K V = p.natDegree * primaryMultiplicity E p := by
    rw [finrank_eq_sum_degree_mul_multiplicity hsq]
    have : Unique (primaryFactors E) :=
      ⟨⟨⟨p, hmem⟩⟩, fun a => Subtype.ext (hsingle a a.2)⟩
    rw [Fintype.sum_unique]
    have hd : (((default : primaryFactors E)) : K[X]) = p :=
      hsingle _ (default : primaryFactors E).2
    rw [hd]
  have hm : Module.finrank (AdjoinRoot p) (primaryComponent E p) = 1 := by
    have hpos : 0 < p.natDegree := Irreducible.natDegree_pos hirr
    have h1 : p.natDegree * primaryMultiplicity E p = p.natDegree * 1 := by
      rw [← hdim, ← hdeg, mul_one]
    exact Nat.eq_of_mul_eq_mul_left hpos h1
  have hbij : Function.Bijective (algebraMap (AdjoinRoot p)
      (Module.End (AdjoinRoot p) (primaryComponent E p))) := by
    refine ⟨fun a b hab => ?_, fun u => ?_⟩
    · obtain ⟨c, -, hc⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hm
        (algebraMap (AdjoinRoot p) (Module.End (AdjoinRoot p) (primaryComponent E p)) a)
      have h1 := hc a (by
        show algebraMap _ _ a = a • LinearMap.id
        rw [Module.algebraMap_end_eq_smul_id])
      have h2 := hc b (by
        show algebraMap _ _ a = b • LinearMap.id
        rw [hab, Module.algebraMap_end_eq_smul_id])
      rw [h1, h2]
    · obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hm u
      exact ⟨c, by rw [Module.algebraMap_end_eq_smul_id, hc]⟩
  let ι : G →* commutant E :=
    { toFun := fun g => ⟨ρ g, (mem_commutant E).mpr (hcomm g)⟩
      map_one' := Subtype.ext (map_one ρ)
      map_mul' := fun g g' => Subtype.ext (map_mul ρ g g') }
  let e := RingEquiv.ofBijective _ hbij
  let f₀ : G →* AdjoinRoot p :=
    (e.symm : Module.End (AdjoinRoot p) (primaryComponent E p) ≃+* AdjoinRoot p).toMonoidHom.comp
      ((commutantRestrictHom (x := E) p).toMonoidHom.comp ι)
  refine isCyclic_of_injective_ringHom f₀ fun g g' hgg' => ?_
  have h1 : commutantRestrictHom (x := E) p (ι g) = commutantRestrictHom (x := E) p (ι g') := by
    have := e.symm.injective hgg'
    exact this
  apply hinj
  have h2 : ((ρ g : Module.End K V) : V →ₗ[K] V) = (ρ g' : V →ₗ[K] V) := by
    refine ext_primaryComponent hsq (fun a ha v hv => ?_)
    have ha' := hsingle a ha
    have hv' : v ∈ primaryComponent E p := ha' ▸ hv
    have := congrArg (fun r : Module.End (AdjoinRoot p) (primaryComponent E p) =>
      ((r ⟨v, hv'⟩ : primaryComponent E p) : V)) h1
    exact this
  exact h2

end Cyclic

section Eigen

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem toLinU_pow_eq_smul {x : primeFormUnitary h (idGram K 5)} {c : Kˣ}
    (hc : ((x ^ 5 : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) =
      GeneralLinearGroup.scalar (Fin 5) c) :
    ((toLinU h 5 x : LinearMap.GeneralLinearGroup K (Fin 5 → K)) :
      Module.End K (Fin 5 → K)) ^ 5 = (c : K) • (1 : Module.End K (Fin 5 → K)) := by
  have h2 : ((toLinU h 5 x : LinearMap.GeneralLinearGroup K (Fin 5 → K)) :
      Module.End K (Fin 5 → K)) ^ 5 = ((toLinU h 5 (x ^ 5) :
        LinearMap.GeneralLinearGroup K (Fin 5 → K)) : Module.End K (Fin 5 → K)) := by
    rw [map_pow, Units.val_pow_eq_pow_val]
  rw [h2]
  change Matrix.toLin' (((x ^ 5 : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) :
    Matrix (Fin 5) (Fin 5) K) = _
  rw [hc, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  ext v i
  simp [Matrix.toLin'_apply, Matrix.mulVec_diagonal]

theorem aeval_toLinU_eq_zero {x : primeFormUnitary h (idGram K 5)} {c : Kˣ}
    (hc : ((x ^ 5 : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) =
      GeneralLinearGroup.scalar (Fin 5) c) :
    aeval ((toLinU h 5 x : LinearMap.GeneralLinearGroup K (Fin 5 → K)) :
      Module.End K (Fin 5 → K)) (X ^ 5 - C (c : K)) = 0 := by
  simp [toLinU_pow_eq_smul h hc, Algebra.algebraMap_eq_smul_one]

theorem eigenvalue_pow_five {x : primeFormUnitary h (idGram K 5)} {c : Kˣ}
    (hc : ((x ^ 5 : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) =
      GeneralLinearGroup.scalar (Fin 5) c) {μ : K} {v : Fin 5 → K} (hv : v ≠ 0)
    (hμ : ((toLinU h 5 x : LinearMap.GeneralLinearGroup K (Fin 5 → K)) :
      Module.End K (Fin 5 → K)) v = μ • v) : μ ^ 5 = c := by
  have hev : Module.End.HasEigenvector ((toLinU h 5 x : LinearMap.GeneralLinearGroup K
      (Fin 5 → K)) : Module.End K (Fin 5 → K)) μ v :=
    ⟨Module.End.mem_eigenspace_iff.mpr hμ, hv⟩
  have h1 := Module.End.aeval_apply_of_hasEigenvector (p := X ^ 5 - C (c : K)) hev
  rw [aeval_toLinU_eq_zero h hc] at h1
  simp only [LinearMap.zero_apply, eval_sub, eval_pow, eval_X, eval_C] at h1
  have h2 := (smul_eq_zero.mp h1.symm).resolve_right hv
  exact sub_eq_zero.mp h2

theorem bar_mul_eq_one_of_pow_five (h5 : 5 ∣ 2 ^ f + 1) {μ : K} {c : Kˣ}
    (hc : c ^ (2 ^ f + 1) = 1) (hμ : μ ^ 5 = c) : h.bar μ * μ = 1 := by
  have hfin := h.finite
  have := Fintype.ofFinite K
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    simp at hμ
    exact c.ne_zero hμ.symm
  set w := μ ^ (2 ^ f + 1) with hw
  have hw5 : w ^ 5 = 1 := by
    rw [hw, ← pow_mul, mul_comm, pow_mul, hμ]
    have := congrArg Units.val hc
    simpa using this
  have hcardK : Fintype.card K = (2 ^ f) ^ 2 := by
    have := h.card_eq_sq
    rw [← Nat.card_eq_fintype_card]
    exact this
  have hwq : w ^ (2 ^ f) = w := by
    have h1 : μ ^ ((2 ^ f) ^ 2) = μ := by
      rw [← hcardK]
      exact FiniteField.pow_card μ
    calc w ^ (2 ^ f) = μ ^ (2 ^ f * 2 ^ f) * μ ^ (2 ^ f) := by
          rw [hw, ← pow_mul, add_mul, one_mul, pow_add]
      _ = w := by
          rw [← sq, h1, hw, pow_succ, mul_comm]
  have hw0 : w ≠ 0 := pow_ne_zero _ hμ0
  have hwq1 : w ^ (2 ^ f - 1) = 1 := by
    have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have : w ^ (2 ^ f) = w * w ^ (2 ^ f - 1) := by
      rw [← pow_succ' w (2 ^ f - 1), Nat.sub_add_cancel hq1]
    rw [this] at hwq
    exact (mul_eq_left₀ hw0).mp hwq
  have hcop : Nat.gcd 5 (2 ^ f - 1) = 1 := by
    have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have hnd : ¬ 5 ∣ 2 ^ f - 1 := by
      intro hd
      have h2 : 5 ∣ (2 ^ f + 1) - (2 ^ f - 1) := Nat.dvd_sub h5 hd
      omega
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr hnd
  have hw1 : w = 1 := by
    have := (pow_gcd_eq_one (a := w) (m := 5) (n := 2 ^ f - 1)).mpr ⟨hw5, hwq1⟩
    rwa [hcop, pow_one] at this
  change μ ^ (2 ^ f) * μ = 1
  rw [← pow_succ]
  exact hw1

theorem bar_mul_eq_one_of_eigenvalue (h5 : 5 ∣ 2 ^ f + 1) {x : primeFormUnitary h (idGram K 5)}
    (hx : x ^ 5 ∈ idScalarKernel h 5) {μ : K} {v : Fin 5 → K} (hv : v ≠ 0)
    (hμ : ((toLinU h 5 x : LinearMap.GeneralLinearGroup K (Fin 5 → K)) :
      Module.End K (Fin 5 → K)) v = μ • v) : h.bar μ * μ = 1 := by
  obtain ⟨c, hcq, hc⟩ := hx
  exact bar_mul_eq_one_of_pow_five h h5 hcq (eigenvalue_pow_five h hc hv hμ)

include h in
theorem exists_isPrimitiveRoot_five (h5 : 5 ∣ 2 ^ f + 1) : ∃ ζ : K, IsPrimitiveRoot ζ 5 := by
  have hfin := h.finite
  have hdvd : 5 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, h.card]
    have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have h2 : 2 ^ (2 * f) = 2 ^ f * 2 ^ f := by rw [two_mul, pow_add]
    have h3 : 2 ^ f * 2 ^ f - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
      have := Nat.mul_self_sub_mul_self_eq (2 ^ f) 1
      simpa using this
    rw [h2, h3]
    exact Dvd.dvd.mul_right h5 _
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 5 hdvd
  have hzp : IsPrimitiveRoot z 5 := by
    have := IsPrimitiveRoot.orderOf z
    rwa [hz] at this
  exact ⟨(z : K), IsPrimitiveRoot.coe_units_iff.mpr hzp⟩

include h in
theorem five_ne_zero : ((5 : ℕ) : K) ≠ 0 := by
  have hcharK : CharP K 2 := h.charP
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h1 : ((5 : ℕ) : K) = 1 := by
    calc ((5 : ℕ) : K) = 1 + 2 * 2 := by norm_num
      _ = 1 := by rw [h2]; ring
  rw [h1]
  exact one_ne_zero

end Eigen

section Group

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem exists_fifth_root (G : Subgroup (primeFormUnitary h (idGram K 5)))
    (hGcomm : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x) (hGnc : ¬ IsCyclic G)
    {x : primeFormUnitary h (idGram K 5)} (hx : x ∈ G) {c : Kˣ}
    (hc : ((x ^ 5 : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) =
      GeneralLinearGroup.scalar (Fin 5) c) : ∃ b : K, b ^ 5 = c := by
  by_contra hb
  push Not at hb
  have hfin := h.finite
  have hirr : Irreducible (X ^ 5 - C (c : K)) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_five hb
  have hmin : minpoly K ((toLinU h 5 x : LinearMap.GeneralLinearGroup K (Fin 5 → K)) :
      Module.End K (Fin 5 → K)) = X ^ 5 - C (c : K) :=
    (minpoly.eq_of_irreducible_of_monic hirr (aeval_toLinU_eq_zero h hc)
      (monic_X_pow_sub_C _ (by norm_num))).symm
  apply hGnc
  let ρ : G →* Module.End K (Fin 5 → K) :=
    (Units.coeHom (Module.End K (Fin 5 → K))).comp ((toLinU h 5).comp G.subtype)
  refine isCyclic_of_irreducible_minpoly (E := ((toLinU h 5 x :
      LinearMap.GeneralLinearGroup K (Fin 5 → K)) : Module.End K (Fin 5 → K)))
    (hmin ▸ hirr) (by rw [hmin, natDegree_X_pow_sub_C, Module.finrank_fin_fun]) ρ
    (fun g g' hgg' => Subtype.ext (toLinU_injective (Units.ext hgg'))) fun g => ?_
  have h1 : Commute (toLinU h 5 (g : primeFormUnitary h (idGram K 5))) (toLinU h 5 x) := by
    have := congrArg (toLinU h 5) (hGcomm g g.2 x hx)
    rw [map_mul, map_mul] at this
    exact this
  exact h1.units_val

theorem iSup_eigenspace_eq_top (h5 : 5 ∣ 2 ^ f + 1) (G : Subgroup (primeFormUnitary h (idGram K 5)))
    (hGcomm : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x) (hGnc : ¬ IsCyclic G)
    (hGpow : ∀ x ∈ G, x ^ 5 ∈ idScalarKernel h 5) {x : primeFormUnitary h (idGram K 5)}
    (hx : x ∈ G) :
    ⨆ μ : K, Module.End.eigenspace ((toLinU h 5 x : LinearMap.GeneralLinearGroup K (Fin 5 → K)) :
      Module.End K (Fin 5 → K)) μ = ⊤ := by
  classical
  obtain ⟨c, hcq, hc⟩ := hGpow x hx
  obtain ⟨b, hb⟩ := exists_fifth_root h G hGcomm hGnc hx hc
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_five h h5
  have hsplit : (X ^ 5 - C (c : K)).Splits := X_pow_sub_C_splits_of_isPrimitiveRoot hζ hb
  have hsq := squarefree_minpoly_toLinU_of_pow_scalar (h := h) (m := 5) (five_ne_zero h)
    (hGpow x hx)
  set E := ((toLinU h 5 x : LinearMap.GeneralLinearGroup K (Fin 5 → K)) :
    Module.End K (Fin 5 → K)) with hE
  have hdvdp : minpoly K E ∣ X ^ 5 - C (c : K) := minpoly.dvd K E (aeval_toLinU_eq_zero h hc)
  have hp0 : (X ^ 5 - C (c : K)) ≠ 0 := X_pow_sub_C_ne_zero (by norm_num) _
  have hlin : ∀ a ∈ primaryFactors E, a.natDegree = 1 := fun a ha => by
    obtain ⟨hai, -, hadvd⟩ := mem_primaryFactors.mp ha
    exact (hsplit.of_dvd hp0 (hadvd.trans hdvdp)).natDegree_eq_one_of_irreducible hai
  have hcomp : ∀ a ∈ primaryFactors E,
      primaryComponent E a ≤ Module.End.eigenspace E (-(a.coeff 0)) := by
    intro a ha v hv
    have hform : a = X + C (a.coeff 0) := (monic_of_mem_primaryFactors ha).eq_X_add_C (hlin a ha)
    rw [mem_primaryComponent, hform] at hv
    have h1 : E v + (a.coeff 0) • v = 0 := by
      simpa [aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] using hv
    rw [Module.End.mem_eigenspace_iff, neg_smul]
    exact eq_neg_of_add_eq_zero_left h1
  rw [eq_top_iff]
  intro v _
  have hv := LinearMap.congr_fun (sum_primaryProjection hsq) v
  rw [LinearMap.sum_apply] at hv
  have hv' : v = ∑ a ∈ primaryFactors E, primaryProjection E a v := by simpa using hv.symm
  rw [hv']
  exact Submodule.sum_mem _ fun a ha => Submodule.mem_iSup_of_mem (-(a.coeff 0))
    (hcomp a ha (primaryProjection_mem hsq ha v))

end Group

end CFSG.RankThree.PartOne.KCEvenUnitaryFive
