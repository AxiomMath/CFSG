module

public import CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofSL2
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofBCent
public import CFSG.RankThree.Chevalley.SteinbergBITrialitySingularIso

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec11.Item1118Res3Proof

open Matrix
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KGD
  CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof Subgroup
open scoped MatrixGroups

section Fixed

variable {L : Type*} [Field L]

theorem sl2Map_injective {E : Type*} [Field E] (φ : E →+* L) :
    Function.Injective (Matrix.SpecialLinearGroup.map φ :
      SpecialLinearGroup (Fin 2) E →* SpecialLinearGroup (Fin 2) L) := by
  intro X Y h
  refine Subtype.ext (Matrix.ext fun i j => φ.injective ?_)
  exact congrArg (fun W : SpecialLinearGroup (Fin 2) L => (W : Matrix (Fin 2) (Fin 2) L) i j) h

theorem exists_sl2_eqLocus (Fr : L →+* L) (Y : SpecialLinearGroup (Fin 2) L)
    (hY : Matrix.SpecialLinearGroup.map Fr Y = Y) :
    ∃ Yk : SpecialLinearGroup (Fin 2) (RingHom.eqLocusField Fr (RingHom.id L)),
      Matrix.SpecialLinearGroup.map (RingHom.eqLocusField Fr (RingHom.id L)).subtype Yk = Y := by
  have hmem : ∀ i j, (Y : Matrix (Fin 2) (Fin 2) L) i j ∈
      RingHom.eqLocusField Fr (RingHom.id L) := by
    intro i j
    rw [RingHom.mem_eqLocusField, RingHom.id_apply]
    exact congrArg (fun W : SpecialLinearGroup (Fin 2) L => (W : Matrix (Fin 2) (Fin 2) L) i j) hY
  let M : Matrix (Fin 2) (Fin 2) (RingHom.eqLocusField Fr (RingHom.id L)) :=
    Matrix.of fun i j => ⟨_, hmem i j⟩
  have hM : (RingHom.eqLocusField Fr (RingHom.id L)).subtype.mapMatrix M = Y := by
    ext i j
    rfl
  have hdet : M.det = 1 := by
    apply (RingHom.eqLocusField Fr (RingHom.id L)).subtype.injective
    rw [RingHom.map_det, hM, map_one]
    exact Y.2
  exact ⟨⟨M, hdet⟩, Subtype.ext hM⟩

theorem map_frob_map_subtype (Fr : L →+* L)
    (A : SpecialLinearGroup (Fin 2) (RingHom.eqLocusField Fr (RingHom.id L))) :
    Matrix.SpecialLinearGroup.map Fr
        (Matrix.SpecialLinearGroup.map (RingHom.eqLocusField Fr (RingHom.id L)).subtype A) =
      Matrix.SpecialLinearGroup.map (RingHom.eqLocusField Fr (RingHom.id L)).subtype A := by
  ext i j
  have h := ((A : Matrix (Fin 2) (Fin 2) (RingHom.eqLocusField Fr (RingHom.id L))) i j).2
  rw [RingHom.mem_eqLocusField, RingHom.id_apply] at h
  exact h

end Fixed

section Conj


variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K}

theorem exists_conj_short (hσ3 : σ ^ 3 = 1) (h3 : (3 : K) ≠ 0)
    {d d' : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hd : d ∈ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom)
    (hd' : d' ∈ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    (hd'3 : d' ^ 3 = 1) (hd'1 : d' ≠ 1) :
    ∃ y ∈ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom, y * d * y⁻¹ = d' := by
  obtain ⟨e⟩ := KS11Lie4Proof.nonempty_mulEquiv_d4ShortSL2 hσ3
  have : Finite (orbitField TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer) := Subtype.finite
  have h3' : (3 : orbitField TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer) ≠ 0 := fun h =>
    h3 (by rw [← map_ofNat (orbitField TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer).subtype 3,
      h, map_zero])
  have hpow : ∀ {z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
      (hz : z ∈ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom), z ^ 3 = 1 →
      (⟨z, hz⟩ : KS11Lie4Proof.d4ShortSL2 K σ.toRingHom) ^ 3 = 1 := fun hz h =>
    Subtype.ext (by rw [Subgroup.coe_pow]; exact h)
  have hne : ∀ {z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
      (hz : z ∈ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom), z ≠ 1 →
      e.symm ⟨z, hz⟩ ≠ 1 := fun hz h h1 =>
    h (congrArg Subtype.val (e.symm.injective (h1.trans (map_one e.symm).symm)))
  obtain ⟨A, hA⟩ := exists_conj_of_pow_three h3'
    (by rw [← map_pow, hpow hd hd3, map_one]) (hne hd hd1)
    (by rw [← map_pow, hpow hd' hd'3, map_one]) (hne hd' hd'1)
  refine ⟨(e A : graphFixedRootGroup TwistTag.D4 K σ.toRingHom), (e A).2, ?_⟩
  have h := congrArg e hA
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h
  exact congrArg Subtype.val h

variable {ℓ f : ℕ} [hℓ : Fact ℓ.Prime]

theorem exists_conj_centS (hf : 1 ≤ f) (hℓ3 : ℓ ≠ 3) (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {c c' : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hc : c ∈ centralizer ((KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
      Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (hc' : c' ∈ centralizer ((KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
      Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) (hc'3 : c' ^ 3 = 1) (hc'1 : c' ≠ 1) :
    ∃ x ∈ centralizer ((KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
      Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)), x * c * x⁻¹ = c' := by
  have hℓp : ℓ.Prime := Fact.out
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓp (k := f * 3) (by omega)
    (by rw [hK, pow_mul])
  set L := AlgebraicClosure K with hL
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hcomm : ∀ c, algebraMap K L (σ c) = Fr (algebraMap K L c) := fun c => by
    rw [hσ, hFr, map_pow]
  have hfixθ := twistHom_thetaConj σ Fr (RingHom.ext hcomm)
  have h3L : (3 : L) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : L) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff L ℓ] at h'
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓp Nat.prime_three).1 h')
  have hZ : ∀ {z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom},
      z ∈ centralizer ((KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
        Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
          Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) → z ^ 3 = 1 → z ≠ 1 →
      ∃ Z : SpecialLinearGroup (Fin 2) L, thetaHom L Z = triEmb K σ L z ∧
        Matrix.SpecialLinearGroup.map Fr Z = Z ∧ Z ^ 3 = 1 ∧ Z ≠ 1 := by
    intro z hz hz3 hz1
    obtain ⟨Z, hZ⟩ := exists_thetaHom_of_mem_centralizer hf hℓ3 hK hσ L hFr hz
    refine ⟨Z, hZ, thetaHom_injective ?_, thetaHom_injective ?_, fun h => hz1 ?_⟩
    · rw [← twistHom_thetaHom Fr hfixθ, hZ]
      exact triEmb_fixed Fr (RingHom.ext hcomm) z
    · rw [map_pow, hZ, ← map_pow, hz3, map_one, map_one]
    · exact triEmb_injective (L := L) (by rw [← hZ, h, map_one, map_one])
  obtain ⟨Z, hZc, hFZ, hZ3, hZ1⟩ := hZ hc hc3 hc1
  obtain ⟨Z', hZc', hFZ', hZ'3, hZ'1⟩ := hZ hc' hc'3 hc'1
  set k := RingHom.eqLocusField Fr (RingHom.id L) with hk
  have hkcard : Nat.card k = ℓ ^ f := natCard_eqLocusField_frob hℓp hf hFr
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hkcard]; exact pow_ne_zero _ hℓp.ne_zero)
  have h3k : (3 : k) ≠ 0 := fun h => h3L (by rw [← map_ofNat k.subtype 3, h, map_zero])
  obtain ⟨Zk, hZk⟩ := exists_sl2_eqLocus Fr Z hFZ
  obtain ⟨Zk', hZk'⟩ := exists_sl2_eqLocus Fr Z' hFZ'
  have hk3 : ∀ {X : SpecialLinearGroup (Fin 2) k} {Y : SpecialLinearGroup (Fin 2) L},
      Matrix.SpecialLinearGroup.map k.subtype X = Y → Y ^ 3 = 1 → X ^ 3 = 1 := fun hX hY =>
    sl2Map_injective k.subtype (by rw [map_pow, hX, hY, map_one])
  have hk1 : ∀ {X : SpecialLinearGroup (Fin 2) k} {Y : SpecialLinearGroup (Fin 2) L},
      Matrix.SpecialLinearGroup.map k.subtype X = Y → Y ≠ 1 → X ≠ 1 := fun hX hY h =>
    hY (by rw [← hX, h, map_one])
  obtain ⟨A, hA⟩ := exists_conj_of_pow_three h3k (hk3 hZk hZ3) (hk1 hZk hZ1) (hk3 hZk' hZ'3)
    (hk1 hZk' hZ'1)
  set AL := Matrix.SpecialLinearGroup.map k.subtype A with hAL
  have hmem : thetaHom L AL ∈ (triEmb K σ L).range := by
    rw [triEmb_range hℓp hf hK hσ Fr hFr]
    refine Subgroup.mem_inf.2 ⟨thetaHom_mem_adjointGroup AL, ?_⟩
    change twistHom TwistTag.D4 L Fr (thetaHom L AL) = MonoidHom.id _ (thetaHom L AL)
    rw [twistHom_thetaHom Fr hfixθ, hAL, map_frob_map_subtype]
    rfl
  obtain ⟨x, hx⟩ := hmem
  refine ⟨x, mem_centralizer_of_triEmb_mem (L := L) (by rw [hx]; exact thetaHom_mem_thetaPair AL),
    triEmb_injective (L := L) ?_⟩
  rw [map_mul, map_mul, map_inv, hx, ← hZc, ← hZc', ← map_inv, ← map_mul, ← map_mul, ← hZk,
    ← hZk', hAL, ← map_inv, ← map_mul, ← map_mul, hA]

theorem exists_inv_short (hσ3 : σ ^ 3 = 1) (h3 : (3 : K) ≠ 0)
    {c d : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hc : c ∈ centralizer ((KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
      Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (hd : d ∈ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) :
    ∃ a : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      a * d * a⁻¹ = d⁻¹ ∧ a * c * a⁻¹ = c := by
  obtain ⟨a, haS, ha⟩ := exists_conj_short hσ3 h3 hd (inv_mem hd) hd3 hd1
    (by rw [inv_pow, hd3, inv_one]) (inv_ne_one.mpr hd1)
  refine ⟨a, ha, ?_⟩
  rw [mem_centralizer_iff.mp hc a haS, mul_inv_cancel_right]

theorem exists_inv_centS (hf : 1 ≤ f) (hℓ3 : ℓ ≠ 3) (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {c d : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hc : c ∈ centralizer ((KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
      Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hd : d ∈ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom) :
    ∃ b : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      b * d * b⁻¹ = d ∧ b * c * b⁻¹ = c⁻¹ := by
  obtain ⟨b, hbS, hb⟩ := exists_conj_centS hf hℓ3 hK hσ hc (inv_mem hc) hc3 hc1
    (by rw [inv_pow, hc3, inv_one]) (inv_ne_one.mpr hc1)
  refine ⟨b, ?_, hb⟩
  rw [← mem_centralizer_iff.mp hbS d hd, mul_inv_cancel_right]

end Conj

end CFSG.RankThree.PartTwo.Sec11.Item1118Res3Proof
