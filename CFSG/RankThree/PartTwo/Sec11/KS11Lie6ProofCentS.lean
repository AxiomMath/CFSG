module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofRigid
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofNine

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof

open Matrix
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KE CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof
  Subgroup
open scoped MatrixGroups


section Conj

variable {K : Type} [Field K] {σ : K ≃+* K} {L : Type} [Field L] [Algebra K L] {Fr : L →+* L}

abbrev outerEmb (K : Type) [Field K] (σ : K ≃+* K) (L : Type) [Field L] [Algebra K L] :
    orbitField TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer →+* L :=
  (algebraMap K L).comp (orbitField TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer).subtype

abbrev frobTriple (Fr : L →+* L) (P : SL2 L) : SL2 L × SL2 L × SL2 L :=
  (P, Matrix.SpecialLinearGroup.map Fr P,
    Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map Fr P))

theorem triEmb_orbitRankOneHom_frob (hcomm : ∀ c, algebraMap K L (σ c) = Fr (algebraMap K L c))
    (B : SL2 (orbitField TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer)) :
    baseChangeGL (algebraMap K L)
        (orbitRankOneHom TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer B) =
      outerTriple L (frobTriple Fr (Matrix.SpecialLinearGroup.map (outerEmb K σ L) B)) := by
  rw [triEmb_orbitRankOneHom_outer]
  have r0 : (algebraMap K L).comp ((σ.toRingHom ^ 0).comp
      (orbitField TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer).subtype) = outerEmb K σ L :=
    RingHom.ext fun c => rfl
  have r1 : (algebraMap K L).comp ((σ.toRingHom ^ 1).comp
      (orbitField TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer).subtype) =
        Fr.comp (outerEmb K σ L) :=
    RingHom.ext fun c => by
      show algebraMap K L (σ (c : K)) = Fr (algebraMap K L (c : K))
      exact hcomm _
  have r2 : (algebraMap K L).comp ((σ.toRingHom ^ 2).comp
      (orbitField TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer).subtype) =
        Fr.comp (Fr.comp (outerEmb K σ L)) :=
    RingHom.ext fun c => by
      show algebraMap K L (σ (σ (c : K))) = Fr (Fr (algebraMap K L (c : K)))
      rw [hcomm, hcomm]
  rw [r0, r1, r2]
  rfl

theorem triEmb_short_eq_conj (hcomm : ∀ c, algebraMap K L (σ c) = Fr (algebraMap K L c))
    {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    {B : SL2 (orbitField TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer)}
    {z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hB : orbitRankOneHom TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer B =
      (z : ModGL TwistTag.D4.tag K)) {P : SL2 L} {μ : Lˣ}
    (hP : Matrix.SpecialLinearGroup.map (outerEmb K σ L) B = P * HSL μ * P⁻¹) :
    triEmb K σ L z = outerTriple L (frobTriple Fr P) *
      rootDiagUnit TwistTag.D4.tag (fun j => μ ^ shortExp (q : ℤ) j) *
        (outerTriple L (frobTriple Fr P))⁻¹ := by
  rw [triEmb_apply, ← hB, triEmb_orbitRankOneHom_frob hcomm, hP]
  have e1 : Units.map Fr.toMonoidHom μ = μ ^ q := Units.ext (by simp [hFr])
  have e2 : Units.map Fr.toMonoidHom (μ ^ q) = μ ^ (q ^ 2) :=
    Units.ext (by simp [hFr, ← pow_mul, sq])
  have htri : frobTriple Fr (P * HSL μ * P⁻¹) =
      frobTriple Fr P * (HSL μ, HSL (μ ^ q), HSL (μ ^ (q ^ 2))) * (frobTriple Fr P)⁻¹ := by
    simp only [frobTriple, map_mul, map_inv, map_HSL, e1, e2, Prod.mk_mul_mk, Prod.inv_mk]
  rw [htri, map_mul, map_mul, map_inv, outerTriple_HSL_short]

theorem exists_triEmb_eq_outerTriple {z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hz : z ∈ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom) :
    ∃ X : SL2 L × SL2 L × SL2 L, triEmb K σ L z = outerTriple L X := by
  obtain ⟨B, hB⟩ := hz
  have hB' : orbitRankOneHom TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer B =
      (z : ModGL TwistTag.D4.tag K) := hB
  exact ⟨_, (congrArg (baseChangeGL (algebraMap K L)) hB').symm.trans
    (triEmb_orbitRankOneHom_outer σ B)⟩

theorem mem_centralizer_of_triEmb_mem {x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hx : triEmb K σ L x ∈ thetaPair L) :
    x ∈ centralizer ((KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
      Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
  rw [mem_centralizer_iff]
  intro s hs
  obtain ⟨X, hX⟩ := exists_triEmb_eq_outerTriple (L := L) hs
  apply triEmb_injective (L := L)
  rw [map_mul, map_mul, hX]
  exact commute_outerTriple_of_mem_thetaPair X hx

end Conj

section Nine

theorem exists_units_orderOf_nine (L : Type) [Field L] [IsAlgClosed L] (h3 : (3 : L) ≠ 0) :
    ∃ μ : Lˣ, orderOf μ = 9 := by
  have h9 : ((9 : ℕ) : L) ≠ 0 := by
    have : ((9 : ℕ) : L) = 3 * 3 := by norm_num
    rw [this]
    exact mul_ne_zero h3 h3
  have : NeZero ((9 : ℕ) : L) := ⟨h9⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 9
  refine ⟨(hζ.isUnit (by norm_num)).unit, ?_⟩
  have h : IsPrimitiveRoot ((hζ.isUnit (by norm_num)).unit : L) 9 := by
    rw [IsUnit.unit_spec]
    exact hζ
  exact (IsPrimitiveRoot.coe_units_iff.1 h).eq_orderOf.symm

theorem cube_mod_nine {q : ℕ} (hq : ¬ 3 ∣ q) : q ^ 3 % 9 = 1 ∨ q ^ 3 % 9 = 8 := by
  have h : ∀ r < 9, r % 3 ≠ 0 → r ^ 3 % 9 = 1 ∨ r ^ 3 % 9 = 8 := by decide
  rw [Nat.pow_mod]
  exact h _ (Nat.mod_lt _ (by norm_num)) (by omega)

@[expose] def companionSL2 {F : Type} [Field F] (t : F) : SL2 F :=
  ⟨!![0, -1; 1, t], by simp [Matrix.det_fin_two]⟩

theorem companionSL2_eq_conj {L : Type} [Field L] {μ : Lˣ} (hμ : (μ : L) ^ 2 ≠ 1) :
    ∃ P : SL2 L, companionSL2 ((μ : L) + ((μ⁻¹ : Lˣ) : L)) = P * HSL μ * P⁻¹ := by
  have hm0 : (μ : L) ≠ 0 := Units.ne_zero μ
  have hinv : ((μ⁻¹ : Lˣ) : L) = (μ : L)⁻¹ := Units.val_inv_eq_inv_val μ
  have hδ : (μ : L) - (μ : L)⁻¹ ≠ 0 := by
    intro h
    apply hμ
    have : (μ : L) * ((μ : L) - (μ : L)⁻¹) = 0 := by rw [h, mul_zero]
    rw [mul_sub, mul_inv_cancel₀ hm0] at this
    linear_combination this
  let P : SL2 L := ⟨!![((μ : L) - (μ : L)⁻¹)⁻¹, 1; -(μ : L) * ((μ : L) - (μ : L)⁻¹)⁻¹,
    -(μ : L)⁻¹], by
    rw [Matrix.det_fin_two_of]
    field_simp
    ring⟩
  refine ⟨P, eq_mul_inv_of_mul_eq (Subtype.ext ?_)⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [companionSL2, P, coe_HSL, hinv, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] {σ : K ≃+* K}

theorem exists_short_nine (hf : 1 ≤ f) (hℓ3 : ℓ ≠ 3) (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (L : Type) [Field L] [Algebra K L] [IsAlgClosed L]
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) :
    ∃ (z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (P : SL2 L) (μ : Lˣ),
      z ∈ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom ∧ orderOf μ = 9 ∧
      triEmb K σ L z = outerTriple L (frobTriple Fr P) *
        rootDiagUnit TwistTag.D4.tag (fun j => μ ^ shortExp ((ℓ ^ f : ℕ) : ℤ) j) *
          (outerTriple L (frobTriple Fr P))⁻¹ := by
  have hℓ : ℓ.Prime := Fact.out
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ (k := f * 3) (by omega)
    (by rw [hK, pow_mul])
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have hσ3 : σ ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    have := ringEquiv_cube_apply_eq hK hσ c
    simpa [pow_succ] using this
  have hcomm : ∀ c, algebraMap K L (σ c) = Fr (algebraMap K L c) := fun c => by
    rw [hσ, hFr, map_pow]
  have h3L : (3 : L) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : L) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff L ℓ] at h'
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 h')
  have hq3 : ¬ 3 ∣ ℓ ^ f := fun h => hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
    (Nat.prime_three.dvd_of_dvd_pow h)).symm
  obtain ⟨μ, hμ⟩ := exists_units_orderOf_nine L h3L
  set tL : L := (μ : L) + ((μ⁻¹ : Lˣ) : L) with htL
  have hpow : ∀ n : ℕ, n % 9 = 1 ∨ n % 9 = 8 → μ ^ n = μ ∨ μ ^ n = μ⁻¹ := by
    intro n hn
    rw [← pow_mod_orderOf, hμ]
    rcases hn with h | h
    · left
      rw [h, pow_one]
    · right
      rw [h]
      have h9 : μ ^ 9 = 1 := by rw [← hμ]; exact pow_orderOf_eq_one μ
      rw [eq_inv_iff_mul_eq_one, ← pow_succ, h9]
  have htK : tL ^ Nat.card K = tL := by
    rw [hK, ← pow_mul, show f * 3 = 3 * f by ring, htL,
      add_pow_char_pow (μ : L) ((μ⁻¹ : Lˣ) : L) ℓ (3 * f)]
    have hn : (ℓ ^ (3 * f)) % 9 = 1 ∨ (ℓ ^ (3 * f)) % 9 = 8 := by
      have e : ℓ ^ (3 * f) = (ℓ ^ f) ^ 3 := by rw [← pow_mul, mul_comm]
      rw [e]
      exact cube_mod_nine hq3
    rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, inv_pow]
    rcases hpow _ hn with h | h
    · rw [h]
    · rw [h, inv_inv, add_comm]
  obtain ⟨t, ht⟩ := mem_range_algebraMap_of_pow_card_eq (k := K) htK
  set t' : orbitField TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer :=
    ⟨t, mem_orbitField_outer hσ3 t⟩ with ht'
  set C := companionSL2 t' with hC
  refine ⟨⟨orbitRankOneHom TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer C,
    range_orbitRankOneHom_le (t := TwistTag.D4) (K := K) (σ := σ.toRingHom)
      KS11Lie4Proof.d4Outer ⟨_, rfl⟩⟩, ?_⟩
  have hμ2 : (μ : L) ^ 2 ≠ 1 := by
    intro h
    have h2 : μ ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])
    have := orderOf_le_of_pow_eq_one (by norm_num) h2
    omega
  obtain ⟨P, hP⟩ := companionSL2_eq_conj hμ2
  refine ⟨P, μ, ⟨C, rfl⟩, hμ, triEmb_short_eq_conj hcomm hFr rfl ?_⟩
  rw [← hP]
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  change outerEmb K σ L ((C : Matrix (Fin 2) (Fin 2) _) i j) =
    (companionSL2 tL : Matrix (Fin 2) (Fin 2) L) i j
  fin_cases i <;> fin_cases j
  · exact map_zero _
  · change outerEmb K σ L (-1) = -1
    rw [map_neg, map_one]
  · exact map_one _
  · exact ht

end Nine

section Rigid

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] {σ : K ≃+* K}

theorem torusGroup_le_normalizer_thetaPair (L : Type) [Field L] :
    torusGroup TwistTag.D4.tag L ≤ normalizer (thetaPair L : Set (ModGL TwistTag.D4.tag L)) := by
  have hθ : IsRoot TwistTag.D4.tag thetaVec := by
    rw [← wordVec_theta, ← KS11Lie5Proof.wordProd_smul]
    exact IsRoot.smul (isRoot_single _ n2) _
  have h := CFSG.RankThree.PartOne.KE.torusGroup_le_normalizer_rootSpan (τ := TwistTag.D4.tag)
    (L := L)
    (S := {thetaVec, -thetaVec}) (by
      rintro α (rfl | rfl)
      · exact hθ
      · exact IsRoot.neg hθ)
  rwa [rootSpan, iSup_insert, iSup_singleton] at h

theorem triEmb_orbitRankOneHom_one {L : Type} [Field L] [Algebra K L]
    (x : SL2 (orbitField TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer))
    (hx : ∀ φ : orbitField TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer →+* L,
      Matrix.SpecialLinearGroup.map φ x = Matrix.SpecialLinearGroup.map (outerEmb K σ L) x) :
    baseChangeGL (algebraMap K L)
        (orbitRankOneHom TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer x) =
      outerTriple L (Matrix.SpecialLinearGroup.map (outerEmb K σ L) x,
        Matrix.SpecialLinearGroup.map (outerEmb K σ L) x,
        Matrix.SpecialLinearGroup.map (outerEmb K σ L) x) := by
  rw [triEmb_orbitRankOneHom_outer, hx, hx ((algebraMap K L).comp ((σ.toRingHom ^ 1).comp _)),
    hx ((algebraMap K L).comp ((σ.toRingHom ^ 2).comp _))]

theorem triEmb_mem_thetaPair_of_mem_centralizer (hf : 1 ≤ f) (hℓ3 : ℓ ≠ 3)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (L : Type) [Field L]
    [Algebra K L] [IsAlgClosed L] {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hx : x ∈ centralizer ((KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
      Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) :
    triEmb K σ L x ∈ thetaPair L := by
  have hℓ : ℓ.Prime := Fact.out
  have hq3 : ¬ 3 ∣ ℓ ^ f := fun h => hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
    (Nat.prime_three.dvd_of_dvd_pow h)).symm
  obtain ⟨y, P, μ, hyS, hμ, hy⟩ := exists_short_nine hf hℓ3 hK hσ L hFr
  set X := outerTriple L (frobTriple Fr P) with hX
  set d := rootDiagUnit TwistTag.D4.tag (fun j => μ ^ shortExp ((ℓ ^ f : ℕ) : ℤ) j) with hd
  rw [mem_centralizer_iff] at hx
  have hxy : triEmb K σ L x * triEmb K σ L y = triEmb K σ L y * triEmb K σ L x := by
    rw [← map_mul, ← map_mul, hx y hyS]
  have hmem : X⁻¹ * triEmb K σ L x * X ∈
      toralCentralizer TwistTag.D4.tag L (fun j => μ ^ shortExp ((ℓ ^ f : ℕ) : ℤ) j) := by
    rw [mem_toralCentralizer]
    refine ⟨mul_mem (mul_mem (inv_mem (outerTriple_mem_adjointGroup _))
      (triEmb_mem_adjointGroup x)) (outerTriple_mem_adjointGroup _), ?_⟩
    have h1 : d = X⁻¹ * triEmb K σ L y * X := by rw [hy]; group
    rw [← hd, h1]
    calc X⁻¹ * triEmb K σ L y * X * (X⁻¹ * triEmb K σ L x * X) *
          (X⁻¹ * triEmb K σ L y * X)⁻¹ =
        X⁻¹ * (triEmb K σ L y * triEmb K σ L x) * (triEmb K σ L y)⁻¹ * X := by group
      _ = X⁻¹ * triEmb K σ L x * X := by rw [← hxy]; group
  have hHQ := toralCentralizer_short_le (q := ℓ ^ f) hq3 (by rw [hμ]) hmem
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _
    (torusGroup_le_normalizer_thetaPair L)] at hHQ
  obtain ⟨h, hh, r, hr, hhr'⟩ := hHQ
  have hhr : h * r = X⁻¹ * triEmb K σ L x * X := hhr'
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  have hXr : X * r = r * X := commute_outerTriple_of_mem_thetaPair _ hr
  have hιx : triEmb K σ L x = X * rootDiagUnit TwistTag.D4.tag b * X⁻¹ * r := by
    have h1 : triEmb K σ L x = X * (rootDiagUnit TwistTag.D4.tag b * r) * X⁻¹ := by
      rw [hhr]; group
    have hrX : r * X⁻¹ = X⁻¹ * r := by
      rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, hXr, mul_inv_cancel_right]
    rw [h1]
    calc X * (rootDiagUnit TwistTag.D4.tag b * r) * X⁻¹ =
        X * rootDiagUnit TwistTag.D4.tag b * (r * X⁻¹) := by group
      _ = X * rootDiagUnit TwistTag.D4.tag b * (X⁻¹ * r) := by rw [hrX]
      _ = _ := by group
  have hcomm2 : ∀ w : SL2 (orbitField TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer),
      (∀ φ : orbitField TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer →+* L,
        Matrix.SpecialLinearGroup.map φ w = Matrix.SpecialLinearGroup.map (outerEmb K σ L) w) →
      rootDiagUnit TwistTag.D4.tag b * outerTriple L ((frobTriple Fr P)⁻¹ *
          (Matrix.SpecialLinearGroup.map (outerEmb K σ L) w,
            Matrix.SpecialLinearGroup.map (outerEmb K σ L) w,
            Matrix.SpecialLinearGroup.map (outerEmb K σ L) w) * frobTriple Fr P) =
        outerTriple L ((frobTriple Fr P)⁻¹ *
          (Matrix.SpecialLinearGroup.map (outerEmb K σ L) w,
            Matrix.SpecialLinearGroup.map (outerEmb K σ L) w,
            Matrix.SpecialLinearGroup.map (outerEmb K σ L) w) * frobTriple Fr P) *
          rootDiagUnit TwistTag.D4.tag b := by
    intro w hw
    set W : SL2 L × SL2 L × SL2 L := (Matrix.SpecialLinearGroup.map (outerEmb K σ L) w,
      Matrix.SpecialLinearGroup.map (outerEmb K σ L) w,
      Matrix.SpecialLinearGroup.map (outerEmb K σ L) w) with hW
    have hwS : (⟨orbitRankOneHom TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer w,
        range_orbitRankOneHom_le (t := TwistTag.D4) (K := K) (σ := σ.toRingHom)
          KS11Lie4Proof.d4Outer ⟨_, rfl⟩⟩ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ∈
        KS11Lie4Proof.d4ShortSL2 K σ.toRingHom := ⟨w, rfl⟩
    have hιw : triEmb K σ L ⟨orbitRankOneHom TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer w,
        range_orbitRankOneHom_le (t := TwistTag.D4) (K := K) (σ := σ.toRingHom)
          KS11Lie4Proof.d4Outer ⟨_, rfl⟩⟩ = outerTriple L W :=
      triEmb_orbitRankOneHom_one w hw
    have h1 := hx _ hwS
    have h2 : triEmb K σ L x * outerTriple L W = outerTriple L W * triEmb K σ L x := by
      rw [← hιw, ← map_mul, ← map_mul, h1]
    have hrW : r * outerTriple L W = outerTriple L W * r :=
      (commute_outerTriple_of_mem_thetaPair W hr).symm
    rw [hιx] at h2
    have h3 : X * rootDiagUnit TwistTag.D4.tag b * X⁻¹ * outerTriple L W =
        outerTriple L W * (X * rootDiagUnit TwistTag.D4.tag b * X⁻¹) := by
      have h4 : X * rootDiagUnit TwistTag.D4.tag b * X⁻¹ * (r * outerTriple L W) =
          outerTriple L W * (X * rootDiagUnit TwistTag.D4.tag b * X⁻¹) * r := by
        rw [← mul_assoc, h2]; group
      rw [hrW] at h4
      have h5 := congrArg (· * r⁻¹) h4
      simpa [mul_assoc] using h5
    rw [map_mul, map_mul, map_inv, ← hX]
    calc rootDiagUnit TwistTag.D4.tag b * (X⁻¹ * outerTriple L W * X) =
        X⁻¹ * (X * rootDiagUnit TwistTag.D4.tag b * X⁻¹ * outerTriple L W) * X := by group
      _ = X⁻¹ * (outerTriple L W * (X * rootDiagUnit TwistTag.D4.tag b * X⁻¹)) * X := by
        rw [h3]
      _ = X⁻¹ * outerTriple L W * X * rootDiagUnit TwistTag.D4.tag b := by group
  have hu := hcomm2 (uSL 1) fun φ => by rw [map_uSL, map_uSL, map_one, map_one]
  have hv := hcomm2 (vSL 1) fun φ => by rw [map_vSL, map_vSL, map_one, map_one]
  rw [map_uSL, map_one] at hu
  rw [map_vSL, map_one] at hv
  have hb := eq_mulSingle_of_commute (frobTriple Fr P) hu hv
  have hdb : rootDiagUnit TwistTag.D4.tag b ∈ thetaPair L := by
    rw [hb]
    exact rootDiagUnit_mulSingle_mem_thetaPair _
  have hXd : X * rootDiagUnit TwistTag.D4.tag b * X⁻¹ = rootDiagUnit TwistTag.D4.tag b := by
    rw [commute_outerTriple_of_mem_thetaPair _ hdb, mul_inv_cancel_right]
  rw [hιx, hXd]
  exact mul_mem hdb hr

end Rigid

end CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
