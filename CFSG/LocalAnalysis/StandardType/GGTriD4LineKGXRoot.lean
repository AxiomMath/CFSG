module

public import CFSG.LocalAnalysis.StandardType.GGTriD4LineKGXDefs
public import CFSG.LieType.Chevalley.TwistedE6NormalFormActors
public import CFSG.RankThree.PartOne.KGD.D4Frame
public import CFSG.LieType.Ree.LargeReeSylowOpposition
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.A1Levi
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A1TwistedE6
public import CFSG.RankThree.PartOne.KE.SigmaPerX
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.Defs

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KGD

open scoped Pointwise

private def z0Tuple {L : Type} [Field L] (A : Lˣ) : Fin Tag.D4.rank → Lˣ := ![A, A, 1, A]

private lemma z0Tuple_zero {L : Type} [Field L] (A : Lˣ) :
    z0Tuple A (0 : Fin Tag.D4.rank) = A := rfl

private lemma z0Tuple_pow_three {L : Type} [Field L] (A : Lˣ) (hA3 : A ^ 3 = 1) :
    (z0Tuple A) ^ 3 = 1 := by
  funext i
  fin_cases i
  · change A ^ 3 = 1; exact hA3
  · change A ^ 3 = 1; exact hA3
  · change (1 : Lˣ) ^ 3 = 1; simp
  · change A ^ 3 = 1; exact hA3

private lemma z0Tuple_ne_one {L : Type} [Field L] (A : Lˣ) (hA1 : A ≠ 1) :
    z0Tuple A ≠ 1 := by
  intro h
  exact hA1 (by rw [← z0Tuple_zero A]; exact congrFun h 0)

private lemma orderOf_rootDiagUnit_of_pow_three {L : Type} [Field L]
    (b : Fin Tag.D4.rank → Lˣ) (h3 : b ^ 3 = 1) (h1 : b ≠ 1) :
    orderOf (rootDiagUnit Tag.D4 b) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [rootDiagUnit_pow, h3, rootDiagUnit_one]
  · intro h
    exact h1 (rootDiagUnit_injective (τ := Tag.D4) (K := L) (by rw [h, rootDiagUnit_one]))

private lemma rootChar_z0Tuple_apply {L : Type} [Field L] (A : Lˣ)
    (v : Fin Tag.D4.rank → ℤ) :
    rootChar (τ := Tag.D4) (K := L) (z0Tuple A) v = A ^ (v 0 + v 1 + v 3) := by
  change (∏ i, z0Tuple A i ^ v i) = A ^ (v 0 + v 1 + v 3)
  change (∏ i : Fin 4, z0Tuple A i ^ v i) = A ^ (v 0 + v 1 + v 3)
  rw [Fin.prod_univ_four]
  change A ^ v 0 * A ^ v 1 * (1 : Lˣ) ^ v 2 * A ^ v 3 = A ^ (v 0 + v 1 + v 3)
  simp only [one_zpow, mul_one]
  rw [← zpow_add, ← zpow_add]

private lemma rootChar_z0Tuple_eq_one_iff {L : Type} [Field L] (A : Lˣ)
    (hA3 : A ^ 3 = 1) (hA1 : A ≠ 1) (v : Fin Tag.D4.rank → ℤ) :
    rootChar (τ := Tag.D4) (K := L) (z0Tuple A) v = 1 ↔ 3 ∣ (v 0 + v 1 + v 3) := by
  rw [rootChar_z0Tuple_apply]
  have hAord : orderOf A = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact orderOf_eq_prime hA3 hA1
  rw [← orderOf_dvd_iff_zpow_eq_one, hAord]
  norm_num

private lemma ringChar_ne_three_of_cube_root {L : Type} [Field L] (A : Lˣ)
    (hA3 : A ^ 3 = 1) (hA1 : A ≠ 1) : ringChar L ≠ 3 := by
  intro hchar
  haveI : CharP L 3 := hchar ▸ ringChar.charP L
  have hA3' : (A : L) ^ 3 = 1 := by
    have := congrArg Units.val hA3
    simpa using this
  have hzero : ((A : L) - 1) ^ 3 = 0 := by
    rw [show (3 : ℕ) = 3 ^ 1 by norm_num, sub_pow_char_pow]
    simp [hA3']
  have hA1' : (A : L) ≠ 1 := fun h => hA1 (Units.ext h)
  have h0 : (A : L) - 1 = 0 := (pow_eq_zero_iff (by norm_num)).mp hzero
  exact hA1' (sub_eq_zero.mp h0)

private def longVec (a b c d : ℤ) : Fin Tag.D4.rank → ℤ := ![a, b, c, d]

private abbrev d4LongA2Set : Set (Fin Tag.D4.rank → ℤ) :=
  {longVec 0 0 1 0, longVec 1 1 1 1, longVec 1 1 2 1,
    longVec 0 0 (-1) 0, longVec (-1) (-1) (-1) (-1), longVec (-1) (-1) (-2) (-1)}

private lemma longVec_add (a b c d a' b' c' d' : ℤ) :
    longVec a b c d + longVec a' b' c' d' = longVec (a + a') (b + b') (c + c') (d + d') := by
  ext i
  fin_cases i <;> rfl

private lemma longVec_neg (a b c d : ℤ) :
    -longVec a b c d = longVec (-a) (-b) (-c) (-d) := by
  ext i
  fin_cases i <;> rfl

private lemma triD4LineV_image_d4A2Sigma :
    (fun α : Fin Tag.D4.rank → ℤ => triD4LineV • α) '' d4A2Sigma = d4LongA2Set := by
  have h0 : triD4LineV • (Pi.single (0 : Fin Tag.D4.rank) 1) = longVec 0 0 1 0 := by
    rw [triD4LineV, wordProd_smul]
    decide +kernel
  have h2 : triD4LineV • (Pi.single (2 : Fin Tag.D4.rank) 1) = longVec 1 1 1 1 := by
    rw [triD4LineV, wordProd_smul]
    decide +kernel
  apply Set.ext
  intro α
  constructor
  · rintro ⟨β, hβ, rfl⟩
    simp only [d4A2Sigma, Set.mem_insert_iff, Set.mem_singleton_iff] at hβ
    rcases hβ with rfl | rfl | rfl | rfl | rfl | rfl
    · dsimp only; rw [h0]; simp [d4LongA2Set]
    · dsimp only; rw [smul_neg, h0, longVec_neg]; simp [d4LongA2Set]
    · dsimp only; rw [h2]; simp [d4LongA2Set]
    · dsimp only; rw [smul_neg, h2, longVec_neg]; simp [d4LongA2Set]
    · dsimp only; rw [smul_add, h0, h2, longVec_add]
      simp [d4LongA2Set]
    · dsimp only; rw [smul_neg, smul_add, h0, h2,
        longVec_add, longVec_neg]; simp [d4LongA2Set]
  · intro hα
    simp only [d4LongA2Set, Set.mem_insert_iff, Set.mem_singleton_iff] at hα
    rcases hα with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨Pi.single 0 1, by simp [d4A2Sigma], ?_⟩
      dsimp only; rw [h0]
    · refine ⟨Pi.single 2 1, by simp [d4A2Sigma], ?_⟩
      dsimp only; rw [h2]
    · refine ⟨Pi.single 0 1 + Pi.single 2 1, by simp [d4A2Sigma], ?_⟩
      dsimp only; rw [smul_add, h0, h2, longVec_add]
      norm_num
    · refine ⟨-Pi.single 0 1, by simp [d4A2Sigma], ?_⟩
      dsimp only; rw [smul_neg, h0, longVec_neg]
      norm_num
    · refine ⟨-Pi.single 2 1, by simp [d4A2Sigma], ?_⟩
      dsimp only; rw [smul_neg, h2, longVec_neg]
    · refine ⟨-(Pi.single 0 1 + Pi.single 2 1), by simp [d4A2Sigma], ?_⟩
      dsimp only; rw [smul_neg, smul_add, h0, h2,
        longVec_add, longVec_neg]
      norm_num

private lemma d4RootVec_three_dvd_iff :
    ∀ k : Fin 24, (3 ∣ (d4RootVec k 0 + d4RootVec k 1 + d4RootVec k 3)) ↔
      d4RootVec k ∈ d4LongA2Set := by
  decide +kernel

private lemma d4LongA2Set_subset_range : d4LongA2Set ⊆ Set.range d4RootVec := by
  intro α hα
  simp only [d4LongA2Set, Set.mem_insert_iff, Set.mem_singleton_iff] at hα
  rcases hα with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨2, by decide +kernel⟩
  · exact ⟨19, by decide +kernel⟩
  · exact ⟨22, by decide +kernel⟩
  · exact ⟨8, by decide +kernel⟩
  · exact ⟨21, by decide +kernel⟩
  · exact ⟨23, by decide +kernel⟩

private lemma isRoot_and_three_dvd_iff
    (α : Fin Tag.D4.rank → ℤ) :
    IsRoot Tag.D4 α ∧ 3 ∣ (α 0 + α 1 + α 3) ↔ α ∈ d4LongA2Set := by
  constructor
  · rintro ⟨hα, h3⟩
    obtain ⟨k, rfl⟩ := isRoot_iff_exists_d4RootVec.mp hα
    exact (d4RootVec_three_dvd_iff k).mp h3
  · intro hα
    obtain ⟨k, hk⟩ := d4LongA2Set_subset_range hα
    rw [← hk] at hα ⊢
    exact ⟨isRoot_d4RootVec k, (d4RootVec_three_dvd_iff k).mpr hα⟩

private lemma rootCharKernel_z0
    {L : Type} [Field L] (A : Lˣ) (hA3 : A ^ 3 = 1)
    (hA1 : A ≠ 1) :
    rootCharKernel (τ := Tag.D4) (z0Tuple A) =
      (fun α : Fin Tag.D4.rank → ℤ => triD4LineV • α) '' d4A2Sigma := by
  rw [triD4LineV_image_d4A2Sigma]
  apply Set.ext
  intro α
  simp only [rootCharKernel, Set.mem_setOf_eq]
  rw [rootChar_z0Tuple_eq_one_iff A hA3 hA1]
  exact isRoot_and_three_dvd_iff α

theorem triD4Line_toralCentralizer_z0
    (L : Type) [Field L] (A : Lˣ) (hA3 : A ^ 3 = 1) (hA1 : A ≠ 1) :
    orderOf (rootDiagUnit Tag.D4 ![A, A, 1, A]) = 3 ∧
      rootCharKernel (τ := Tag.D4) ![A, A, 1, A] = (fun α => triD4LineV • α) '' d4A2Sigma ∧
      (toralCentralizer Tag.D4 L ![A, A, 1, A] : Set (ModGL Tag.D4 L)) =
        (torusGroup Tag.D4 L : Set (ModGL Tag.D4 L)) * (d4A2Qv L triD4LineV : Set _) ∧
      d4A2Qv L triD4LineV ≤ toralCentralizer Tag.D4 L ![A, A, 1, A] ∧
      d4A2Qv L triD4LineV ⊓ torusGroup Tag.D4 L = d4A2Tv L triD4LineV := by
  change orderOf (rootDiagUnit Tag.D4 (z0Tuple A)) = 3 ∧
    rootCharKernel (τ := Tag.D4) (z0Tuple A) =
      (fun α : Fin Tag.D4.rank → ℤ => triD4LineV • α) '' d4A2Sigma ∧
    (toralCentralizer Tag.D4 L (z0Tuple A) : Set (ModGL Tag.D4 L)) =
      (torusGroup Tag.D4 L : Set (ModGL Tag.D4 L)) * (d4A2Qv L triD4LineV : Set _) ∧
    d4A2Qv L triD4LineV ≤ toralCentralizer Tag.D4 L (z0Tuple A) ∧
    d4A2Qv L triD4LineV ⊓ torusGroup Tag.D4 L = d4A2Tv L triD4LineV
  have hord := orderOf_rootDiagUnit_of_pow_three (z0Tuple A)
    (z0Tuple_pow_three A hA3) (z0Tuple_ne_one A hA1)
  have hsig := rootCharKernel_z0 A hA3 hA1
  have hpK := ringChar_ne_three_of_cube_root A hA3 hA1
  have hlib := D4_odd_prime_A2_root_character_centralizer L 3 Nat.prime_three
    (by norm_num) hpK (z0Tuple A) hord triD4LineV hsig
  obtain ⟨-, h2, h3, -, -, -, -, h8, -⟩ := hlib
  exact ⟨hord, hsig, h2, h3, h8⟩

private lemma sigma_omega_eq {K : Type} [Field K] (σ : K ≃+* K)
    (hσ3 : σ ^ 3 = 1) (ω : K) (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) : σ ω = ω := by
  have h3 : ∀ c : K, σ (σ (σ c)) = c := fun c => by
    rw [← ringEquiv_pow_three_apply, hσ3]; rfl
  have hω_quad : ω ^ 2 + ω + 1 = 0 := by
    have h0 : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by
      calc (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 := by ring
        _ = 0 := by rw [hω3]; ring
    exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hω1)
  set u := σ ω with hu
  have hu3 : u ^ 3 = 1 := by
    rw [hu, ← map_pow, hω3, map_one]
  have hu1 : u ≠ 1 := by
    intro h
    apply hω1
    apply σ.injective
    rw [← hu, h, map_one]
  have hu_quad : u ^ 2 + u + 1 = 0 := by
    have h0 : (u - 1) * (u ^ 2 + u + 1) = 0 := by
      calc (u - 1) * (u ^ 2 + u + 1) = u ^ 3 - 1 := by ring
        _ = 0 := by rw [hu3]; ring
    exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hu1)
  have hprod : (u - ω) * (u - ω ^ 2) = 0 := by
    have h1 : ω + ω ^ 2 = -1 := by linear_combination hω_quad
    have h2 : u + u ^ 2 = -1 := by linear_combination hu_quad
    calc (u - ω) * (u - ω ^ 2) = u ^ 2 - u * (ω + ω ^ 2) + ω ^ 3 := by ring
      _ = u ^ 2 - u * (-1) + 1 := by rw [h1, hω3]
      _ = u ^ 2 + u + 1 := by ring
      _ = 0 := hu_quad
  rcases (mul_eq_zero.mp hprod) with huw | huw
  · rw [hu]; exact sub_eq_zero.mp huw
  · exfalso
    have hσu : σ u = ω := by
      have e : u ^ 2 = ω := by
        rw [sub_eq_zero.mp huw]
        calc (ω ^ 2) ^ 2 = ω ^ 3 * ω := by ring
          _ = ω := by rw [hω3]; ring
      calc σ u = σ (ω ^ 2) := by rw [sub_eq_zero.mp huw]
        _ = (σ ω) ^ 2 := by rw [map_pow]
        _ = u ^ 2 := rfl
        _ = ω := e
    have h3u : σ (σ (σ u)) = u := h3 u
    have hchain : σ (σ (σ u)) = ω := by
      rw [hσu]
      rw [show σ ω = u from hu.symm]
      exact hσu
    have hωeq : ω = ω ^ 2 := by
      rw [hchain] at h3u
      exact h3u.trans (sub_eq_zero.mp huw)
    have hω0 : ω ≠ 0 := by
      intro h
      rw [h, zero_pow (by norm_num)] at hω3
      exact zero_ne_one hω3
    have hpp : ω * (ω - 1) = 0 := by
      rw [mul_sub, mul_one, ← sq, ← hωeq, sub_self]
    exact hω1 (sub_eq_zero.mp ((mul_eq_zero.mp hpp).resolve_left hω0))

theorem triD4Line_trialityOuterTorus_z0
    (K : Type) [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ3 : σ ^ 3 = 1) (ω : Kˣ)
    (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    ∃ hz : trialityOuterTorus K σ ω ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      orderOf (⟨trialityOuterTorus K σ ω, hz⟩ :
          graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = 3 ∧
        fieldActor σ σ ⟨trialityOuterTorus K σ ω, hz⟩ = ⟨trialityOuterTorus K σ ω, hz⟩ ∧
        ∀ (L : Type) [Field L] [Algebra K L],
          triEmb K σ L ⟨trialityOuterTorus K σ ω, hz⟩ =
            rootDiagUnit Tag.D4 ![Units.map (algebraMap K L).toMonoidHom (ω ^ 2),
              Units.map (algebraMap K L).toMonoidHom (ω ^ 2), 1,
              Units.map (algebraMap K L).toMonoidHom (ω ^ 2)] := by
  have h3 : ∀ c : K, σ (σ (σ c)) = c := fun c => by
    rw [← ringEquiv_pow_three_apply, hσ3]; rfl
  have hω3' : (ω : K) ^ 3 = 1 := by
    have := congrArg Units.val hω3
    simpa using this
  have hω1' : (ω : K) ≠ 1 := fun h => hω1 (Units.ext h)
  have hσω : Units.map σ.toRingHom.toMonoidHom ω = ω :=
    Units.ext (sigma_omega_eq σ hσ3 (ω : K) hω3' hω1')
  have hmid : trialityMiddleTorus K σ (1 : (trialityFixedField K σ.toRingHom)ˣ) = 1 := by
    rw [trialityMiddleTorus]
    exact CFSG.Blueprint.Chevalley.torusElt_one ⟨2, by decide⟩
  have hzT : trialityOuterTorus K σ ω ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom := by
    have h := trialityTorusHom_mem_graphFixedTorus (σ := σ) hσ3 (ω, 1)
    rw [trialityTorusHom_apply, hmid, mul_one] at h
    exact h
  have hΓ := (even_triality_fixed_group_eq_root_group K (ringChar.eq K 2) σ h3).1
  have hz : trialityOuterTorus K σ ω ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
    rw [← hΓ]
    exact (Subgroup.mem_inf.1 hzT).2
  have hz_eq : trialityOuterTorus K σ ω =
      rootDiagUnit Tag.D4 (z0Tuple (ω ^ 2)) := by
    rw [trialityOuterTorus_eq_rootDiagUnit]
    change rootDiagUnit Tag.D4 (d4Tuple (ω ^ 2)
      ((Units.map σ.toRingHom.toMonoidHom) ω ^ 2)
      ((ω * (Units.map σ.toRingHom.toMonoidHom) ω *
        (Units.map σ.toRingHom.toMonoidHom) ((Units.map σ.toRingHom.toMonoidHom) ω))⁻¹)
      ((Units.map σ.toRingHom.toMonoidHom) ((Units.map σ.toRingHom.toMonoidHom) ω) ^ 2)) =
      rootDiagUnit Tag.D4 (d4Tuple (ω ^ 2) (ω ^ 2) 1 (ω ^ 2))
    congr 1
    refine vec4_eq ?_ ?_ ?_ ?_
    · rfl
    · simp only [hσω]
    · simp only [hσω]
      have hω3'' : ω * ω * ω = 1 := by
        rw [← pow_two, ← pow_succ, show 2 + 1 = 3 by norm_num, hω3]
      simp only [hω3'', inv_one]
    · simp only [hσω]
  refine ⟨hz, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_mk, hz_eq]
    have hω23 : (ω ^ 2) ^ 3 = 1 := by
      rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hω3, one_pow]
    have hω2ne : (ω ^ 2) ≠ 1 := by
      intro h
      apply hω1
      have h1 : ω ^ 3 = ω := by
        rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, h, one_mul]
      rw [hω3] at h1
      exact h1.symm
    exact orderOf_rootDiagUnit_of_pow_three (z0Tuple (ω ^ 2))
      (z0Tuple_pow_three (ω ^ 2) hω23) (z0Tuple_ne_one (ω ^ 2) hω2ne)
  · apply Subtype.ext
    rw [coe_fieldActor]
    change Units.map (entrywiseHom σ.toRingHom) (trialityOuterTorus K σ ω) =
      trialityOuterTorus K σ ω
    rw [hz_eq]
    change Units.map (entrywiseHom σ.toRingHom)
      (rootDiagUnit TwistTag.D4.tag (d4Tuple (ω ^ 2) (ω ^ 2) 1 (ω ^ 2))) =
      rootDiagUnit TwistTag.D4.tag (d4Tuple (ω ^ 2) (ω ^ 2) 1 (ω ^ 2))
    rw [units_map_entrywiseHom_rootDiagUnit]
    congr 1
    funext i
    fin_cases i
    · change (Units.map σ.toRingHom.toMonoidHom) (ω ^ 2) = ω ^ 2
      rw [map_pow, hσω]
    · change (Units.map σ.toRingHom.toMonoidHom) (ω ^ 2) = ω ^ 2
      rw [map_pow, hσω]
    · change (Units.map σ.toRingHom.toMonoidHom) 1 = 1
      simp
    · change (Units.map σ.toRingHom.toMonoidHom) (ω ^ 2) = ω ^ 2
      rw [map_pow, hσω]
  · intro L _ _
    rw [triEmb_apply]
    change baseChangeGL (algebraMap K L) (trialityOuterTorus K σ ω) =
      rootDiagUnit Tag.D4 ![Units.map (algebraMap K L).toMonoidHom (ω ^ 2),
        Units.map (algebraMap K L).toMonoidHom (ω ^ 2), 1,
        Units.map (algebraMap K L).toMonoidHom (ω ^ 2)]
    rw [hz_eq]
    change baseChangeGL (algebraMap K L)
      (rootDiagUnit TwistTag.D4.tag (d4Tuple (ω ^ 2) (ω ^ 2) 1 (ω ^ 2))) =
      rootDiagUnit TwistTag.D4.tag
        (d4Tuple (Units.map (algebraMap K L).toMonoidHom (ω ^ 2))
          (Units.map (algebraMap K L).toMonoidHom (ω ^ 2)) 1
          (Units.map (algebraMap K L).toMonoidHom (ω ^ 2)))
    rw [baseChangeGL_rootDiagUnit]
    congr 1
    funext i
    fin_cases i
    · change (Units.map (algebraMap K L).toMonoidHom) (ω ^ 2) =
        Units.map (algebraMap K L).toMonoidHom (ω ^ 2)
      rfl
    · change (Units.map (algebraMap K L).toMonoidHom) (ω ^ 2) =
        Units.map (algebraMap K L).toMonoidHom (ω ^ 2)
      rfl
    · change (Units.map (algebraMap K L).toMonoidHom) 1 = 1
      simp
    · change (Units.map (algebraMap K L).toMonoidHom) (ω ^ 2) =
        Units.map (algebraMap K L).toMonoidHom (ω ^ 2)
      rfl

end CFSG.StandardType
