module

public import CFSG.Quasithin.EmptyFaithful.S152T2F4
public import CFSG.Quasithin.EmptyFaithful.S152TG2
public import CFSG.Quasithin.EmptyFaithful.S152SSplit
public import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm
public import CFSG.LieType.Chevalley.EvenTrialityTorusCoordinates
public import CFSG.LieType.Chevalley.GraphFixedSimpleComplement
public import CFSG.LieType.Chevalley.GraphFixedSylowOpposition
public import CFSG.LieType.Chevalley.TorusCentralizer

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.K1 CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
  CFSG.LocalAnalysis.ComponentInitial

section D4Arith

theorem d4_not_dvd_of_abs_lt {m x : ℤ} (hx : x ≠ 0) (h : |x| < m) : ¬ m ∣ x :=
  fun hd => hx (Int.eq_zero_of_abs_lt_dvd hd h)

theorem d4_cast_pow_three_sub_one {q : ℕ} (hq : 1 ≤ q) :
    (((q ^ 3 - 1 : ℕ) : ℤ)) = (q : ℤ) ^ 3 - 1 := by
  have h : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ hq
  rw [Nat.cast_sub h]
  push_cast
  ring

theorem d4_not_dvd_exp₁ {q : ℕ} (hq : 4 ≤ q) : ¬ (((q ^ 3 - 1 : ℕ) : ℤ)) ∣ (1 + q - q ^ 2) := by
  rw [d4_cast_pow_three_sub_one (by omega)]
  have h4 : (4 : ℤ) ≤ q := by exact_mod_cast hq
  exact d4_not_dvd_of_abs_lt (by nlinarith) (abs_lt.2 ⟨by nlinarith, by nlinarith⟩)

theorem d4_not_dvd_exp₂ {q : ℕ} (hq : 4 ≤ q) : ¬ (((q ^ 3 - 1 : ℕ) : ℤ)) ∣ (1 - q + q ^ 2) := by
  rw [d4_cast_pow_three_sub_one (by omega)]
  have h4 : (4 : ℤ) ≤ q := by exact_mod_cast hq
  exact d4_not_dvd_of_abs_lt (by nlinarith) (abs_lt.2 ⟨by nlinarith, by nlinarith⟩)

theorem d4_not_dvd_exp₃ {q : ℕ} (hq : 4 ≤ q) : ¬ (((q ^ 3 - 1 : ℕ) : ℤ)) ∣ (-1 + q + q ^ 2) := by
  rw [d4_cast_pow_three_sub_one (by omega)]
  have h4 : (4 : ℤ) ≤ q := by exact_mod_cast hq
  exact d4_not_dvd_of_abs_lt (by nlinarith) (abs_lt.2 ⟨by nlinarith, by nlinarith⟩)

theorem d4_not_dvd_outer {q : ℕ} (hq : 4 ≤ q) {m₀ m₁ m₃ : ℤ}
    (h : (m₀ = 1 ∧ m₁ = 1 ∧ m₃ = -1) ∨ (m₀ = 1 ∧ m₁ = -1 ∧ m₃ = 1) ∨
      (m₀ = -1 ∧ m₁ = 1 ∧ m₃ = 1)) :
    ¬ (((q ^ 3 - 1 : ℕ) : ℤ)) ∣ (m₀ + q * m₁ + q * q * m₃) := by
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · have := d4_not_dvd_exp₁ hq
    convert this using 2
    ring
  · have := d4_not_dvd_exp₂ hq
    convert this using 2
    ring
  · have := d4_not_dvd_exp₃ hq
    convert this using 2
    ring

theorem d4_not_dvd_norm {q : ℕ} (hq : 4 ≤ q) {m : ℤ} (hm : m = 1 ∨ m = -1 ∨ m = 2) :
    ¬ (((q ^ 3 - 1 : ℕ) : ℤ)) ∣ ((q ^ 2 + q + 1) * m) := by
  rw [d4_cast_pow_three_sub_one (by omega)]
  have h4 : (4 : ℤ) ≤ q := by exact_mod_cast hq
  rcases hm with rfl | rfl | rfl
  · exact d4_not_dvd_of_abs_lt (by nlinarith) (abs_lt.2 ⟨by nlinarith, by nlinarith⟩)
  · exact d4_not_dvd_of_abs_lt (by nlinarith) (abs_lt.2 ⟨by nlinarith, by nlinarith⟩)
  · exact d4_not_dvd_of_abs_lt (by nlinarith) (abs_lt.2 ⟨by nlinarith, by nlinarith⟩)

end D4Arith

section D4Torus


variable {K : Type} [Field K]

@[expose] def d4m (i : Fin TwistTag.D4.tag.rank) (v : Fin TwistTag.D4.tag.rank → ℤ) : ℤ :=
  ∑ k, TwistTag.D4.tag.cartan i k * v k

@[expose] noncomputable def d4Outer (σ : K ≃+* K) (a : Kˣ) : adjointGroup TwistTag.D4.tag K :=
  torusElement TwistTag.D4.tag K ⟨0, by decide⟩ a *
    torusElement TwistTag.D4.tag K ⟨1, by decide⟩ (Units.map σ.toRingHom.toMonoidHom a) *
    torusElement TwistTag.D4.tag K ⟨3, by decide⟩
      (Units.map σ.toRingHom.toMonoidHom (Units.map σ.toRingHom.toMonoidHom a))

@[expose] noncomputable def d4Middle (b : Kˣ) : adjointGroup TwistTag.D4.tag K :=
  torusElement TwistTag.D4.tag K ⟨2, by decide⟩ b

theorem d4Outer_conj (σ : K ≃+* K) (a : Kˣ) (β : Root TwistTag.D4.tag) (c : K) :
    d4Outer σ a * (rootOperatorFamily TwistTag.D4.tag).eltElement β c * (d4Outer σ a)⁻¹ =
      (rootOperatorFamily TwistTag.D4.tag).eltElement β
        (((a ^ d4m ⟨0, by decide⟩ β.1 * Units.map σ.toRingHom.toMonoidHom a ^ d4m ⟨1, by decide⟩ β.1 *
          Units.map σ.toRingHom.toMonoidHom (Units.map σ.toRingHom.toMonoidHom a) ^
            d4m ⟨3, by decide⟩ β.1 : Kˣ) : K) * c) := by
  have e : ∀ (x y z E : adjointGroup TwistTag.D4.tag K),
      x * y * z * E * (x * y * z)⁻¹ = x * (y * (z * E * z⁻¹) * y⁻¹) * x⁻¹ := fun x y z E => by group
  unfold d4Outer
  rw [e, (rootOperatorFamily TwistTag.D4.tag).torusElement_mul_eltElement_mul_inv,
    (rootOperatorFamily TwistTag.D4.tag).torusElement_mul_eltElement_mul_inv,
    (rootOperatorFamily TwistTag.D4.tag).torusElement_mul_eltElement_mul_inv]
  congr 1
  simp only [Units.val_mul, d4m]
  ring

theorem d4Middle_conj (b : Kˣ) (β : Root TwistTag.D4.tag) (c : K) :
    d4Middle b * (rootOperatorFamily TwistTag.D4.tag).eltElement β c * (d4Middle b)⁻¹ =
      (rootOperatorFamily TwistTag.D4.tag).eltElement β
        (((b ^ d4m ⟨2, by decide⟩ β.1 : Kˣ) : K) * c) :=
  (rootOperatorFamily TwistTag.D4.tag).torusElement_mul_eltElement_mul_inv _ b β c

theorem d4Outer_mem_H [Finite K] (σ : K ≃+* K) (a : Kˣ) :
    d4Outer σ a ∈ (nativeData TwistTag.D4.tag K).H :=
  mul_mem (mul_mem (torusElement_mem_H _ _ _) (torusElement_mem_H _ _ _))
    (torusElement_mem_H _ _ _)

theorem d4Middle_mem_H [Finite K] (b : Kˣ) : d4Middle b ∈ (nativeData TwistTag.D4.tag K).H :=
  torusElement_mem_H _ _ _

end D4Torus

section D4Word

@[expose] def d4LongWord : List (Fin TwistTag.D4.tag.rank) :=
  (List.replicate 3 ([0, 1, 3, 2] : List (Fin 4))).flatten

theorem d4_negCheck : negCheck TwistTag.D4.tag d4LongWord = true := by decide +kernel

theorem d4_char_cases : ∀ m < TwistTag.D4.tag.rootCertificate.roots.length,
    0 < height (TwistTag.D4.tag.rootCertificate.root m) →
      (d4m ⟨2, by decide⟩ (TwistTag.D4.tag.rootCertificate.root m) = 1 ∨
       d4m ⟨2, by decide⟩ (TwistTag.D4.tag.rootCertificate.root m) = -1 ∨
       d4m ⟨2, by decide⟩ (TwistTag.D4.tag.rootCertificate.root m) = 2 ∨
       (d4m ⟨2, by decide⟩ (TwistTag.D4.tag.rootCertificate.root m) = 0 ∧
        ((d4m ⟨0, by decide⟩ (TwistTag.D4.tag.rootCertificate.root m) = 1 ∧
          d4m ⟨1, by decide⟩ (TwistTag.D4.tag.rootCertificate.root m) = 1 ∧
          d4m ⟨3, by decide⟩ (TwistTag.D4.tag.rootCertificate.root m) = -1) ∨
         (d4m ⟨0, by decide⟩ (TwistTag.D4.tag.rootCertificate.root m) = 1 ∧
          d4m ⟨1, by decide⟩ (TwistTag.D4.tag.rootCertificate.root m) = -1 ∧
          d4m ⟨3, by decide⟩ (TwistTag.D4.tag.rootCertificate.root m) = 1) ∨
         (d4m ⟨0, by decide⟩ (TwistTag.D4.tag.rootCertificate.root m) = -1 ∧
          d4m ⟨1, by decide⟩ (TwistTag.D4.tag.rootCertificate.root m) = 1 ∧
          d4m ⟨3, by decide⟩ (TwistTag.D4.tag.rootCertificate.root m) = 1)))) := by
  decide +kernel

section Reduced


theorem d4_isReduced : (coxeterSystem TwistTag.D4.tag).IsReduced d4LongWord :=
  isReduced_of_reducedCheck (by decide +kernel)

end Reduced

end D4Word

section D4Char

variable {K : Type} [Field K]

theorem d4_units_map_sigma {q : ℕ} {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ q) (a : Kˣ) :
    Units.map σ.toRingHom.toMonoidHom a = a ^ q :=
  Units.ext (by simp [hσ])

theorem d4_outer_char_eq {q : ℕ} {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ q) (a : Kˣ) (m₀ m₁ m₃ : ℤ) :
    a ^ m₀ * Units.map σ.toRingHom.toMonoidHom a ^ m₁ *
        Units.map σ.toRingHom.toMonoidHom (Units.map σ.toRingHom.toMonoidHom a) ^ m₃ =
      a ^ (m₀ + q * m₁ + q * q * m₃) := by
  simp only [d4_units_map_sigma hσ, ← zpow_natCast, ← zpow_mul, ← zpow_add]

theorem d4_outer_char_ne_one {q : ℕ} (hq : 4 ≤ q) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ q) {a : Kˣ}
    (ha : orderOf a = q ^ 3 - 1) {m₀ m₁ m₃ : ℤ}
    (h : (m₀ = 1 ∧ m₁ = 1 ∧ m₃ = -1) ∨ (m₀ = 1 ∧ m₁ = -1 ∧ m₃ = 1) ∨
      (m₀ = -1 ∧ m₁ = 1 ∧ m₃ = 1)) :
    ((a ^ m₀ * Units.map σ.toRingHom.toMonoidHom a ^ m₁ *
      Units.map σ.toRingHom.toMonoidHom (Units.map σ.toRingHom.toMonoidHom a) ^ m₃ : Kˣ) : K) ≠ 1 := by
  rw [Ne, Units.val_eq_one, d4_outer_char_eq hσ]
  intro h1
  have h2 := orderOf_dvd_iff_zpow_eq_one.2 h1
  rw [ha] at h2
  exact d4_not_dvd_outer hq h h2

theorem d4_middle_char_ne_one {q : ℕ} (hq : 4 ≤ q) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ q) {a : Kˣ}
    (ha : orderOf a = q ^ 3 - 1) {m : ℤ} (hm : m = 1 ∨ m = -1 ∨ m = 2) :
    (((a * Units.map σ.toRingHom.toMonoidHom a *
      Units.map σ.toRingHom.toMonoidHom (Units.map σ.toRingHom.toMonoidHom a)) ^ m : Kˣ) : K) ≠ 1 := by
  have e : a * Units.map σ.toRingHom.toMonoidHom a *
      Units.map σ.toRingHom.toMonoidHom (Units.map σ.toRingHom.toMonoidHom a) =
        a ^ ((1 : ℤ) + q * 1 + q * q * 1) := by
    have := d4_outer_char_eq hσ a 1 1 1
    simpa only [zpow_one] using this
  rw [Ne, Units.val_eq_one, e, ← zpow_mul]
  intro h1
  have h2 := orderOf_dvd_iff_zpow_eq_one.2 h1
  rw [ha] at h2
  refine d4_not_dvd_norm hq hm ?_
  convert h2 using 1
  ring

section Hchar


theorem d4_hchar {q : ℕ} (hq : 4 ≤ q) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ q) {a : Kˣ}
    (ha : orderOf a = q ^ 3 - 1) (β : Root TwistTag.D4.tag) (hβ : 0 < height β.1)
    {y : adjointGroup TwistTag.D4.tag K} (hy : y ∈ (nativeRootSubgroups TwistTag.D4.tag K).X β)
    (hyc : ∀ h ∈ ({d4Outer σ a, d4Middle (a * Units.map σ.toRingHom.toMonoidHom a *
      Units.map σ.toRingHom.toMonoidHom (Units.map σ.toRingHom.toMonoidHom a))} :
        Set (adjointGroup TwistTag.D4.tag K)), h * y * h⁻¹ = y) : y = 1 := by
  have hcases := d4_char_cases (rootPos β) (rootPos_lt β) (by rw [root_rootPos]; exact hβ)
  rw [root_rootPos] at hcases
  have hA : (d4m ⟨2, by decide⟩ β.1 = 1 ∨ d4m ⟨2, by decide⟩ β.1 = -1 ∨
      d4m ⟨2, by decide⟩ β.1 = 2) → y = 1 := fun hm =>
    eq_one_of_conj_eltElement (d4_middle_char_ne_one hq hσ ha hm)
      (fun c => d4Middle_conj _ β c) hy (hyc _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  rcases hcases with h | h | h | ⟨-, htriple⟩
  · exact hA (Or.inl h)
  · exact hA (Or.inr (Or.inl h))
  · exact hA (Or.inr (Or.inr h))
  · exact eq_one_of_conj_eltElement (d4_outer_char_ne_one hq hσ ha htriple)
      (fun c => d4Outer_conj σ a β c) hy (hyc _ (Set.mem_insert _ _))

end Hchar

end D4Char

section D4Fixed

variable {K : Type} [Field K]

variable (σ : K ≃+* K)

theorem coe_d4Outer (a : Kˣ) :
    ((d4Outer σ a : adjointGroup TwistTag.D4.tag K) : ModGL TwistTag.D4.tag K) =
      trialityOuterTorus K σ a := by
  rw [trialityOuterTorus_eq]
  rfl

theorem coe_d4Middle_norm (hσ : σ ^ 3 = 1) (a : Kˣ) :
    ((d4Middle (a * Units.map σ.toRingHom.toMonoidHom a *
        Units.map σ.toRingHom.toMonoidHom (Units.map σ.toRingHom.toMonoidHom a)) :
      adjointGroup TwistTag.D4.tag K) : ModGL TwistTag.D4.tag K) =
      trialityMiddleTorus K σ (trialityNorm σ hσ a) := by
  rw [trialityMiddleTorus, trialityFixedUnit_norm hσ]
  rfl

theorem trialityMiddleTorus_one : trialityMiddleTorus K σ 1 = 1 := by
  rw [trialityMiddleTorus, map_one, torusElt_one]

theorem trialityOuterTorus_one : trialityOuterTorus K σ 1 = 1 := by
  rw [trialityOuterTorus_eq, map_one, map_one, torusElt_one, torusElt_one, torusElt_one]
  group

variable {σ}

theorem commute_of_mem_graphFixedTorus {τ : K →+* K}
    (hΓC : twistedFixedGroup TwistTag.D4 K τ ≤ graphFixedRootGroup TwistTag.D4 K τ)
    {T : ModGL TwistTag.D4.tag K} (hT : T ∈ graphFixedTorus TwistTag.D4 K τ)
    {u : graphFixedRootGroup TwistTag.D4 K τ}
    (hc : ∀ h : graphFixedRootGroup TwistTag.D4 K τ,
      h ∈ Subgroup.normalizer
        (((graphFixedPosUnipotent TwistTag.D4 K τ).subgroupOf (graphFixedRootGroup TwistTag.D4 K τ) :
          Subgroup (graphFixedRootGroup TwistTag.D4 K τ)) : Set (graphFixedRootGroup TwistTag.D4 K τ)) →
      h ∈ Subgroup.normalizer
        (((graphFixedNegUnipotent TwistTag.D4 K τ).subgroupOf (graphFixedRootGroup TwistTag.D4 K τ) :
          Subgroup (graphFixedRootGroup TwistTag.D4 K τ)) : Set (graphFixedRootGroup TwistTag.D4 K τ)) →
      h * u = u * h) :
    T * (u : ModGL TwistTag.D4.tag K) = (u : ModGL TwistTag.D4.tag K) * T := by
  obtain ⟨hTt, hTΓ⟩ := Subgroup.mem_inf.1 hT
  have hNU : (⟨T, hΓC hTΓ⟩ : graphFixedRootGroup TwistTag.D4 K τ) ∈ Subgroup.normalizer
      (((graphFixedPosUnipotent TwistTag.D4 K τ).subgroupOf (graphFixedRootGroup TwistTag.D4 K τ) :
        Subgroup (graphFixedRootGroup TwistTag.D4 K τ)) : Set (graphFixedRootGroup TwistTag.D4 K τ)) :=
    S152T.mem_normalizer_subgroupOf (graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.D4 K τ)
      (S152T.mem_normalizer_inf ((triangular_borel_structure.{0, 0} TwistTag.D4.tag K).2.2.1 hTt) hTΓ)
  have hNV : (⟨T, hΓC hTΓ⟩ : graphFixedRootGroup TwistTag.D4 K τ) ∈ Subgroup.normalizer
      (((graphFixedNegUnipotent TwistTag.D4 K τ).subgroupOf (graphFixedRootGroup TwistTag.D4 K τ) :
        Subgroup (graphFixedRootGroup TwistTag.D4 K τ)) : Set (graphFixedRootGroup TwistTag.D4 K τ)) :=
    S152T.mem_normalizer_subgroupOf (graphFixedNegUnipotent_le_graphFixedRootGroup TwistTag.D4 K τ)
      (S152T.mem_normalizer_inf (torusGroup_le_normalizer_negUnipotent hTt) hTΓ)
  exact congrArg Subtype.val (hc _ hNU hNV)

end D4Fixed

section D4U


variable {K : Type} [Field K] [Finite K]

theorem mem_nativeData_U_of_mem_posUnipotent_tag {τ : Tag} {x : ModGL τ K}
    (hx : x ∈ posUnipotent τ K) :
    (⟨x, posUnipotent_le_adjointGroup hx⟩ : adjointGroup τ K) ∈ (nativeData τ K).U := by
  have h : (posUnipotent τ K).subgroupOf (adjointGroup τ K) ≤ (nativeData τ K).U := by
    rw [posUnipotent, rootSpan,
      CFSG.LieType.Ree.subgroupOf_biSup_of_le fun α _ => rootSubgroup_le_adjointGroup α]
    refine iSup₂_le fun α hα => ?_
    exact ((rootOperatorFamily τ).subgroupOf_rootSubgroup_eq K ⟨α, hα.1⟩).le.trans
      (RootGroupData.X_le_U (D := nativeData τ K) (α := ⟨α, hα.1⟩) hα.2)
  exact h (Subgroup.mem_subgroupOf.2 hx)

end D4U

section D4Main


variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)

local notation "τ₀" => σ.toRingHom

theorem borelCentralizerTrivial_d4 {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    BorelCentralizerTrivial (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨⟨PU, hPU⟩, ⟨PV, hPV⟩, hUV, hopp, -, -⟩ :=
    exceptional_fixed_Sylow_opposition TwistTag.D4 K 2 σ w₀ hw₀
  have hU : IsSylowTwoOf ((graphFixedPosUnipotent TwistTag.D4 K τ₀).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K τ₀)) ⊤ := by
    rw [← hPU]
    exact isSylowTwoOf_top_iff.mpr ⟨PU.isPGroup', PU.not_dvd_index⟩
  have hV : IsSylowTwoOf ((graphFixedNegUnipotent TwistTag.D4 K τ₀).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K τ₀)) ⊤ := by
    rw [← hPV]
    exact isSylowTwoOf_top_iff.mpr ⟨PV.isPGroup', PV.not_dvd_index⟩
  have hUV' : (graphFixedPosUnipotent TwistTag.D4 K τ₀).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K τ₀) ⊓
      (graphFixedNegUnipotent TwistTag.D4 K τ₀).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K τ₀) = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have h : (x : ModGL TwistTag.D4.tag K) ∈
        graphFixedPosUnipotent TwistTag.D4 K τ₀ ⊓ graphFixedNegUnipotent TwistTag.D4 K τ₀ :=
      Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).1, (Subgroup.mem_inf.1 hx).2⟩
    rw [hUV, Subgroup.mem_bot] at h
    exact Subgroup.mem_bot.2 (Subtype.ext h)
  refine bct_of_opposition hU hV hUV' ?_ ?_ (exceptional_fixed_center_trivial TwistTag.D4 K σ) ?_
  · intro S hS hUS
    obtain ⟨hp, hi⟩ := isSylowTwoOf_top_iff.mp hS
    have hcoe : ((hp.toSylow hi : Sylow 2 (graphFixedRootGroup TwistTag.D4 K τ₀)) :
        Subgroup (graphFixedRootGroup TwistTag.D4 K τ₀)) = S := IsPGroup.toSylow_coe hp hi
    obtain ⟨u, hu, hSu⟩ := (hopp (hp.toSylow hi)).1 (by rw [hcoe]; exact hUS)
    exact ⟨u, hu, hcoe ▸ hSu⟩
  ·
    rintro δ hUδ hVδ ⟨w, hwU, hw⟩
    have hδA : δ ∈ graphFixedUnipotentStabilizer TwistTag.D4 K τ₀ := ⟨hUδ, hVδ⟩
    obtain ⟨u, δ', hδ⟩ := exists_normalActor_eq_D4 Nat.prime_two (by omega) hK σ hσ hδA
    have hX : ∀ (a : Fin TwistTag.D4.foldedTag.rank) (c : orbitField TwistTag.D4 K τ₀ a),
        ((u a : (orbitField TwistTag.D4 K τ₀ a)ˣ) : orbitField TwistTag.D4 K τ₀ a) *
          orbitFieldRestrict TwistTag.D4 σ δ' a c = c := by
      intro a c
      obtain ⟨hle, hnorm, -, hdec, -, huniq, -, -, -, -⟩ :=
        fixed_simple_positive_complement TwistTag.D4 K σ a
      have hxU : fixedOrbitX TwistTag.D4 K τ₀ a c ∈
          (graphFixedPosUnipotent TwistTag.D4 K τ₀).subgroupOf
            (graphFixedRootGroup TwistTag.D4 K τ₀) := orbitX_mem_graphFixedPosUnipotent _ τ₀ a c
      have h1 : δ (fixedOrbitX TwistTag.D4 K τ₀ a c) = fixedOrbitX TwistTag.D4 K τ₀ a
          (((u a : (orbitField TwistTag.D4 K τ₀ a)ˣ) : orbitField TwistTag.D4 K τ₀ a) *
            orbitFieldRestrict TwistTag.D4 σ δ' a c) := by
        rw [hδ, normalActor_fixedOrbitX]
      have h2 := hw _ hxU
      have h3 : (w : ModGL TwistTag.D4.tag K) *
          (orbitX TwistTag.D4 K τ₀ a c : ModGL TwistTag.D4.tag K) *
            (w : ModGL TwistTag.D4.tag K)⁻¹ =
          (orbitX TwistTag.D4 K τ₀ a
            (((u a : (orbitField TwistTag.D4 K τ₀ a)ˣ) : orbitField TwistTag.D4 K τ₀ a) *
              orbitFieldRestrict TwistTag.D4 σ δ' a c) : ModGL TwistTag.D4.tag K) := by
        have := congrArg (fun g : graphFixedRootGroup TwistTag.D4 K τ₀ =>
          (g : ModGL TwistTag.D4.tag K)) (h2.symm.trans h1)
        exact this
      exact eq_of_conj_eq_of_complement
        (fun c : orbitField TwistTag.D4 K τ₀ a =>
          (orbitX TwistTag.D4 K τ₀ a c : ModGL TwistTag.D4.tag K))
        hle hnorm (fun c => orbitX_mem_graphFixedPosUnipotent _ τ₀ a c)
        (fun c c' => by
          rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← orbitX_add, ← orbitX_add, add_comm])
        hdec huniq (Subgroup.mem_subgroupOf.mp hwU) h3
    have hu : ∀ a, u a = 1 := fun a => by
      have h2 : ((u a : orbitField TwistTag.D4 K τ₀ a) : K) * δ' 1 = 1 :=
        congrArg Subtype.val (hX a 1)
      rw [map_one, mul_one] at h2
      exact Units.ext (Subtype.ext h2)
    have h0 : orbitField TwistTag.D4 K τ₀ ⟨0, by decide⟩ = ⊤ :=
      orbitField_D4_zero_eq_top σ (ringEquiv_cube_apply_eq hK hσ)
    have hδ'1 : δ' = 1 := by
      refine RingEquiv.ext fun c => ?_
      have hmem : c ∈ orbitField TwistTag.D4 K τ₀ ⟨0, by decide⟩ := by
        rw [h0]
        exact Subfield.mem_top c
      have h : ((u ⟨0, by decide⟩ : orbitField TwistTag.D4 K τ₀ ⟨0, by decide⟩) : K) * δ' c = c :=
        congrArg Subtype.val (hX ⟨0, by decide⟩ ⟨c, hmem⟩)
      have hu0 : ((u ⟨0, by decide⟩ : orbitField TwistTag.D4 K τ₀ ⟨0, by decide⟩) : K) = 1 :=
        congrArg (fun x : orbitField TwistTag.D4 K τ₀ ⟨0, by decide⟩ => (x : K))
          (congrArg Units.val (hu ⟨0, by decide⟩))
      rw [hu0, one_mul] at h
      exact h
    have hu1 : u = 1 := funext hu
    have hδ1 : normalActor σ u δ' = 1 := by
      rw [hu1, hδ'1, normalActor_one_right]
      exact map_one _
    exact hδ.trans hδ1
  ·
    intro u hu hc
    obtain ⟨a₀, ha₀⟩ := S152T.exists_units_orderOf_eq_card_sub_one (K := K)
    have hq : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    have ha₀' : orderOf a₀ = (2 ^ f) ^ 3 - 1 := by rw [ha₀, hK]
    have hσ3' : ∀ c, σ (σ (σ c)) = c := ringEquiv_cube_apply_eq hK hσ
    have hσ3 : σ ^ 3 = 1 := RingEquiv.ext fun c => by
      rw [ringEquiv_pow_three_apply]
      exact hσ3' c
    have hΓC : twistedFixedGroup TwistTag.D4 K τ₀ ≤ graphFixedRootGroup TwistTag.D4 K τ₀ :=
      (even_triality_fixed_group_eq_root_group K (ringChar.eq K 2) σ hσ3').1.le
    have hTo : trialityOuterTorus K σ a₀ ∈ graphFixedTorus TwistTag.D4 K τ₀ := by
      have h := trialityTorusHom_mem_graphFixedTorus hσ3 (a₀, 1)
      rwa [trialityTorusHom_apply, trialityMiddleTorus_one, mul_one] at h
    have hTm : trialityMiddleTorus K σ (trialityNorm σ hσ3 a₀) ∈
        graphFixedTorus TwistTag.D4 K τ₀ := by
      have h := trialityTorusHom_mem_graphFixedTorus hσ3 (1, trialityNorm σ hσ3 a₀)
      rwa [trialityTorusHom_apply, trialityOuterTorus_one, one_mul] at h
    have hx : (u : ModGL TwistTag.D4.tag K) ∈ posUnipotent TwistTag.D4.tag K :=
      (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hu)).1
    have h1 := eq_one_of_mem_U_of_forall_commute
      (A := {d4Outer σ a₀, d4Middle (a₀ * Units.map σ.toRingHom.toMonoidHom a₀ *
        Units.map σ.toRingHom.toMonoidHom (Units.map σ.toRingHom.toMonoidHom a₀))})
      (by
        rintro h (rfl | rfl)
        · exact d4Outer_mem_H σ a₀
        · exact d4Middle_mem_H _)
      (fun β hβ y hy hyc => d4_hchar hq hσ ha₀' β hβ hy hyc)
      d4_isReduced d4_negCheck (mem_nativeData_U_of_mem_posUnipotent_tag hx)
      (by
        rintro h (rfl | rfl)
        · apply Subtype.ext
          have h2 := commute_of_mem_graphFixedTorus hΓC hTo hc
          rw [← coe_d4Outer σ a₀] at h2
          show ((d4Outer σ a₀ : adjointGroup TwistTag.D4.tag K) : ModGL TwistTag.D4.tag K) *
              (u : ModGL TwistTag.D4.tag K) *
              ((d4Outer σ a₀ : adjointGroup TwistTag.D4.tag K) : ModGL TwistTag.D4.tag K)⁻¹ =
            (u : ModGL TwistTag.D4.tag K)
          rw [h2]
          group
        · apply Subtype.ext
          have h2 := commute_of_mem_graphFixedTorus hΓC hTm hc
          rw [← coe_d4Middle_norm σ hσ3 a₀] at h2
          show ((d4Middle (a₀ * Units.map σ.toRingHom.toMonoidHom a₀ *
              Units.map σ.toRingHom.toMonoidHom (Units.map σ.toRingHom.toMonoidHom a₀)) :
                adjointGroup TwistTag.D4.tag K) : ModGL TwistTag.D4.tag K) *
              (u : ModGL TwistTag.D4.tag K) *
              ((d4Middle (a₀ * Units.map σ.toRingHom.toMonoidHom a₀ *
                Units.map σ.toRingHom.toMonoidHom (Units.map σ.toRingHom.toMonoidHom a₀)) :
                  adjointGroup TwistTag.D4.tag K) : ModGL TwistTag.D4.tag K)⁻¹ =
            (u : ModGL TwistTag.D4.tag K)
          rw [h2]
          group)
    have h2 : (u : ModGL TwistTag.D4.tag K) = 1 :=
      congrArg (fun x : adjointGroup TwistTag.D4.tag K => (x : ModGL TwistTag.D4.tag K)) h1
    exact Subtype.ext h2

end D4Main

section D4Fam


theorem bctFam3D4_proof : BCTFam3D4 := by
  intro f hf X _ _ hmodel
  obtain ⟨-, K, _, _, hK, σ₀, hσ₀, ⟨e⟩⟩ := hmodel
  have hK3 : Nat.card K = (2 ^ f) ^ 3 := hK
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega)
    (show Nat.card K = 2 ^ (f * 3) by rw [hK3, ← pow_mul])
  obtain ⟨σ, rfl⟩ : ∃ σ : K ≃+* K, σ.toRingHom = σ₀ :=
    ⟨RingEquiv.ofBijective σ₀ ⟨σ₀.injective, Finite.surjective_of_injective σ₀.injective⟩, rfl⟩
  have hσ : ∀ c, σ c = c ^ (2 ^ f) := hσ₀
  obtain ⟨-, -, -, -, -, -, -, ⟨E⟩⟩ :=
    even_triality_exact_automorphism_normal_form (by omega) K hK3 σ hσ
  exact BorelCentralizerTrivial.of_mulEquiv (e.trans E).symm
    (borelCentralizerTrivial_d4 σ hf hK3 hσ)

end D4Fam

end CFSG.Quasithin
