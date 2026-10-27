module

public import CFSG.RankThree.SteinbergR3ELinearTwoFieldDescent
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoFixedCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDescent

public section

namespace CFSG.RankThree.LinearTwo

open Matrix CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ComponentClassification.CatalogueBLinearTwoDescent (fixedSubfield mem_fixedSubfield)
open CFSG.ComponentClassification.UnbalancedGS.SubfieldCentralizer (subfieldD subfieldD_mk
  subfieldD_injective subfieldD_surj_mk subfieldD_G fieldExtension_commute_subfieldD
  fieldExtension_mul_translation fieldExtension_mul_inversion
  eq_one_of_commute_translation_inversion fieldExtension_mem_zpowers upperGL invGL map_upperGL
  map_invGL coordinateGLAction_upperGL coordinateGLAction_invGL)
open CFSG.ComponentClassification.CatalogueBLinearTwoFixed
  (coordinatePGLAction_mem_field_centralizer_iff)
open CFSG.ComponentClassification.CatalogueBHigherLinearField
  (pgl_fixed_iff_mem_subfield_range pglFieldAut_two)
open CFSG.Semidihedral.ProjectiveNonsquareInvolutions (projective_mem_G_iff)

universe u

theorem div_two_pow_eq_and_odd {r p : ℕ} (hr : Odd r) (hp : Odd p) :
    r ^ p / 2 = r / 2 * ∑ i ∈ Finset.range p, r ^ i ∧ Odd (∑ i ∈ Finset.range p, r ^ i) := by
  obtain ⟨s, rfl⟩ := hr
  have hpow : Odd ((2 * s + 1) ^ p) := (odd_two_mul_add_one s).pow
  obtain ⟨t, ht⟩ := hpow
  have hgeom : ((∑ i ∈ Finset.range p, (2 * s + 1) ^ i : ℕ) : ℤ) * (((2 * s + 1 : ℕ) : ℤ) - 1) =
      (((2 * s + 1 : ℕ) : ℤ)) ^ p - 1 := by
    push_cast
    exact geom_sum_mul _ p
  have hsum : (∑ i ∈ Finset.range p, (2 * s + 1) ^ i) * s = t := by
    have h2 : ((((2 * s + 1) ^ p : ℕ)) : ℤ) = 2 * (t : ℤ) + 1 := by exact_mod_cast ht
    push_cast at hgeom h2
    have : ((∑ i ∈ Finset.range p, (2 * s + 1) ^ i : ℕ) : ℤ) * s = t := by
      push_cast
      nlinarith [hgeom, h2]
    exact_mod_cast this
  have hpar : ∀ n, (∑ i ∈ Finset.range n, (2 * s + 1) ^ i) % 2 = n % 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, Nat.add_mod, ih]
      have : (2 * s + 1) ^ n % 2 = 1 := by
        rw [Nat.pow_mod]
        simp [Nat.add_mod]
      rw [this]
      omega
  refine ⟨?_, ?_⟩
  · rw [ht, show (2 * t + 1) / 2 = t by omega, show (2 * s + 1) / 2 = s by omega, mul_comm,
      hsum]
  · have := hpar p
    obtain ⟨k, hk⟩ := hp
    rw [Nat.odd_iff]
    omega

theorem isSquare_units_map_iff {K : Type u} [Field K] [Finite K] (S : Subfield K) {p : ℕ}
    (hodd : Odd p) (hcard : Nat.card K = Nat.card S ^ p) (u : Sˣ) :
    IsSquare (Units.map S.subtype.toMonoidHom u) ↔ IsSquare u := by
  classical
  refine ⟨fun h => ?_, fun ⟨r, hr⟩ => ⟨Units.map S.subtype.toMonoidHom r, by rw [hr, map_mul]⟩⟩
  have hchar : ringChar S = ringChar K := by
    have := RingHom.charP S.subtype S.subtype_injective (ringChar K)
    exact ringChar.eq S (ringChar K)
  by_cases h2 : ringChar K = 2
  · obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (hchar.trans h2) (u : S)
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hr
      exact u.ne_zero hr
    exact ⟨Units.mk0 r hr0, Units.ext (by rw [Units.val_mul, Units.val_mk0]; exact hr)⟩
  · have : Fintype S := Fintype.ofFinite S
    have : Fintype K := Fintype.ofFinite K
    have h2S : ringChar S ≠ 2 := hchar ▸ h2
    rw [FiniteField.unit_isSquare_iff h2] at h
    rw [FiniteField.unit_isSquare_iff h2S]
    set r := Fintype.card S with hrdef
    have hK : Fintype.card K = r ^ p := by
      rw [← Nat.card_eq_fintype_card, hcard, Nat.card_eq_fintype_card]
    rw [hK] at h
    have hu : u ^ (r ^ p / 2) = 1 := by
      apply Units.map_injective (f := S.subtype.toMonoidHom) S.subtype_injective
      rw [map_pow, h, map_one]
    have hrodd : Odd r := Nat.odd_iff.mpr (FiniteField.odd_card_of_char_ne_two h2S)
    obtain ⟨hdiv, hmodd⟩ := div_two_pow_eq_and_odd hrodd hodd
    set m := ∑ i ∈ Finset.range p, r ^ i
    have hε : (u ^ (r / 2)) ^ 2 = 1 := by
      rw [← pow_mul]
      have hr1 : r / 2 * 2 = r - 1 := by
        obtain ⟨s, hs⟩ := hrodd
        omega
      rw [hr1]
      have hcardu : Fintype.card Sˣ = r - 1 := by
        rw [Fintype.card_units]
      rw [← hcardu]
      exact pow_card_eq_one
    rw [hdiv, pow_mul] at hu
    obtain ⟨k, hk⟩ := hmodd
    rw [hk, pow_succ, pow_mul, hε, one_pow, one_mul] at hu
    exact hu

theorem linear_two_odd_field_fixed_group_and_centralizer (K : Type u) [Field K] [Finite K]
    (σ : K ≃+* K) {p : ℕ} (hodd : Odd p) (hσ : orderOf σ = p) :
    (∀ A : GL (Fin 2) (fixedSubfield K σ),
      (subfieldD (fixedSubfield K σ) (pglEquivCoordinateD (fixedSubfield K σ)
        (ProjGenLinGroup.mk A)) : Equiv.Perm (Omega K)) =
          coordinateGLAction K (GeneralLinearGroup.map (fixedSubfield K σ).subtype A)) ∧
    Function.Injective (subfieldD (fixedSubfield K σ)) ∧
    coordinateD K ⊓ Subgroup.centralizer {fieldExtension K σ} =
      ((coordinateD K).subtype.comp (subfieldD (fixedSubfield K σ))).range ∧
    coordinateG K ⊓ Subgroup.centralizer {fieldExtension K σ} =
      ((coordinateG (fixedSubfield K σ)).subgroupOf (coordinateD (fixedSubfield K σ))).map
        ((coordinateD K).subtype.comp (subfieldD (fixedSubfield K σ))) ∧
    Subgroup.centralizer
        ((((coordinateG (fixedSubfield K σ)).subgroupOf (coordinateD (fixedSubfield K σ))).map
          ((coordinateD K).subtype.comp (subfieldD (fixedSubfield K σ))) :
            Subgroup (Equiv.Perm (Omega K))) : Set (Equiv.Perm (Omega K))) ⊓ coordinateE K =
      Subgroup.zpowers (fieldExtension K σ) ∧
    Nat.card (Subgroup.zpowers (fieldExtension K σ)) = p := by
  classical
  set k := fixedSubfield K σ with hkdef
  have hσk : ∀ x ∈ k, σ x = x := fun x hx => (mem_fixedSubfield K σ x).mp hx
  obtain ⟨n, hℓ, hKn⟩ := finiteField_primePower K
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0, pow_zero] at hKn
      exact absurd hKn (Finite.one_lt_card (α := K)).ne'
    · exact h0
  obtain ⟨hdvd, hkcard⟩ := card_fixedSubfield hℓ hn hKn σ
  rw [hσ] at hdvd hkcard
  have hKk : Nat.card K = Nat.card k ^ p := by
    rw [hkcard, ← pow_mul, Nat.div_mul_cancel hdvd, hKn]
  have hDcent : coordinateD K ⊓ Subgroup.centralizer {fieldExtension K σ} =
      ((coordinateD K).subtype.comp (subfieldD k)).range := by
    apply le_antisymm
    · rintro g ⟨hgD, hgc⟩
      rw [← coordinatePGLAction_range_eq_D] at hgD
      obtain ⟨g', rfl⟩ := hgD
      have hfix := (coordinatePGLAction_mem_field_centralizer_iff K σ g').mp hgc
      rw [← pglFieldAut_two] at hfix
      obtain ⟨y, hy⟩ := (pgl_fixed_iff_mem_subfield_range (Fin 2) K σ g').mp hfix
      obtain ⟨B, rfl⟩ := ProjGenLinGroup.mk_surjective y
      refine ⟨pglEquivCoordinateD k (ProjGenLinGroup.mk B), ?_⟩
      change (subfieldD k (pglEquivCoordinateD k (ProjGenLinGroup.mk B)) :
        Equiv.Perm (Omega K)) = _
      rw [subfieldD_mk, ← hy]
      rfl
    · rintro _ ⟨y, rfl⟩
      exact ⟨(subfieldD k y).2, Subgroup.mem_centralizer_singleton_iff.mpr
        (fieldExtension_commute_subfieldD k σ hσk y).symm⟩
  set jG : Subgroup (Equiv.Perm (Omega K)) :=
    ((coordinateG k).subgroupOf (coordinateD k)).map ((coordinateD K).subtype.comp (subfieldD k))
    with hjG
  have hGcent : coordinateG K ⊓ Subgroup.centralizer {fieldExtension K σ} = jG := by
    apply le_antisymm
    · rintro g ⟨hgG, hgc⟩
      obtain ⟨y, hy⟩ := hDcent.le ⟨coordinateG_le_D K hgG, hgc⟩
      obtain ⟨B, rfl⟩ := subfieldD_surj_mk k y
      refine Subgroup.mem_map.mpr ⟨_, ?_, hy⟩
      rw [Subgroup.mem_subgroupOf]
      have hgB : g = coordinateGLAction K (GeneralLinearGroup.map k.subtype B) := by
        rw [← hy]
        exact subfieldD_mk k B
      have hsqK : IsSquare (GeneralLinearGroup.det (GeneralLinearGroup.map k.subtype B)) := by
        apply (projective_mem_G_iff K (GeneralLinearGroup.map k.subtype B)).mp
        rw [hgB] at hgG
        exact hgG
      rw [Matrix.GeneralLinearGroup.map_det] at hsqK
      have hsqk := (isSquare_units_map_iff k hodd hKk _).mp hsqK
      exact (projective_mem_G_iff k B).mpr hsqk
    · rintro _ ⟨y, hyG, rfl⟩
      exact ⟨subfieldD_G k y hyG, (hDcent.ge ⟨y, rfl⟩).2⟩
  have hT : ∀ t : k, translation K (t : K) ∈ jG := by
    intro t
    refine Subgroup.mem_map.mpr ⟨pglEquivCoordinateD k (ProjGenLinGroup.mk (upperGL t)),
      ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      change coordinateGLAction k (upperGL t) ∈ coordinateG k
      rw [coordinateGLAction_upperGL]
      exact Subgroup.subset_closure (Or.inl ⟨t, rfl⟩)
    · change (subfieldD k (pglEquivCoordinateD k (ProjGenLinGroup.mk (upperGL t))) :
        Equiv.Perm (Omega K)) = _
      rw [subfieldD_mk, map_upperGL, coordinateGLAction_upperGL]
  have hI : inversion K ∈ jG := by
    refine Subgroup.mem_map.mpr ⟨pglEquivCoordinateD k (ProjGenLinGroup.mk invGL), ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      change coordinateGLAction k invGL ∈ coordinateG k
      rw [coordinateGLAction_invGL]
      exact Subgroup.subset_closure (Or.inr rfl)
    · change (subfieldD k (pglEquivCoordinateD k (ProjGenLinGroup.mk invGL)) :
        Equiv.Perm (Omega K)) = _
      rw [subfieldD_mk, map_invGL, coordinateGLAction_invGL]
  have hEcent : Subgroup.centralizer (jG : Set (Equiv.Perm (Omega K))) ⊓ coordinateE K =
      Subgroup.zpowers (fieldExtension K σ) := by
    apply le_antisymm
    · rintro e ⟨hcent, hE⟩
      rw [← coordinateSemilinearAction_range_eq_E] at hE
      obtain ⟨y, rfl⟩ := hE
      rw [← SemidirectProduct.inl_left_mul_inr_right y, map_mul, coordinateSemilinearAction_inl,
        coordinateSemilinearAction_inr] at hcent ⊢
      set d := coordinatePGLAction K y.left with hd
      set τ := y.right
      have hcomm : ∀ h ∈ jG, h * (d * fieldExtension K τ) = d * fieldExtension K τ * h :=
        fun h hh => Subgroup.mem_centralizer_iff.mp hcent h hh
      have hdD : d ∈ coordinateD K := by
        rw [← coordinatePGLAction_range_eq_D]
        exact ⟨_, rfl⟩
      have key : ∀ T : Equiv.Perm (Omega K), T ∈ jG →
          fieldExtension K τ * T = T * fieldExtension K τ → d * T = T * d := by
        intro T hTS hfT
        have := hcomm T hTS
        have h2 : (T * d) * fieldExtension K τ = (d * T) * fieldExtension K τ := by
          rw [mul_assoc, this, mul_assoc, hfT, mul_assoc]
        exact (mul_right_cancel h2).symm
      have h1 : d * translation K 1 = translation K 1 * d := by
        have hT1 := hT 1
        rw [OneMemClass.coe_one] at hT1
        exact key _ hT1 (by rw [fieldExtension_mul_translation, map_one])
      have h2 : d * inversion K = inversion K * d := key _ hI (fieldExtension_mul_inversion τ)
      have hd1 : d = 1 := eq_one_of_commute_translation_inversion d hdD h1 h2
      rw [hd1, one_mul] at hcomm ⊢
      have hτk : ∀ x, σ x = x → τ x = x := by
        intro x hx
        have hxk : x ∈ k := (mem_fixedSubfield K σ x).mpr hx
        have := hcomm _ (hT ⟨x, hxk⟩)
        rw [fieldExtension_mul_translation] at this
        have h3 := mul_right_cancel this
        have h4 := congrArg (fun φ : Equiv.Perm (Omega K) => φ (some 0)) h3
        simp only [translation_some, zero_add, Option.some.injEq] at h4
        exact h4.symm
      exact fieldExtension_mem_zpowers (mem_zpowers_of_forall_fixed hℓ hn hKn σ τ hτk)
    · rw [Subgroup.zpowers_le]
      refine ⟨Subgroup.mem_centralizer_iff.mpr ?_, Subgroup.subset_closure (Or.inr ⟨σ, rfl⟩)⟩
      intro h hh
      obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp hh
      exact (fieldExtension_commute_subfieldD k σ hσk x).symm
  have hord : orderOf (fieldExtension K σ) = p := by
    have hinj : Function.Injective
        ((coordinateSemilinearAction K).comp (SemidirectProduct.inr : (K ≃+* K) →* PGammaL2 K)) :=
      (coordinateSemilinearAction_injective K).comp SemidirectProduct.inr_injective
    rw [← coordinateSemilinearAction_inr, ← hσ]
    exact orderOf_injective _ hinj σ
  refine ⟨subfieldD_mk k, subfieldD_injective k, hDcent, hGcent, hEcent, ?_⟩
  rw [Nat.card_zpowers, hord]

end CFSG.RankThree.LinearTwo
