module

public import CFSG.RankThree.Chevalley.SteinbergCBTrialityQPlusFields
public import CFSG.RankThree.Chevalley.SteinbergCBTrialityQuadraticTorus

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical CFSG.RankThree.QuadraticSL2 TrialityFold
open scoped Pointwise

@[expose] def trialityRootPairFixed {K₂ : Type} [Field K₂] (σ₂ : K₂ →+* K₂)
    (O : Set (Fin TwistTag.D4.tag.rank → ℤ)) : Subgroup (ModGL TwistTag.D4.tag K₂) :=
  (rootSpan TwistTag.D4.tag K₂ O ⊓ graphFixedRootGroup TwistTag.D4 K₂ σ₂) ⊔
    (rootSpan TwistTag.D4.tag K₂ (-O) ⊓ graphFixedRootGroup TwistTag.D4 K₂ σ₂)

section RankOne

variable {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K K₂ : Type} [Field K] [Field K₂] [Algebra K K₂]
  (hK : Nat.card K = (ℓ ^ f) ^ 3) (hK₂ : Nat.card K₂ = (ℓ ^ f) ^ 6) {σ : K →+* K}
  (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {σ₂ : K₂ ≃+* K₂} (hσ₂ : ∀ c, σ₂ c = c ^ ((ℓ ^ f) ^ 4))
  {τ : K₂ ≃+* K₂} (hτ : ∀ c, τ c = c ^ ((ℓ ^ f) ^ 3))

include hℓ hK₂ hσ₂ in
theorem sigma₂_pow_three : σ₂ ^ 3 = 1 := RingEquiv.ext fun c => by
  change σ₂ (σ₂ (σ₂ c)) = c
  rw [hσ₂, hσ₂, hσ₂, ← pow_mul, ← pow_mul,
    show (ℓ ^ f) ^ 4 * ((ℓ ^ f) ^ 4 * (ℓ ^ f) ^ 4) = (ℓ ^ f) ^ 6 * (ℓ ^ f) ^ 6 by ring, pow_mul,
    pow_q_six_eq hK₂ hℓ, pow_q_six_eq hK₂ hℓ]

include hℓ hf hK hK₂ hσ hσ₂ hτ in
theorem exists_fixed_matrix_orbitConjRankOneHom
    {g : ModGL TwistTag.D4.tag K₂}
    (hg : g ∈ graphFixedRootGroup TwistTag.D4 K₂ σ₂.toRingHom)
    (hzg : trialityOpposition K₂ = g * (Units.map (entrywiseHom τ.toRingHom) g)⁻¹)
    {w : WeylGroup TwistTag.D4.tag} (hw : w ∈ relWeylTwist TwistTag.D4)
    (b : Fin TwistTag.D4.foldedTag.rank) :
    Function.Injective (orbitConjRankOneHom TwistTag.D4 K₂ σ₂.toRingHom w b) ∧
    ∃ P : GL (Fin 2) (orbitField TwistTag.D4 K₂ σ₂.toRingHom b),
      (graphFixedRootPair TwistTag.D4 K₂ σ₂.toRingHom (fixedOrbitImage TwistTag.D4 w b) ⊓
          trialityConjImage K σ g).comap (orbitConjRankOneHom TwistTag.D4 K₂ σ₂.toRingHom w b) =
        (Matrix.SpecialLinearGroup.map (algebraMap (orbitFieldFixed σ₂.toRingHom τ.toRingHom b)
          (orbitField TwistTag.D4 K₂ σ₂.toRingHom b))).range.map (conjSL P) ∧
      (fun A : SL2 (orbitField TwistTag.D4 K₂ σ₂.toRingHom b) =>
          Matrix.trace (A : Matrix (Fin 2) (Fin 2) (orbitField TwistTag.D4 K₂ σ₂.toRingHom b))) ''
          ((graphFixedRootPair TwistTag.D4 K₂ σ₂.toRingHom (fixedOrbitImage TwistTag.D4 w b) ⊓
            trialityConjImage K σ g).comap
              (orbitConjRankOneHom TwistTag.D4 K₂ σ₂.toRingHom w b) : Set _) =
        Set.range (algebraMap (orbitFieldFixed σ₂.toRingHom τ.toRingHom b)
          (orbitField TwistTag.D4 K₂ σ₂.toRingHom b)) ∧
      Subgroup.centralizer ((((graphFixedRootPair TwistTag.D4 K₂ σ₂.toRingHom
          (fixedOrbitImage TwistTag.D4 w b) ⊓ trialityConjImage K σ g).comap
            (orbitConjRankOneHom TwistTag.D4 K₂ σ₂.toRingHom w b)).map
              Matrix.SpecialLinearGroup.toGL :
          Subgroup (GL (Fin 2) (orbitField TwistTag.D4 K₂ σ₂.toRingHom b))) :
            Set (GL (Fin 2) (orbitField TwistTag.D4 K₂ σ₂.toRingHom b))) =
        (Matrix.GeneralLinearGroup.scalar (Fin 2)).range := by
  have hσ₂3 := sigma₂_pow_three hℓ hK₂ hσ₂
  have hinj := orbitConjRankOneHom_injective_D4 σ₂ hσ₂3 w b
  obtain ⟨-, -, -, hall⟩ := triality_qplus_quadratic_realization_and_toral_Sylow ℓ f hℓ hf K K₂
    hK hK₂ σ hσ σ₂ hσ₂ τ.toRingHom hτ
  obtain ⟨hF2, hΓ, -⟩ := hall g hg hzg
  have hzΓ : trialityOpposition K₂ ∈ twistedFixedGroup TwistTag.D4 K₂ σ₂.toRingHom :=
    graphFixedRootGroup_le _ _ _ (trialityOpposition_mem_graphFixedRootGroup _)
  have hτσ := tau_comm_sigma₂ hσ₂ hτ
  obtain ⟨M, hM⟩ := exists_semilinearConj_orbitConjRankOneHom (σ := σ₂.toRingHom) hτσ
    (trialityOpposition_mem_monomialSubgroup (K := K₂)) weylQuotientHom_trialityOpposition_smul
    hzΓ hw b hinj
  set Φ := orbitConjRankOneHom TwistTag.D4 K₂ σ₂.toRingHom w b
  have hinvol : ∀ A, semilinearConj M (orbitFieldRestrict τ hτσ b)
      (semilinearConj M (orbitFieldRestrict τ hτσ b) A) = A := fun A => hinj (by
    rw [hM, hM, hF2])
  have hrange := range_orbitConjRankOneHom (K := K₂) (σ := σ₂.toRingHom) hw b
  have hfix : (semilinearConj M (orbitFieldRestrict τ hτσ b)).eqLocus (MonoidHom.id _) =
      (graphFixedRootPair TwistTag.D4 K₂ σ₂.toRingHom (fixedOrbitImage TwistTag.D4 w b) ⊓
        trialityConjImage K σ g).comap Φ := by
    ext A
    change semilinearConj M (orbitFieldRestrict τ hτσ b) A = A ↔
      Φ A ∈ graphFixedRootPair TwistTag.D4 K₂ σ₂.toRingHom (fixedOrbitImage TwistTag.D4 w b) ⊓
        trialityConjImage K σ g
    rw [hΓ]
    constructor
    · intro h
      have hQ : Φ A ∈ graphFixedRootPair TwistTag.D4 K₂ σ₂.toRingHom
          (fixedOrbitImage TwistTag.D4 w b) := by
        rw [← hrange]
        exact ⟨A, rfl⟩
      refine Subgroup.mem_inf.2 ⟨hQ, Subgroup.mem_inf.2
        ⟨orbitConjRankOneHom_mem_graphFixedRootGroup hw b A, ?_⟩⟩
      change twistedEntrywise (trialityOpposition K₂) τ.toRingHom (Φ A) = Φ A
      rw [← hM, h]
    · intro h
      obtain ⟨-, h'⟩ := Subgroup.mem_inf.1 h
      obtain ⟨-, h''⟩ := Subgroup.mem_inf.1 h'
      exact hinj (by rw [hM]; exact h'')
  obtain ⟨hfin, hdeg, hpow⟩ := orbitFieldFixed_data hℓ hf hK hK₂ hσ₂ hτ σ hσ b
  have := hfin
  obtain ⟨P, -, hP, htr, hcent⟩ := even_quadratic_semilinear_SL2_fixed_matrix_group
    (orbitFieldFixed σ₂.toRingHom τ.toRingHom b) (orbitField TwistTag.D4 K₂ σ₂.toRingHom b) hdeg
    (orbitFieldRestrict τ hτσ b) hpow M hinvol
  rw [hfix] at hP htr hcent
  exact ⟨hinj, P, hP, htr, hcent⟩

end RankOne

theorem isQuasisimple_of_comap_eq_conjSL {L F G : Type*} [Field L] [Field F] [Algebra F L]
    [Group G] {ι : SL2 L →* G} (hι : Function.Injective ι) {R : Subgroup G} (hR : R ≤ ι.range)
    {P : GL (Fin 2) L}
    (hRP : R.comap ι = (Matrix.SpecialLinearGroup.map (algebraMap F L)).range.map (conjSL P))
    (h4 : ∃ s : Finset F, s.card = 4) : CFSG.IsQuasisimple R := by
  have hSLinj : Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2)
      (algebraMap F L)) := by
    intro A B h
    ext i j
    have h1 := congrArg (fun X : SL2 L => (X : Matrix (Fin 2) (Fin 2) L) i j) h
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply] at h1
    exact (algebraMap F L).injective h1
  have hPinj : Function.Injective (conjSL P) := fun A B h => by
    have h1 := congrArg (conjSL P⁻¹) h
    rwa [← conjSL_mul, ← conjSL_mul, inv_mul_cancel, conjSL_one, conjSL_one] at h1
  have hmap : (R.comap ι).map ι = R := by
    rw [Subgroup.map_comap_eq]
    exact inf_of_le_right hR
  let e : SL2 F ≃* R :=
    ((((MonoidHom.ofInjective hSLinj).trans (Subgroup.equivMapOfInjective _ _ hPinj)).trans
      (MulEquiv.subgroupCongr hRP.symm)).trans
        (Subgroup.equivMapOfInjective _ _ hι)).trans (MulEquiv.subgroupCongr hmap)
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e (isQuasisimple_SL2 h4)

theorem conjSL_toGL' {L : Type*} [Field L] (B A : SL2 L) :
    conjSL (Matrix.SpecialLinearGroup.toGL B) A = B * A * B⁻¹ := by
  apply Subtype.ext
  rw [coe_conjSL, ← map_inv, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul]

theorem commutator_le_self' {G : Type*} [Group G] (D : Subgroup G) : ⁅D, D⁆ ≤ D :=
  Subgroup.commutator_le.2 fun x hx y hy => by
    rw [commutatorElement_def]
    exact D.mul_mem (D.mul_mem (D.mul_mem hx hy) (D.inv_mem hx)) (D.inv_mem hy)

section Structure

variable {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K K₂ : Type} [Field K] [Field K₂] [Algebra K K₂]
  (hK : Nat.card K = (ℓ ^ f) ^ 3) (hK₂ : Nat.card K₂ = (ℓ ^ f) ^ 6) {σ : K →+* K}
  (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {σ₂ : K₂ ≃+* K₂} (hσ₂ : ∀ c, σ₂ c = c ^ ((ℓ ^ f) ^ 4))
  {τ : K₂ ≃+* K₂} (hτ : ∀ c, τ c = c ^ ((ℓ ^ f) ^ 3))

include hℓ hf hK hK₂ hσ hσ₂ hτ in
theorem qplus_orbit_centralizer_structure
    {g : ModGL TwistTag.D4.tag K₂}
    (hg : g ∈ graphFixedRootGroup TwistTag.D4 K₂ σ₂.toRingHom)
    (hzg : trialityOpposition K₂ = g * (Units.map (entrywiseHom τ.toRingHom) g)⁻¹)
    (hq4 : 4 ≤ ℓ ^ f) {x : ModGL TwistTag.D4.tag K₂}
    {v : WeylGroup TwistTag.D4.tag} (hv : v ∈ relWeylTwist TwistTag.D4)
    (b : Fin TwistTag.D4.foldedTag.rank) {D Q R M : Subgroup (ModGL TwistTag.D4.tag K₂)}
    (hD : D = trialityConjImage K σ g ⊓ Subgroup.centralizer {x})
    (hQ : Q = graphFixedRootPair TwistTag.D4 K₂ σ₂.toRingHom (fixedOrbitImage TwistTag.D4 v b))
    (hR : R = Q ⊓ trialityConjImage K σ g)
    (hM : M = graphFixedRootGroup TwistTag.D4 K₂ σ₂.toRingHom ⊓ Subgroup.centralizer {x})
    (hMeq : M = graphFixedRootTorus TwistTag.D4 K₂ σ₂.toRingHom ⊔ Q)
    (hMset : (M : Set (ModGL TwistTag.D4.tag K₂)) =
      (graphFixedRootTorus TwistTag.D4 K₂ σ₂.toRingHom : Set (ModGL TwistTag.D4.tag K₂)) *
        (Q : Set (ModGL TwistTag.D4.tag K₂))) :
    CFSG.IsQuasisimple R ∧ ⁅D, D⁆ = R ∧
      D ⊓ Subgroup.centralizer (R : Set (ModGL TwistTag.D4.tag K₂)) =
        (Subgroup.center D).map D.subtype ∧
      (Subgroup.center D).map D.subtype ≤
        graphFixedRootTorus TwistTag.D4 K₂ σ₂.toRingHom ⊓ trialityConjImage K σ g := by
  have hσ₂3 := sigma₂_pow_three hℓ hK₂ hσ₂
  obtain ⟨-, -, -, hall⟩ := triality_qplus_quadratic_realization_and_toral_Sylow ℓ f hℓ hf K K₂
    hK hK₂ σ hσ σ₂ hσ₂ τ.toRingHom hτ
  obtain ⟨-, hΓ, -⟩ := hall g hg hzg
  have hΓC : trialityConjImage K σ g ≤ graphFixedRootGroup TwistTag.D4 K₂ σ₂.toRingHom := by
    rw [hΓ]
    exact inf_le_left
  have h4 : ∃ s : Finset (orbitField TwistTag.D4 K₂ σ₂.toRingHom b), s.card = 4 := by
    have : Finite K₂ := Nat.finite_of_card_ne_zero (by
      rw [hK₂]
      exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
    have : Fintype (orbitField TwistTag.D4 K₂ σ₂.toRingHom b) := Fintype.ofFinite _
    have hle : 4 ≤ (Finset.univ : Finset (orbitField TwistTag.D4 K₂ σ₂.toRingHom b)).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, natCard_orbitField_K₂ hℓ hf hK₂ hσ₂ b]
      have hpos : 1 ≤ (TwistTag.D4.orbit b).card := TwistTag.D4.card_orbit_pos b
      calc 4 ≤ ℓ ^ f := hq4
        _ ≤ (ℓ ^ f) ^ 2 := Nat.le_self_pow (by norm_num) _
        _ ≤ ((ℓ ^ f) ^ 2) ^ (TwistTag.D4.orbit b).card := Nat.le_self_pow (by omega) _
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hle
    exact ⟨s, hs⟩
  obtain ⟨-, hMcomm, hMZ, hMZH⟩ := triality_orbitPair_structure σ₂ hσ₂3 hv b h4 M (by
    rw [hMeq, hQ])
  rw [← hQ] at hMcomm hMZ
  obtain ⟨hinj, P, hP, -, hcentP⟩ :=
    exists_fixed_matrix_orbitConjRankOneHom hℓ hf hK hK₂ hσ hσ₂ hτ hg hzg hv b
  obtain ⟨Φ, hΦ⟩ : ∃ Φ, Φ = orbitConjRankOneHom TwistTag.D4 K₂ σ₂.toRingHom v b := ⟨_, rfl⟩
  rw [← hQ, ← hR, ← hΦ] at hP hcentP
  rw [← hΦ] at hinj
  have hrange : Φ.range = Q := by rw [hQ, hΦ]; exact range_orbitConjRankOneHom hv b
  have h4' : ∃ s : Finset (orbitFieldFixed σ₂.toRingHom τ.toRingHom b), s.card = 4 := by
    obtain ⟨hfin, -, -⟩ := orbitFieldFixed_data hℓ hf hK hK₂ hσ₂ hτ σ hσ b
    have : Fintype (orbitFieldFixed σ₂.toRingHom τ.toRingHom b) := Fintype.ofFinite _
    have hle : 4 ≤ (Finset.univ : Finset (orbitFieldFixed σ₂.toRingHom τ.toRingHom b)).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      rcases foldedD4_cases b with rfl | rfl
      · rw [natCard_orbitFieldFixed_zero hℓ hK hK₂ hσ₂ hτ]
        exact hq4.trans (Nat.le_self_pow (by norm_num) _)
      · rw [natCard_orbitFieldFixed_one hℓ hf hK hσ₂ hτ σ hσ]
        exact hq4
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hle
    exact ⟨s, hs⟩
  have hRQ : R ≤ Q := by rw [hR]; exact inf_le_left
  have hquasi : CFSG.IsQuasisimple R :=
    isQuasisimple_of_comap_eq_conjSL hinj (hrange.symm ▸ hRQ) hP h4'
  have hDM : D ≤ M := fun y hy => by
    rw [hD] at hy
    rw [hM]
    exact Subgroup.mem_inf.2 ⟨hΓC (Subgroup.mem_inf.1 hy).1, (Subgroup.mem_inf.1 hy).2⟩
  have hQM : Q ≤ M := by rw [hMeq]; exact le_sup_right
  have hRD : R ≤ D := fun y hy => by
    have hyQ := hQM (hRQ hy)
    rw [hM] at hyQ
    rw [hR] at hy
    rw [hD]
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hy).2, (Subgroup.mem_inf.1 hyQ).2⟩
  have hDΓ : D ≤ trialityConjImage K σ g := by rw [hD]; exact inf_le_left
  have hperf : ⁅R, R⁆ = R := Subgroup.isPerfect_iff.1 hquasi.1
  have hDD : ⁅D, D⁆ = R := by
    refine le_antisymm ?_ (hperf ▸ Subgroup.commutator_mono hRD hRD)
    rw [hR]
    refine le_inf ?_ ((commutator_le_self' D).trans hDΓ)
    rw [← hMcomm]
    exact Subgroup.commutator_mono hDM hDM
  have hkey : ∀ y ∈ D, (∀ r ∈ R, r * y = y * r) →
      y ∈ graphFixedRootTorus TwistTag.D4 K₂ σ₂.toRingHom ∧ ∀ m ∈ M, m * y = y * m := by
    intro y hyD hyR
    have hyM : y ∈ (M : Set (ModGL TwistTag.D4.tag K₂)) := hDM hyD
    rw [hMset] at hyM
    obtain ⟨h, hh, q, hq, hhq⟩ := hyM
    rw [← hrange] at hq
    obtain ⟨B', rfl⟩ := hq
    have hy : y = h * Φ B' := hhq.symm
    have hh0 : h ∈ graphFixedTorus TwistTag.D4 K₂ σ₂.toRingHom := (Subgroup.mem_inf.1 hh).1
    obtain ⟨l, hl⟩ := exists_conj_orbitConjRankOneHom_eq_conjSL hh0 hv b
    rw [← hΦ] at hl
    have hXact : ∀ A, y * Φ A * y⁻¹ =
        Φ (conjSL (diagUnitOne l * Matrix.SpecialLinearGroup.toGL B') A) := fun A => by
      rw [hy, conjSL_mul, conjSL_toGL', ← hl, map_mul, map_mul, map_inv]
      group
    have hXR : diagUnitOne l * Matrix.SpecialLinearGroup.toGL B' ∈
        Subgroup.centralizer (((R.comap Φ).map Matrix.SpecialLinearGroup.toGL :
          Subgroup (GL (Fin 2) (orbitField TwistTag.D4 K₂ σ₂.toRingHom b))) :
            Set (GL (Fin 2) (orbitField TwistTag.D4 K₂ σ₂.toRingHom b))) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨A, hA, rfl⟩
      have h1 : conjSL (diagUnitOne l * Matrix.SpecialLinearGroup.toGL B') A = A := hinj (by
        rw [← hXact, ← hyR (Φ A) hA, mul_inv_cancel_right])
      have h2 := commute_of_conjSL_eq _ h1
      ext1
      rw [Units.val_mul, Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
      exact h2.symm
    rw [hcentP] at hXR
    obtain ⟨u, hu⟩ := hXR
    have hcQ : ∀ A, y * Φ A * y⁻¹ = Φ A := fun A => by
      rw [hXact, ← hu, conjSL_scalar]
    have hyQ : y ∈ M ⊓ Subgroup.centralizer (Q : Set (ModGL TwistTag.D4.tag K₂)) := by
      refine Subgroup.mem_inf.2 ⟨hDM hyD, Subgroup.mem_centralizer_iff.2 fun q hq => ?_⟩
      rw [← hrange] at hq
      obtain ⟨A, rfl⟩ := hq
      exact (mul_inv_eq_iff_eq_mul.1 (hcQ A)).symm
    rw [hMZ] at hyQ
    refine ⟨hMZH hyQ, fun m hm => ?_⟩
    obtain ⟨y', hy'Z, hy'eq⟩ := hyQ
    have h3 := congrArg Subtype.val (Subgroup.mem_center_iff.1 hy'Z ⟨m, hm⟩)
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at h3
    rw [← hy'eq]
    exact h3
  have hcentD : D ⊓ Subgroup.centralizer (R : Set (ModGL TwistTag.D4.tag K₂)) =
      (Subgroup.center D).map D.subtype := by
    refine le_antisymm (fun y hy => ?_) ?_
    · obtain ⟨hyD, hyR⟩ := Subgroup.mem_inf.1 hy
      obtain ⟨-, hyM⟩ := hkey y hyD fun r hr => Subgroup.mem_centralizer_iff.1 hyR r hr
      refine ⟨⟨y, hyD⟩, Subgroup.mem_center_iff.2 fun d => Subtype.ext ?_, rfl⟩
      exact hyM d (hDM d.2)
    · rintro _ ⟨y, hyZ, rfl⟩
      refine Subgroup.mem_inf.2 ⟨y.2, Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hyZ ⟨r, hRD hr⟩)
  refine ⟨hquasi, hDD, hcentD, ?_⟩
  rintro _ ⟨y, hyZ, rfl⟩
  have hyR : ∀ r ∈ R, r * y = y * r := fun r hr =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 hyZ ⟨r, hRD hr⟩)
  exact Subgroup.mem_inf.2 ⟨(hkey y y.2 hyR).1, hDΓ y.2⟩

end Structure

theorem triality_qplus_fixed_root_centralizers
    (ℓ f : ℕ) (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (K K₂ : Type) [Field K] [Field K₂] [Algebra K K₂]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (hK₂ : Nat.card K₂ = (ℓ ^ f) ^ 6)
    (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (σ₂ : K₂ ≃+* K₂) (hσ₂ : ∀ c, σ₂ c = c ^ ((ℓ ^ f) ^ 4))
    (τ : K₂ ≃+* K₂) (hτ : ∀ c, τ c = c ^ ((ℓ ^ f) ^ 3))
    (g : ModGL TwistTag.D4.tag K₂) (hg : g ∈ graphFixedRootGroup TwistTag.D4 K₂ σ₂.toRingHom)
    (hzg : trialityOpposition K₂ = g * (Units.map (entrywiseHom τ.toRingHom) g)⁻¹)
    (p : ℕ) (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ ℓ ^ f + 1) (x : ModGL TwistTag.D4.tag K₂)
    (hx : x ∈ graphFixedRootTorus TwistTag.D4 K₂ σ₂.toRingHom ⊓ trialityConjImage K σ g)
    (hxp : orderOf x = p) :
    (∀ S : Sylow 2 (graphFixedRootTorus TwistTag.D4 K₂ σ₂.toRingHom ⊓ trialityConjImage K σ g :
        Subgroup (ModGL TwistTag.D4.tag K₂)),
      (∀ y y' : S, y * y' = y' * y) ∧ ∃ y y' : S, Subgroup.closure {y, y'} = ⊤) ∧
    (ℓ = 2 → Odd (Nat.card (graphFixedRootTorus TwistTag.D4 K₂ σ₂.toRingHom ⊓
      trialityConjImage K σ g : Subgroup (ModGL TwistTag.D4.tag K₂)))) ∧
    orbitField TwistTag.D4 K₂ σ₂.toRingHom ⟨0, by decide⟩ = ⊤ ∧
    orbitField TwistTag.D4 K₂ σ₂.toRingHom ⟨1, by decide⟩ = trialityFixedField K₂ σ₂.toRingHom ∧
    (orbitFieldFixed σ₂.toRingHom τ.toRingHom ⟨0, by decide⟩).map
        (orbitField TwistTag.D4 K₂ σ₂.toRingHom ⟨0, by decide⟩).subtype =
      (algebraMap K K₂).fieldRange ∧
    Nat.card (orbitFieldFixed σ₂.toRingHom τ.toRingHom ⟨1, by decide⟩) = ℓ ^ f ∧
    ∃ a : Fin TwistTag.D4.tag.rank → K₂ˣ, x = rootDiagUnit TwistTag.D4.tag a ∧
      ((rootCharKernel a = ∅ ∧ trialityConjImage K σ g ⊓ Subgroup.centralizer {x} =
          graphFixedRootTorus TwistTag.D4 K₂ σ₂.toRingHom ⊓ trialityConjImage K σ g) ∨
      ∃ α : Fin TwistTag.D4.tag.rank → ℤ, IsRoot TwistTag.D4.tag α ∧ 0 < height α ∧
        rootCharKernel a = (TwistTag.D4.diagramOrbit α : Set (Fin TwistTag.D4.tag.rank → ℤ)) ∪
          -(TwistTag.D4.diagramOrbit α : Set (Fin TwistTag.D4.tag.rank → ℤ)) ∧
        ∃ D Q R : Subgroup (ModGL TwistTag.D4.tag K₂),
          D = trialityConjImage K σ g ⊓ Subgroup.centralizer {x} ∧
          Q = trialityRootPairFixed σ₂.toRingHom
            (TwistTag.D4.diagramOrbit α : Set (Fin TwistTag.D4.tag.rank → ℤ)) ∧
          R = Q ⊓ trialityConjImage K σ g ∧
          CFSG.IsQuasisimple R ∧ ⁅D, D⁆ = R ∧
          D ⊓ Subgroup.centralizer (R : Set (ModGL TwistTag.D4.tag K₂)) =
            (Subgroup.center D).map D.subtype ∧
          (Subgroup.center D).map D.subtype ≤
            graphFixedRootTorus TwistTag.D4 K₂ σ₂.toRingHom ⊓ trialityConjImage K σ g ∧
          (∀ S : Sylow 2 (Subgroup.center D),
            (∀ y y' : S, y * y' = y' * y) ∧ ∃ y y' : S, Subgroup.closure {y, y'} = ⊤) ∧
          (ℓ = 2 → Odd (Nat.card (Subgroup.center D))) ∧
          ∀ w ∈ relWeylTwist TwistTag.D4, ∀ b : Fin TwistTag.D4.foldedTag.rank,
            fixedOrbitImage TwistTag.D4 w b =
              (TwistTag.D4.diagramOrbit α : Set (Fin TwistTag.D4.tag.rank → ℤ)) →
            Function.Injective (orbitConjRankOneHom TwistTag.D4 K₂ σ₂.toRingHom w b) ∧
            (orbitConjRankOneHom TwistTag.D4 K₂ σ₂.toRingHom w b).range = Q ∧
            ∃ P : GL (Fin 2) (orbitField TwistTag.D4 K₂ σ₂.toRingHom b),
              R.comap (orbitConjRankOneHom TwistTag.D4 K₂ σ₂.toRingHom w b) =
                (Matrix.SpecialLinearGroup.map (algebraMap
                  (orbitFieldFixed σ₂.toRingHom τ.toRingHom b)
                  (orbitField TwistTag.D4 K₂ σ₂.toRingHom b))).range.map (conjSL P) ∧
              (fun A : SL2 (orbitField TwistTag.D4 K₂ σ₂.toRingHom b) =>
                  Matrix.trace
                    (A : Matrix (Fin 2) (Fin 2) (orbitField TwistTag.D4 K₂ σ₂.toRingHom b))) ''
                  (R.comap (orbitConjRankOneHom TwistTag.D4 K₂ σ₂.toRingHom w b) : Set _) =
                Set.range (algebraMap (orbitFieldFixed σ₂.toRingHom τ.toRingHom b)
                  (orbitField TwistTag.D4 K₂ σ₂.toRingHom b)) ∧
              Subgroup.centralizer (((R.comap
                  (orbitConjRankOneHom TwistTag.D4 K₂ σ₂.toRingHom w b)).map
                    Matrix.SpecialLinearGroup.toGL :
                  Subgroup (GL (Fin 2) (orbitField TwistTag.D4 K₂ σ₂.toRingHom b))) :
                    Set (GL (Fin 2) (orbitField TwistTag.D4 K₂ σ₂.toRingHom b))) =
                (Matrix.GeneralLinearGroup.scalar (Fin 2)).range) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K₂ := Nat.finite_of_card_ne_zero (by
    rw [hK₂]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  have hp5 := five_le_of_prime_of_three_lt hp hp3
  have hq4 : 4 ≤ ℓ ^ f := by
    have := Nat.le_of_dvd (by omega) hpq
    omega
  have hσ₂3 := sigma₂_pow_three hℓ hK₂ hσ₂
  have h3 : ∀ c, σ₂ (σ₂ (σ₂ c)) = c := fun c => by
    rw [← ringEquiv_pow_three_apply, hσ₂3]
    rfl
  obtain ⟨-, -, -, hall⟩ := triality_qplus_quadratic_realization_and_toral_Sylow ℓ f hℓ hf K K₂
    hK hK₂ σ hσ σ₂ hσ₂ τ.toRingHom hτ
  obtain ⟨-, hΓ, hTc, -, ⟨eT⟩, -⟩ := hall g hg hzg
  have hΓC : trialityConjImage K σ g ≤ graphFixedRootGroup TwistTag.D4 K₂ σ₂.toRingHom := by
    rw [hΓ]
    exact inf_le_left
  obtain ⟨-, ⟨e, he⟩, hL0, hL1, -, -, -, -, -⟩ :=
    triality_all_characteristic_faithful_torus_coordinates K₂ σ₂ hσ₂3
  have hTsyl : ∀ (G : Type) [Group G] (φ : G →* (graphFixedRootTorus TwistTag.D4 K₂ σ₂.toRingHom ⊓
      trialityConjImage K σ g : Subgroup (ModGL TwistTag.D4.tag K₂))),
      Function.Injective φ → (∀ y y' : G, y * y' = y' * y) ∧
        ∃ y y' : G, Subgroup.closure {y, y'} = ⊤ := fun G _ φ hφ =>
    comm_and_two_generated_of_injective_prod (eT.toMonoidHom.comp φ) (eT.injective.comp hφ)
  have hTodd : ℓ = 2 → Odd (Nat.card (graphFixedRootTorus TwistTag.D4 K₂ σ₂.toRingHom ⊓
      trialityConjImage K σ g : Subgroup (ModGL TwistTag.D4.tag K₂))) := by
    intro h2
    have hev : Even (ℓ ^ f) := by
      rw [h2]
      exact (Nat.even_pow' (by omega)).2 even_two
    rw [Nat.card_congr eT.toEquiv, Nat.card_prod, natCard_multiplicative_zmod,
      natCard_multiplicative_zmod]
    exact Odd.mul (Even.add_one (hev.pow_of_ne_zero (by norm_num))) (Even.add_one hev)
  obtain ⟨α, β, -, -, hxαβ⟩ := (hTc x).1 hx
  have hxe : x = (e (α, β) : ModGL TwistTag.D4.tag K₂) := by rw [hxαβ, he]
  have hxp1 : x ^ p = 1 := by rw [← hxp]; exact pow_orderOf_eq_one x
  have hαβp : (α, β) ^ p = 1 := by
    have h1 : e ((α, β) ^ p) = 1 := Subtype.ext (by
      rw [map_pow, Subgroup.coe_pow, ← hxe, hxp1]
      rfl)
    exact (map_eq_one_iff e e.injective).1 h1
  have hαp : α ^ p = 1 := congrArg Prod.fst hαβp
  have hβp : β ^ p = 1 := congrArg Prod.snd hαβp
  have hp4 : p ∣ (ℓ ^ f) ^ 4 - 1 := hpq.trans (dvd_of_int_eq_mul
    ((((ℓ ^ f : ℕ) : ℤ) - 1) * (((ℓ ^ f : ℕ) : ℤ) ^ 2 + 1)) (by
      push_cast [Nat.cast_sub (Nat.one_le_pow 4 _ hq1)]
      ring))
  have hα4 : α ^ ((ℓ ^ f) ^ 4) = α := by
    obtain ⟨m, hm⟩ := hp4
    have h4 : (ℓ ^ f) ^ 4 = p * m + 1 := by
      have := Nat.one_le_pow 4 _ hq1
      omega
    rw [h4, pow_succ, pow_mul, hαp, one_pow, one_mul]
  have hσα : Units.map σ₂.toRingHom.toMonoidHom α = α := Units.ext (by
    change σ₂ (α : K₂) = α
    rw [hσ₂, ← Units.val_pow_eq_pow_val, hα4])
  obtain ⟨A, hA⟩ : ∃ A : K₂ˣ, A = α ^ 2 * (trialityFixedUnit K₂ σ₂ β)⁻¹ := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : K₂ˣ, B = (α * α * α)⁻¹ * trialityFixedUnit K₂ σ₂ β ^ 2 := ⟨_, rfl⟩
  have hxa : x = rootDiagUnit TwistTag.D4.tag (d4Tuple A A B A) := by
    rw [hxαβ, trialityOuter_mul_middle_eq]
    simp only [hσα, hA, hB]
  have hbUp : trialityFixedUnit K₂ σ₂ β ^ p = 1 := by rw [← map_pow, hβp, map_one]
  have hAp : A ^ p = 1 := by
    rw [hA, mul_pow, inv_pow, ← pow_mul, mul_comm 2 p, pow_mul, hαp, hbUp, one_pow, inv_one,
      mul_one]
  have hBp : B ^ p = 1 := by
    rw [hB, mul_pow, inv_pow, mul_pow, mul_pow, hαp, ← pow_mul, mul_comm 2 p, pow_mul, hbUp,
      one_pow]
    simp
  have hAB : ¬(A = 1 ∧ B = 1) := by
    rintro ⟨hA1, hB1⟩
    have hx1 : x = 1 := by
      rw [hxa, hA1, hB1]
      convert rootDiagUnit_one (τ := TwistTag.D4.tag) (K := K₂) using 2
      exact vec4_one
    rw [hx1, orderOf_one] at hxp
    omega
  have hcases := triality_toral_centralizer_cases σ₂ (a := d4Tuple A A B A) rfl rfl rfl rfl hp hp3
    hAp hBp hAB
  rw [← hxa] at hcases
  refine ⟨fun S => hTsyl S S.toSubgroup.subtype S.toSubgroup.subtype_injective, hTodd, hL0, hL1,
    map_orbitFieldFixed_zero hℓ hK hK₂ hσ₂ hτ, natCard_orbitFieldFixed_one hℓ hf hK hσ₂ hτ σ hσ,
    d4Tuple A A B A, hxa, ?_⟩
  have hxtor : x ∈ torusGroup TwistTag.D4.tag K₂ :=
    graphFixedRootTorus_le_torusGroup _ (Subgroup.mem_inf.1 hx).1
  rcases hcases with ⟨hker, hcent⟩ | ⟨v, hv, b, hker, hOpos, hMeq, hMset⟩
  ·
    refine Or.inl ⟨hker, le_antisymm (fun y hy => ?_) (fun y hy => ?_)⟩
    · obtain ⟨hyΓ, hyc⟩ := Subgroup.mem_inf.1 hy
      have hyH : y ∈ graphFixedRootTorus TwistTag.D4 K₂ σ₂.toRingHom := by
        rw [← hcent]
        exact Subgroup.mem_inf.2 ⟨hΓC hyΓ, hyc⟩
      exact Subgroup.mem_inf.2 ⟨hyH, hyΓ⟩
    · obtain ⟨hyH, hyΓ⟩ := Subgroup.mem_inf.1 hy
      refine Subgroup.mem_inf.2 ⟨hyΓ, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      exact commute_of_mem_torusGroup (graphFixedRootTorus_le_torusGroup _ hyH) hxtor
  right
  obtain ⟨α₀, hα₀⟩ : ∃ α₀ : Fin TwistTag.D4.tag.rank → ℤ,
      α₀ = v • (Pi.single (TwistTag.D4.orbitMin b) 1 : Fin TwistTag.D4.tag.rank → ℤ) := ⟨_, rfl⟩
  have hα₀O : α₀ ∈ fixedOrbitImage TwistTag.D4 v b := ⟨_, TwistTag.D4.orbitMin_mem b, hα₀.symm⟩
  have hOset : (TwistTag.D4.diagramOrbit α₀ : Set (Fin TwistTag.D4.tag.rank → ℤ)) =
      fixedOrbitImage TwistTag.D4 v b := by
    rw [hα₀, TwistTag.D4.diagramOrbit_smul_single hv, TwistTag.D4.orbitIndex_orbitMin,
      Finset.coe_image]
    rfl
  have hpar : ringChar K₂ = 2 ∨ ∃ n, Odd n ∧ ∀ c, σ₂ c = c ^ n := by
    have : CharP K₂ ℓ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ
        (k := f * 6) (by omega) (by rw [hK₂, pow_mul])
    rcases hℓ.eq_two_or_odd' with h2 | hodd
    · exact Or.inl (by rw [ringChar.eq K₂ ℓ, h2])
    · exact Or.inr ⟨(ℓ ^ f) ^ 4, hodd.pow.pow, hσ₂⟩
  have hΓeq := twistedFixedGroup_eq_graphFixedRootGroup_triality σ₂ h3 hpar
  have hQeq : ∀ O : Set (Fin TwistTag.D4.tag.rank → ℤ),
      trialityRootPairFixed σ₂.toRingHom O = graphFixedRootPair TwistTag.D4 K₂ σ₂.toRingHom O :=
    fun O => by rw [trialityRootPairFixed, graphFixedRootPair, hΓeq]
  have hQO : trialityRootPairFixed σ₂.toRingHom
      (TwistTag.D4.diagramOrbit α₀ : Set (Fin TwistTag.D4.tag.rank → ℤ)) =
        graphFixedRootPair TwistTag.D4 K₂ σ₂.toRingHom (fixedOrbitImage TwistTag.D4 v b) := by
    rw [hOset, hQeq]
  rw [← hQO] at hMeq hMset
  obtain ⟨hquasi, hDD, hcentD, hZT⟩ := qplus_orbit_centralizer_structure hℓ hf hK hK₂ hσ hσ₂ hτ
    hg hzg hq4 hv b rfl hQO rfl rfl hMeq hMset
  obtain ⟨D, hD⟩ : ∃ D, D = trialityConjImage K σ g ⊓ Subgroup.centralizer {x} := ⟨_, rfl⟩
  rw [← hD] at hDD hcentD hZT
  let ιZ : Subgroup.center D →* (graphFixedRootTorus TwistTag.D4 K₂ σ₂.toRingHom ⊓
      trialityConjImage K σ g : Subgroup (ModGL TwistTag.D4.tag K₂)) :=
    MonoidHom.codRestrict (D.subtype.comp (Subgroup.center D).subtype) _
      (fun y => hZT ⟨y, y.2, rfl⟩)
  have hιZ : Function.Injective ιZ := fun y y' h => by
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  refine ⟨α₀, by rw [hα₀]; exact IsRoot.smul (isRoot_single _ _) v, hOpos α₀ hα₀O,
    by rw [hOset]; exact hker, D, _, _, hD, rfl, rfl, hquasi, hDD, hcentD, hZT,
    fun S => hTsyl S (ιZ.comp S.toSubgroup.subtype) (hιZ.comp S.toSubgroup.subtype_injective),
    fun hℓ2 => ?_,
    fun w hw b' hO => ?_⟩
  · have hdvd : Nat.card (Subgroup.center D) ∣
        Nat.card (graphFixedRootTorus TwistTag.D4 K₂ σ₂.toRingHom ⊓ trialityConjImage K σ g :
          Subgroup (ModGL TwistTag.D4.tag K₂)) := by
      rw [← Subgroup.card_map_of_injective D.subtype_injective]
      exact Subgroup.card_dvd_of_le hZT
    exact Odd.of_dvd_nat (hTodd hℓ2) hdvd
  · have hQO' : trialityRootPairFixed σ₂.toRingHom
        (TwistTag.D4.diagramOrbit α₀ : Set (Fin TwistTag.D4.tag.rank → ℤ)) =
          graphFixedRootPair TwistTag.D4 K₂ σ₂.toRingHom (fixedOrbitImage TwistTag.D4 w b') := by
      rw [← hO, hQeq]
    obtain ⟨hinj', P', hP', htr', hcent'⟩ :=
      exists_fixed_matrix_orbitConjRankOneHom hℓ hf hK hK₂ hσ hσ₂ hτ hg hzg hw b'
    rw [← hQO'] at hP' htr' hcent'
    exact ⟨hinj', by rw [hQO']; exact range_orbitConjRankOneHom hw b', P', hP', htr', hcent'⟩

end CFSG.RankThree.Chevalley
