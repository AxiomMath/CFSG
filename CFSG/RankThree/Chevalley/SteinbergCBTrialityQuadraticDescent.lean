module

public import CFSG.RankThree.Chevalley.SteinbergCBTrialityOpposition
public import CFSG.LieType.Chevalley.TrialityFullAmbientFixedGroup
public import CFSG.LieType.Chevalley.DiagramCoordinateFixedStructure
public import CFSG.LieType.AlgebraicGroups.AllCharacteristicLang
public import CFSG.GroupTheory.LangNormOneDescent
public import CFSG.LieType.Chevalley.GraphFixedF4GroupDescent
public import Certificates.Certificate45
public import Certificates.Certificate113
public import Certificates.Certificate46
public import Certificates.Certificate114
public import Certificates.Certificate47
public import Certificates.Certificate117
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import CFSG.GroupTheory.LocalCores.Fitting

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.GroupTheory

theorem units_map_entrywiseHom_ringHom_id {τ : Tag} {L : Type} [Field L] (g : ModGL τ L) :
    Units.map (entrywiseHom (RingHom.id L)) g = g :=
  Units.ext (entrywise_id _)

theorem twistHom_eq_units_map_of_fixed {L : Type} [Field L] {σ₂ fr τ : L →+* L}
    (hc : fr.comp σ₂ = σ₂.comp fr) (h6 : (fr.comp fr).comp σ₂ = RingHom.id L)
    (hτ : τ = (fr.comp fr).comp fr) {g : ModGL TwistTag.D4.tag L}
    (hg : twistHom TwistTag.D4 L σ₂ g = g) :
    twistHom TwistTag.D4 L fr g = Units.map (entrywiseHom τ) g := by
  have hA : twistHom TwistTag.D4 L σ₂ (Units.map (entrywiseHom fr) g) =
      Units.map (entrywiseHom fr) g := by
    have h := congrArg (Units.map (entrywiseHom fr)) hg
    rw [twistHom_apply, map_mul, map_mul, map_inv, units_map_entrywiseHom_diagramMap,
      units_map_entrywiseHom_comp, hc, ← units_map_entrywiseHom_comp] at h
    rw [twistHom_apply]
    exact h
  have h2 := congrArg (Units.map (entrywiseHom (fr.comp fr))) hA
  rw [twistHom_apply, map_mul, map_mul, map_inv, units_map_entrywiseHom_diagramMap,
    units_map_entrywiseHom_comp, h6, units_map_entrywiseHom_ringHom_id,
    units_map_entrywiseHom_comp] at h2
  rw [twistHom_apply, h2, hτ]

theorem ringHom_comp_apply_pow {L : Type} [CommRing L] {φ ψ : L →+* L} {a b : ℕ}
    (hφ : ∀ c, φ c = c ^ a) (hψ : ∀ c, ψ c = c ^ b) (c : L) : (φ.comp ψ) c = c ^ (b * a) := by
  rw [RingHom.comp_apply, hφ, hψ, ← pow_mul]

section Finite

variable {ℓ f : ℕ} {K₂ : Type} [Field K₂]

theorem pow_q_six_eq (hK₂ : Nat.card K₂ = (ℓ ^ f) ^ 6) (hℓ : ℓ.Prime) (c : K₂) :
    c ^ ((ℓ ^ f) ^ 6) = c := by
  have : Finite K₂ := Nat.finite_of_card_ne_zero (by
    rw [hK₂]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Fintype K₂ := Fintype.ofFinite K₂
  rw [← hK₂, Nat.card_eq_fintype_card, FiniteField.pow_card]

end Finite

theorem graphFixedRootGroup_inf_eqLocus_eq
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (K K₂ : Type) [Field K] [Field K₂] [Algebra K K₂]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (hK₂ : Nat.card K₂ = (ℓ ^ f) ^ 6)
    (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (σ₂ : K₂ →+* K₂) (hσ₂ : ∀ c, σ₂ c = c ^ ((ℓ ^ f) ^ 4))
    (τ : K₂ →+* K₂) (hτ : ∀ c, τ c = c ^ ((ℓ ^ f) ^ 3)) :
    graphFixedRootGroup TwistTag.D4 K₂ σ₂ ⊓
        (Units.map (entrywiseHom τ)).eqLocus (MonoidHom.id _) =
      (graphFixedRootGroup TwistTag.D4 K σ).map (baseChangeGL (algebraMap K K₂)) := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Fintype K := Fintype.ofFinite K
  have : Finite K₂ := Nat.finite_of_card_ne_zero (by
    rw [hK₂]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ
      (k := f * 3) (by omega) (by rw [hK, pow_mul])
  have hq6 := pow_q_six_eq hK₂ hℓ
  set ι := algebraMap K K₂
  have : CharP K₂ ℓ := charP_of_injective_algebraMap ι.injective ℓ
  set frH : K₂ →+* K₂ := iterateFrobenius K₂ ℓ f
  have hfr : ∀ c, frH c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  set q := ℓ ^ f with hqdef
  clear_value q
  have hq3 : ∀ c : K, c ^ (q ^ 3) = c := fun c => by
    rw [← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  set σE : K ≃+* K := RingEquiv.ofBijective σ ⟨σ.injective,
    Finite.surjective_of_injective σ.injective⟩
  have hσE : σE.toRingHom = σ := RingHom.ext fun _ => rfl
  set frE : K₂ ≃+* K₂ := RingEquiv.ofBijective frH ⟨frH.injective,
    Finite.surjective_of_injective frH.injective⟩
  have hfrE : frE.toRingHom = frH := RingHom.ext fun _ => rfl
  have hσ3 : ∀ c, σE (σE (σE c)) = c := fun c => by
    change σ (σ (σ c)) = c
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul, show q * (q * q) = q ^ 3 by ring, hq3]
  have hpar : ringChar K = 2 ∨ ∃ n, Odd n ∧ ∀ c, σE c = c ^ n := by
    rcases hℓ.eq_two_or_odd' with h2 | hodd
    · exact Or.inl (by rw [ringChar.eq K ℓ, h2])
    · exact Or.inr ⟨q, by rw [hqdef]; exact hodd.pow, hσ⟩
  have hΓ := twistedFixedGroup_D4_eq_map_baseChangeGL (ι := ι) (σ := σE) (ψ := frE)
    (fun l hl => rootDiagUnit_mem_graphFixedRootGroup_triality σE hσ3 hpar hl)
    (fun c => by
      change frH (ι c) = ι (σ c)
      rw [hfr, hσ, map_pow])
    (fun c hc => by
      refine mem_range_algebraMap_of_pow_card_eq ?_
      change frH (frH (frH c)) = c at hc
      rw [hfr, hfr, hfr, ← pow_mul, ← pow_mul] at hc
      rw [hK, show q ^ 3 = q * (q * q) by ring]
      exact hc)
  rw [hfrE, hσE] at hΓ
  have hFτ : ∀ g, twistHom TwistTag.D4 K₂ σ₂ g = g →
      twistHom TwistTag.D4 K₂ frH g = Units.map (entrywiseHom τ) g := fun g hg =>
    twistHom_eq_units_map_of_fixed
      (RingHom.ext fun c => by
        rw [ringHom_comp_apply_pow hfr hσ₂, ringHom_comp_apply_pow hσ₂ hfr, mul_comm])
      (RingHom.ext fun c => by
        rw [ringHom_comp_apply_pow (ringHom_comp_apply_pow hfr hfr) hσ₂,
          show q ^ 4 * (q * q) = q ^ 6 by ring, hq6, RingHom.id_apply])
      (RingHom.ext fun c => by
        rw [ringHom_comp_apply_pow (ringHom_comp_apply_pow hfr hfr) hfr, hτ,
          show q * (q * q) = q ^ 3 by ring]) hg
  have hle : (graphFixedRootGroup TwistTag.D4 K σ).map (baseChangeGL ι) ≤
      graphFixedRootGroup TwistTag.D4 K₂ σ₂ :=
    map_baseChangeGL_graphFixedRootGroup_le (Finite.surjective_of_injective σ.injective)
      fun c => by rw [hσ₂, hσ, ← map_pow, show q ^ 4 = q ^ 3 * q by ring, pow_mul, hq3]
  have hτι : τ.comp ι = ι := RingHom.ext fun c => by
    rw [RingHom.comp_apply, hτ, ← map_pow, hq3]
  refine le_antisymm (fun g hg => ?_) (fun g hg => ?_)
  · obtain ⟨hgC, hgτ⟩ := Subgroup.mem_inf.1 hg
    have hgτ' : Units.map (entrywiseHom τ) g = g := hgτ
    have hgΓ := graphFixedRootGroup_le TwistTag.D4 K₂ σ₂ hgC
    rw [mem_twistedFixedGroup_iff_twistHom] at hgΓ
    have hgF : g ∈ twistedFixedGroup TwistTag.D4 K₂ frH :=
      (mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨hgΓ.1, by rw [hFτ g hgΓ.2, hgτ']⟩
    rw [hΓ] at hgF
    exact hgF
  · refine Subgroup.mem_inf.2 ⟨hle hg, ?_⟩
    obtain ⟨x, -, rfl⟩ := hg
    change Units.map (entrywiseHom τ) (baseChangeGL ι x) = baseChangeGL ι x
    rw [units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL, hτι]

theorem exists_eq_mul_inv_entrywise_trialityOpposition
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (K₂ : Type) [Field K₂] (hK₂ : Nat.card K₂ = (ℓ ^ f) ^ 6) (σ₂ : K₂ →+* K₂)
    (hσ₂ : ∀ c, σ₂ c = c ^ ((ℓ ^ f) ^ 4)) (τ : K₂ →+* K₂) (hτ : ∀ c, τ c = c ^ ((ℓ ^ f) ^ 3)) :
    ∃ g ∈ graphFixedRootGroup TwistTag.D4 K₂ σ₂,
      trialityOpposition K₂ = g * (Units.map (entrywiseHom τ) g)⁻¹ := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K₂ ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ
      (k := f * 6) (by omega) (by rw [hK₂, pow_mul])
  have hq6 := pow_q_six_eq hK₂ hℓ
  set Ω := AlgebraicClosure K₂
  set ι := algebraMap K₂ Ω
  have : CharP Ω ℓ := charP_of_injective_algebraMap ι.injective ℓ
  obtain ⟨S, hS, hLang⟩ :=
    (exceptional_all_characteristic_field_Lang_surjectivity ℓ Ω f hf).2 TwistTag.D4 1
  set Fr := iterateFrobenius Ω ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  set frH : K₂ →+* K₂ := iterateFrobenius K₂ ℓ f
  have hfr : ∀ c, frH c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFr2 : ∀ c, (Fr.comp Fr) c = c ^ (ℓ ^ (2 * f)) := fun c => by
    rw [RingHom.comp_apply, hFr, hFr, ← pow_mul, ← pow_add, two_mul]
  have hK₂' : Nat.card K₂ = (ℓ ^ (2 * f)) ^ 3 := by
    rw [hK₂]
    ring
  have hσ₂' : ∀ c, σ₂ c = c ^ ((ℓ ^ (2 * f)) ^ 2) := fun c => by
    rw [hσ₂]
    congr 1
    ring
  set q := ℓ ^ f with hqdef
  clear_value q
  have hS' : ∀ g', (S g' : ModGL TwistTag.D4.tag Ω) =
      twistHom TwistTag.D4 Ω Fr (g' : ModGL TwistTag.D4.tag Ω) := fun g' => by
    rw [hS, zpow_one, twistHom_apply]
  have hzΓ := graphFixedRootGroup_le TwistTag.D4 Ω (RingHom.id Ω)
    (trialityOpposition_mem_graphFixedRootGroup (K := Ω) (RingHom.id Ω))
  rw [mem_twistedFixedGroup_iff_twistHom] at hzΓ
  set x : adjointGroup TwistTag.D4.tag Ω := ⟨trialityOpposition Ω, hzΓ.1⟩
  have hSx : S x = x := Subtype.ext (by
    rw [hS']
    change twistHom TwistTag.D4 Ω Fr (trialityOpposition Ω) = trialityOpposition Ω
    rw [twistHom_apply, units_map_entrywiseHom_trialityOpposition]
    have h := hzΓ.2
    rwa [twistHom_apply, units_map_entrywiseHom_ringHom_id] at h)
  have hxS : x * S x = 1 := by
    rw [hSx]
    exact Subtype.ext (by
      rw [Subgroup.coe_mul, ← pow_two]
      exact trialityOpposition_sq)
  have hnorm : ((List.range 2).map fun i => (⇑S.toMonoidHom)^[i] x).prod = 1 := by
    simpa [List.range_succ] using hxS
  obtain ⟨h, hR, hxh, -⟩ := exceptional_Lang_norm_one_descent S.toMonoidHom (m := 2)
    (by norm_num) hLang x hnorm
  have hSh : S (S h) = h := hR
  obtain ⟨-, hGS, -⟩ := triality_both_field_orientations_simple_full_ambient_fixed_group ℓ (2 * f)
    hℓ (by omega) K₂ hK₂' Ω 2 (Or.inr rfl) σ₂ hσ₂' (Fr.comp Fr) hFr2
  have e1 : ((S (S h) : adjointGroup TwistTag.D4.tag Ω) : ModGL TwistTag.D4.tag Ω) =
      twistHom TwistTag.D4 Ω Fr (twistHom TwistTag.D4 Ω Fr (h : ModGL TwistTag.D4.tag Ω)) := by
    rw [hS', hS']
  have e2 : twistHom TwistTag.D4 Ω Fr (twistHom TwistTag.D4 Ω Fr (h : ModGL TwistTag.D4.tag Ω)) =
      diagramMap TwistTag.D4 Ω ^ 2 *
        Units.map (entrywiseHom (Fr.comp Fr)) (h : ModGL TwistTag.D4.tag Ω) *
          (diagramMap TwistTag.D4 Ω ^ 2)⁻¹ := by
    rw [twistHom_apply, twistHom_apply, map_mul, map_mul, map_inv,
      units_map_entrywiseHom_diagramMap, units_map_entrywiseHom_comp, sq]
    group
  have hP2 : diagramMap TwistTag.D4 Ω ^ 2 *
      Units.map (entrywiseHom (Fr.comp Fr)) (h : ModGL TwistTag.D4.tag Ω) *
        (diagramMap TwistTag.D4 Ω ^ 2)⁻¹ = h := by
    rw [← e2, ← e1, hSh]
  have hmem : (h : ModGL TwistTag.D4.tag Ω) ∈ ((graphFixedRootGroup TwistTag.D4 K₂ σ₂).map
      (baseChangeGL ι) : Set (ModGL TwistTag.D4.tag Ω)) := by
    rw [← hGS]
    exact ⟨h.2, hP2⟩
  obtain ⟨h₂, hh₂, hh₂e⟩ := hmem
  have hFτ : twistHom TwistTag.D4 K₂ frH h₂ = Units.map (entrywiseHom τ) h₂ :=
    twistHom_eq_units_map_of_fixed
      (RingHom.ext fun c => by
        rw [ringHom_comp_apply_pow hfr hσ₂, ringHom_comp_apply_pow hσ₂ hfr, mul_comm])
      (RingHom.ext fun c => by
        rw [ringHom_comp_apply_pow (ringHom_comp_apply_pow hfr hfr) hσ₂,
          show q ^ 4 * (q * q) = q ^ 6 by ring, hq6, RingHom.id_apply])
      (RingHom.ext fun c => by
        rw [ringHom_comp_apply_pow (ringHom_comp_apply_pow hfr hfr) hfr, hτ,
          show q * (q * q) = q ^ 3 by ring])
      ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 (graphFixedRootGroup_le _ _ _ hh₂)).2
  have hcomm : ι.comp frH = Fr.comp ι := RingHom.ext fun c => by
    rw [RingHom.comp_apply, RingHom.comp_apply, hfr, hFr, map_pow]
  have hSh₂ : (S h : ModGL TwistTag.D4.tag Ω) = baseChangeGL ι (Units.map (entrywiseHom τ) h₂) := by
    rw [hS', ← hh₂e, twistHom_baseChangeGL ι hcomm, hFτ]
  have hz : baseChangeGL ι (trialityOpposition K₂) =
      baseChangeGL ι (h₂⁻¹ * Units.map (entrywiseHom τ) h₂) := by
    rw [baseChangeGL_trialityOpposition, map_mul, map_inv, ← hSh₂, hh₂e]
    have e := congrArg (fun y : adjointGroup TwistTag.D4.tag Ω => (y : ModGL TwistTag.D4.tag Ω))
      hxh
    simpa using e
  refine ⟨h₂⁻¹, inv_mem hh₂, ?_⟩
  rw [baseChangeGL_injective ι hz, map_inv, inv_inv]

theorem map_conj_eq_inf_eqLocus {G : Type*} [Group G] {C₂ C : Subgroup G} {τ : G →* G}
    (hC : C₂ ⊓ τ.eqLocus (MonoidHom.id G) = C) {g z : G} (hg : g ∈ C₂) (hz : z = g * (τ g)⁻¹) :
    C.map (MulAut.conj g).toMonoidHom =
      C₂ ⊓ ((MulAut.conj z).toMonoidHom.comp τ).eqLocus (MonoidHom.id G) := by
  have hzg : z * τ g = g := by rw [hz, inv_mul_cancel_right]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← hC] at hy
    obtain ⟨hyC, hyτ⟩ := Subgroup.mem_inf.1 hy
    have hyτ' : τ y = y := hyτ
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact mul_mem (mul_mem hg hyC) (inv_mem hg)
    · change z * τ ((MulAut.conj g) y) * z⁻¹ = (MulAut.conj g) y
      rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hyτ']
      calc z * (τ g * y * (τ g)⁻¹) * z⁻¹ = (z * τ g) * y * (z * τ g)⁻¹ := by group
        _ = g * y * g⁻¹ := by rw [hzg]
  · intro hx
    obtain ⟨hxC, hxF⟩ := Subgroup.mem_inf.1 hx
    have hxF' : z * τ x * z⁻¹ = x := hxF
    have hτx : τ x = z⁻¹ * x * z := by
      calc τ x = z⁻¹ * (z * τ x * z⁻¹) * z := by group
        _ = z⁻¹ * x * z := by rw [hxF']
    have hτg : τ g = z⁻¹ * g := by
      calc τ g = z⁻¹ * (z * τ g) := by group
        _ = z⁻¹ * g := by rw [hzg]
    have hy : g⁻¹ * x * g ∈ C := by
      rw [← hC]
      refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem (inv_mem hg) hxC) hg, ?_⟩
      change τ (g⁻¹ * x * g) = g⁻¹ * x * g
      rw [map_mul, map_mul, map_inv, hτx, hτg]
      group
    refine ⟨_, hy, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

end CFSG.RankThree.Chevalley
