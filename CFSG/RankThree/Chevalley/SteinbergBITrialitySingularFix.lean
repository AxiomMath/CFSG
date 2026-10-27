module

public import CFSG.RankThree.Chevalley.SteinbergBID4RootSL2Trace
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.Chevalley.SteinbergBID4A2CharCentralizer
public import CFSG.RankThree.Chevalley.SteinbergCDTrialityThreeSixSylow

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix Pointwise

variable (Ω : Type) [Field Ω]

@[expose] def tsQv
    (v : WeylGroup Tag.D4) : Subgroup (ModGL TwistTag.D4.tag Ω) := d4A2Qv Ω v

@[expose] def tsIota
    (A : Matrix.SpecialLinearGroup (Fin 2) Ω) : ModGL TwistTag.D4.tag Ω :=
  ((d4A2Iota Ω A : subsystemGroup Tag.D4 Ω d4SuppA2) : ModGL Tag.D4 Ω)

variable (K : Type) [Field K] [Algebra K Ω] (σ : K ≃+* K)

@[expose] def threeSixSingularR
    (Fr : Ω →+* Ω) (ε : ℤ) (v : WeylGroup Tag.D4)
    (g : ModGL TwistTag.D4.tag Ω) : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
  ((tsQv Ω v ⊓ (threeSixFrob Ω Fr ε).eqLocus (MonoidHom.id _)).map
    (MulAut.conj g).toMonoidHom).comap (threeSixEmb K Ω σ)

section Fixed

variable {Ω K σ}

theorem range_threeSixEmb
    [IsAlgClosure K Ω] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (Fr : Ω →+* Ω)
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) :
    (threeSixEmb K Ω σ).range =
      adjointGroup TwistTag.D4.tag Ω ⊓ (trialityFrob Ω Fr).eqLocus (MonoidHom.id _) := by
  obtain ⟨-, hfix, -, -, -⟩ := triality_both_field_orientations_simple_full_ambient_fixed_group ℓ f
    hℓ hf K hK Ω 1 (Or.inl rfl) σ.toRingHom (fun c => by rw [pow_one]; exact hσ c) Fr hFr
  rw [threeSixEmb, MonoidHom.range_comp, Subgroup.range_subtype]
  refine SetLike.coe_injective ?_
  rw [← hfix]
  ext x
  simp only [pow_one, Set.mem_ofPred_eq, SetLike.mem_coe, Subgroup.mem_inf]
  rfl

theorem trialityFrob_conj
    {Fr : Ω →+* Ω} {ε : ℤ} {g : ModGL TwistTag.D4.tag Ω}
    (hFg : trialityFrob Ω Fr g = g * threeSixN Ω ε) (u : ModGL TwistTag.D4.tag Ω) :
    trialityFrob Ω Fr (g * u * g⁻¹) = g * threeSixFrob Ω Fr ε u * g⁻¹ := by
  rw [map_mul, map_mul, map_inv, hFg, threeSixFrob_apply]
  group

variable (Ω K σ) in
@[expose] def threeSixEmb'
    (g : ModGL TwistTag.D4.tag Ω) :
    graphFixedRootGroup TwistTag.D4 K σ.toRingHom →* ModGL TwistTag.D4.tag Ω :=
  (MulAut.conj g⁻¹).toMonoidHom.comp (threeSixEmb K Ω σ)

theorem threeSixEmb'_apply
    (g : ModGL TwistTag.D4.tag Ω)
    (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    threeSixEmb' Ω K σ g y = g⁻¹ * threeSixEmb K Ω σ y * g := by
  rw [threeSixEmb', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]

theorem threeSixEmb'_injective
    (g : ModGL TwistTag.D4.tag Ω) :
    Function.Injective (threeSixEmb' Ω K σ g) :=
  (MulAut.conj g⁻¹).injective.comp
    ((baseChangeGL_injective (τ := TwistTag.D4.tag) (algebraMap K Ω)).comp Subtype.val_injective)

theorem mem_range_threeSixEmb'
    {Fr : Ω →+* Ω} {ε : ℤ} {g : ModGL TwistTag.D4.tag Ω}
    (hrange : (threeSixEmb K Ω σ).range =
      adjointGroup TwistTag.D4.tag Ω ⊓ (trialityFrob Ω Fr).eqLocus (MonoidHom.id _))
    (hgG : g ∈ adjointGroup TwistTag.D4.tag Ω) (hFg : trialityFrob Ω Fr g = g * threeSixN Ω ε)
    (u : ModGL TwistTag.D4.tag Ω) :
    u ∈ (threeSixEmb' Ω K σ g).range ↔
      u ∈ adjointGroup TwistTag.D4.tag Ω ∧ threeSixFrob Ω Fr ε u = u := by
  have key : ∀ u, g * u * g⁻¹ ∈ (threeSixEmb K Ω σ).range ↔
      u ∈ adjointGroup TwistTag.D4.tag Ω ∧ threeSixFrob Ω Fr ε u = u := fun u => by
    rw [hrange, Subgroup.mem_inf]
    change _ ∧ trialityFrob Ω Fr (g * u * g⁻¹) = g * u * g⁻¹ ↔ _
    rw [trialityFrob_conj hFg]
    constructor
    · rintro ⟨hG, hF⟩
      refine ⟨?_, by simpa using hF⟩
      have := mul_mem (mul_mem (inv_mem hgG) hG) hgG
      simpa [mul_assoc] using this
    · rintro ⟨hG, hF⟩
      exact ⟨mul_mem (mul_mem hgG hG) (inv_mem hgG), by rw [hF]⟩
  rw [← key]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, by rw [threeSixEmb'_apply]; group⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, by rw [threeSixEmb'_apply, hy]; group⟩

theorem threeSixSingularR_eq_comap
    {Fr : Ω →+* Ω} {ε : ℤ} {g : ModGL TwistTag.D4.tag Ω}
    (hrange : (threeSixEmb K Ω σ).range =
      adjointGroup TwistTag.D4.tag Ω ⊓ (trialityFrob Ω Fr).eqLocus (MonoidHom.id _))
    (hgG : g ∈ adjointGroup TwistTag.D4.tag Ω) (hFg : trialityFrob Ω Fr g = g * threeSixN Ω ε)
    (v : WeylGroup Tag.D4) :
    threeSixSingularR Ω K σ Fr ε v g = (tsQv Ω v).comap (threeSixEmb' Ω K σ g) := by
  ext y
  rw [threeSixSingularR, Subgroup.mem_comap, Subgroup.mem_comap, Subgroup.mem_map]
  have hfix := ((mem_range_threeSixEmb' hrange hgG hFg _).1 ⟨y, rfl⟩).2
  constructor
  · rintro ⟨u, hu, hyu⟩
    rw [threeSixEmb'_apply, ← hyu]
    simpa [MulAut.conj_apply, mul_assoc] using (Subgroup.mem_inf.1 hu).1
  · intro hy
    refine ⟨threeSixEmb' Ω K σ g y, Subgroup.mem_inf.2 ⟨hy, hfix⟩, ?_⟩
    rw [threeSixEmb'_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem centralizer_eq_comap
    {Fr : Ω →+* Ω} {ε : ℤ} {g : ModGL TwistTag.D4.tag Ω}
    (hrange : (threeSixEmb K Ω σ).range =
      adjointGroup TwistTag.D4.tag Ω ⊓ (trialityFrob Ω Fr).eqLocus (MonoidHom.id _))
    (hgG : g ∈ adjointGroup TwistTag.D4.tag Ω) (hFg : trialityFrob Ω Fr g = g * threeSixN Ω ε)
    {a : Fin TwistTag.D4.tag.rank → Ωˣ} {x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hx : threeSixEmb K Ω σ x = g * rootDiagUnit TwistTag.D4.tag a * g⁻¹) :
    Subgroup.centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) =
      (toralCentralizer TwistTag.D4.tag Ω a).comap (threeSixEmb' Ω K σ g) := by
  have hxa : threeSixEmb' Ω K σ g x = rootDiagUnit TwistTag.D4.tag a := by
    rw [threeSixEmb'_apply, hx]
    group
  ext y
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_comap, mem_toralCentralizer]
  have hG := ((mem_range_threeSixEmb' hrange hgG hFg _).1 ⟨y, rfl⟩).1
  rw [← (threeSixEmb'_injective (K := K) (σ := σ) g).eq_iff, map_mul, map_mul, hxa]
  set u := threeSixEmb' Ω K σ g y
  constructor
  · intro h
    refine ⟨hG, ?_⟩
    rw [← h, mul_inv_cancel_right]
  · rintro ⟨-, h⟩
    calc u * rootDiagUnit TwistTag.D4.tag a =
        rootDiagUnit TwistTag.D4.tag a * u * (rootDiagUnit TwistTag.D4.tag a)⁻¹ *
          rootDiagUnit TwistTag.D4.tag a := by rw [h]
      _ = rootDiagUnit TwistTag.D4.tag a * u := by group

end Fixed

end CFSG.RankThree.Chevalley
