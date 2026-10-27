module

public import CFSG.RankThree.Chevalley.SteinbergCDTrialityThreeSixCoreTools
public import CFSG.RankThree.PartOne.KC.PlaneReduction

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.Lattice CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.GroupTheory.SteinbergBY
open Subgroup
open scoped Pointwise commutatorElement

@[expose] def SingularCentralizerData
    {K : Type} [Field K] (σ : K ≃+* K) (q : ℕ)
    (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : Prop :=
  CFSG.IsQuasisimple (⁅centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
    centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁆ :
      Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∧
  Odd (Nat.card (center (⁅centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
    centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁆ :
      Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))) ∧
  Odd ((⁅centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
    centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁆ :
      Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).relIndex
        (centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))) ∧
  ∃ X : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
    X ⊆ ((⁅centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
      centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁆ :
        Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
          Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ∧
    Nat.card (Subfield.closure ((fun r : graphFixedRootGroup TwistTag.D4 K σ.toRingHom =>
      LinearMap.trace K (RootModule TwistTag.D4.tag K)
        ((r : ModGL TwistTag.D4.tag K) : Module.End K (RootModule TwistTag.D4.tag K))) '' X)) = q

theorem trace_conj_inv_mul {K : Type} [Field K] (c r : ModGL TwistTag.D4.tag K) :
    LinearMap.trace K (RootModule TwistTag.D4.tag K)
        ((c⁻¹ * r * c : ModGL TwistTag.D4.tag K) : Module.End K (RootModule TwistTag.D4.tag K)) =
      LinearMap.trace K (RootModule TwistTag.D4.tag K)
        ((r : ModGL TwistTag.D4.tag K) : Module.End K (RootModule TwistTag.D4.tag K)) := by
  rw [Units.val_mul, Units.val_mul, mul_assoc, LinearMap.trace_mul_comm, mul_assoc,
    Units.mul_inv, mul_one]

theorem singularCentralizerData_of_conj
    {K : Type} [Field K] {σ : K ≃+* K} {q : ℕ}
    {x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (h : SingularCentralizerData σ q (c * x * c⁻¹)) : SingularCentralizerData σ q x := by
  obtain ⟨hq, hZ, hDR, X, hXR, hX⟩ := h
  obtain ⟨φ, hφ⟩ : ∃ φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      φ = MulAut.conj c⁻¹ := ⟨_, rfl⟩
  have hφx : φ (c * x * c⁻¹) = x := by
    rw [hφ, MulAut.conj_apply]
    group
  have hD : (centralizer ({c * x * c⁻¹} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))).map
      φ.toMonoidHom = centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
    rw [CFSG.RankThree.PartOne.map_centralizer_singleton_mulEquiv, hφx]
  have hR : (⁅centralizer ({c * x * c⁻¹} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
      centralizer ({c * x * c⁻¹} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁆ :
        Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.toMonoidHom =
      ⁅centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
        centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))⁆ := by
    rw [map_commutator, hD]
  have e := (equivMapOfInjective _ _ φ.injective).trans (MulEquiv.subgroupCongr hR)
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq, ?_, ?_, φ '' X, ?_, ?_⟩
  · rw [← map_center_eq e, card_map_of_injective (by exact e.injective)]
    exact hZ
  · rw [← hR, ← hD, relIndex_map_map_of_injective _ _ φ.injective]
    exact hDR
  · rintro _ ⟨r, hr, rfl⟩
    rw [← hR]
    exact ⟨r, hXR hr, rfl⟩
  · have himg : (fun r : graphFixedRootGroup TwistTag.D4 K σ.toRingHom =>
        LinearMap.trace K (RootModule TwistTag.D4.tag K)
          ((r : ModGL TwistTag.D4.tag K) : Module.End K (RootModule TwistTag.D4.tag K))) ''
            (φ '' X) =
        (fun r : graphFixedRootGroup TwistTag.D4 K σ.toRingHom =>
          LinearMap.trace K (RootModule TwistTag.D4.tag K)
            ((r : ModGL TwistTag.D4.tag K) : Module.End K (RootModule TwistTag.D4.tag K))) ''
              X := by
      rw [Set.image_image]
      refine Set.image_congr fun r _ => ?_
      rw [hφ, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      exact trace_conj_inv_mul _ _
    rw [himg]
    exact hX

theorem odd_card_centralizer_of_conj {G : Type*} [Group G] {x : G} (c : G)
    (h : Odd (Nat.card (centralizer ({c * x * c⁻¹} : Set G)))) :
    Odd (Nat.card (centralizer ({x} : Set G))) := by
  rw [← map_conj_centralizer_singleton_eq, card_map_of_injective (MulAut.conj c).injective] at h
  exact h

theorem threeSix_dichotomy_of_singular
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type)
    [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (Fr : Ω →+* Ω)
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {d : ℕ}
    (hd : (d : ℤ) = ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * (ℓ ^ f : ℕ) + 1) {g : ModGL TwistTag.D4.tag Ω}
    (hgG : g ∈ adjointGroup TwistTag.D4.tag Ω) (hFg : trialityFrob Ω Fr g = g * threeSixN Ω ε)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpd : p ∣ d)
    (hsing : ∀ a : Fin TwistTag.D4.tag.rank → Ωˣ,
      rootDiagUnit TwistTag.D4.tag a ∈ threeSixTorus Ω Fr ε →
      orderOf (rootDiagUnit TwistTag.D4.tag a) = p → (survivingRoots a).Nonempty →
      ∀ x, threeSixEmb K Ω σ x = g * rootDiagUnit TwistTag.D4.tag a * g⁻¹ →
        SingularCentralizerData σ (ℓ ^ f) x) :
    (∀ x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, orderOf x = p →
      Odd (Nat.card (centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))) ∨
        SingularCentralizerData σ (ℓ ^ f) x) ∧
    (∀ A : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      IsElementaryAbelian p A → Nat.card A = p ^ 2 →
      (∃ x ∈ A, x ≠ 1 ∧
        Odd (Nat.card (centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))))) ∧
      ∃ x ∈ A, x ≠ 1 ∧ SingularCentralizerData σ (ℓ ^ f) x) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, -, hall⟩ :=
    triality_three_six_tori_Sylow_and_root_kernels hℓ hf K hK σ hσ Ω Fr hFr hε hd
  obtain ⟨-, -, hp'⟩ := hall g hgG hFg
  obtain ⟨-, -, -, -, -, -, -, -, hreg, hplanes⟩ := hp' p hp hp3 hpd
  have horder : ∀ a : Fin TwistTag.D4.tag.rank → Ωˣ,
      rootDiagUnit TwistTag.D4.tag a ∈ threeSixTorsion Ω Fr ε p →
      rootDiagUnit TwistTag.D4.tag a ≠ 1 → orderOf (rootDiagUnit TwistTag.D4.tag a) = p :=
    fun a ha ha1 => orderOf_eq_prime ha.2 ha1
  refine ⟨fun x hx => ?_, fun A hA hAcard => ?_⟩
  · obtain ⟨c, a, ha, ha1, hxa⟩ :=
      threeSix_conj_dichotomy hℓ hf K hK σ hσ Ω Fr hFr hε hd hgG hFg hp hp3 hpd x hx
    by_cases hemp : survivingRoots a = ∅
    · left
      obtain ⟨hcent, hodd⟩ := hreg a ha ha1 hemp _ hxa
      exact odd_card_centralizer_of_conj c (by rw [hcent]; exact hodd)
    · right
      exact singularCentralizerData_of_conj c
        (hsing a ha.1 (horder a ha ha1) (Set.nonempty_iff_ne_empty.2 hemp) _ hxa)
  · obtain ⟨c, hAc, ⟨M₁, hM₁A, hM₁card, hM₁⟩, ⟨M₂, hM₂A, hM₂card, hM₂⟩⟩ :=
      hplanes A hA hAcard
    have hne : ∀ M : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), Nat.card M = p →
        ∃ x ∈ M, x ≠ 1 := by
      intro M hM
      have hM1 : M ≠ ⊥ := fun h => by
        rw [h, card_bot] at hM
        exact hp.one_lt.ne hM
      obtain ⟨⟨x, hxM⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hM1
      exact ⟨x, hxM, fun h => hx1 (Subtype.ext h)⟩
    have hTp : ∀ x ∈ A, ∃ a : Fin TwistTag.D4.tag.rank → Ωˣ,
        rootDiagUnit TwistTag.D4.tag a ∈ threeSixTorsion Ω Fr ε p ∧
        threeSixEmb K Ω σ (c * x * c⁻¹) = g * rootDiagUnit TwistTag.D4.tag a * g⁻¹ := by
      intro x hx
      have hxT : (MulAut.conj c).toMonoidHom x ∈ threeSixFixedTorsion K Ω σ Fr ε p g := by
        rw [← hAc]
        exact ⟨x, hx, rfl⟩
      obtain ⟨u, hu, hux⟩ := hxT
      obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hu.1.1
      exact ⟨a, hu, hux.symm⟩
    have hda1 : ∀ x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, x ≠ 1 →
        ∀ a : Fin TwistTag.D4.tag.rank → Ωˣ,
        threeSixEmb K Ω σ (c * x * c⁻¹) = g * rootDiagUnit TwistTag.D4.tag a * g⁻¹ →
        rootDiagUnit TwistTag.D4.tag a ≠ 1 := by
      intro x hx1 a hxa h1
      rw [h1, mul_one, mul_inv_cancel] at hxa
      have h3 : c * x * c⁻¹ = 1 := threeSixEmb_injective K Ω σ (hxa.trans (map_one _).symm)
      rw [conj_eq_one_iff] at h3
      exact hx1 h3
    obtain ⟨xr, hxrM, hxr1⟩ := hne M₂ hM₂card
    obtain ⟨xs, hxsM, hxs1⟩ := hne M₁ hM₁card
    obtain ⟨ar, har, hxr⟩ := hTp xr (hM₂A hxrM)
    obtain ⟨as, has, hxs⟩ := hTp xs (hM₁A hxsM)
    refine ⟨⟨xr, hM₂A hxrM, hxr1, ?_⟩, ⟨xs, hM₁A hxsM, hxs1, ?_⟩⟩
    · obtain ⟨hcent, hodd⟩ :=
        hreg ar har (hda1 xr hxr1 ar hxr) (hM₂ xr hxrM hxr1 ar hxr) _ hxr
      exact odd_card_centralizer_of_conj c (by rw [hcent]; exact hodd)
    · exact singularCentralizerData_of_conj c (hsing as has.1
        (horder as has (hda1 xs hxs1 as hxs)) (hM₁ xs hxsM as hxs) _ hxs)

theorem natCard_closure_image_of_injective {F E : Type*} [Field F] [Field E] (f : F →+* E)
    (S : Set F) : Nat.card (Subfield.closure (f '' S)) = Nat.card (Subfield.closure S) := by
  rw [← RingHom.map_field_closure]
  change Nat.card ((Subfield.map f (Subfield.closure S) : Subfield E) : Set E) =
    Nat.card ((Subfield.closure S : Subfield F) : Set F)
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Subfield.coe_map,
    Set.ncard_image_of_injective _ f.injective]

theorem natCard_closure_trace_threeSixEmb
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    (σ : K ≃+* K) (X : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    Nat.card (Subfield.closure ((fun r : graphFixedRootGroup TwistTag.D4 K σ.toRingHom =>
      LinearMap.trace Ω (RootModule TwistTag.D4.tag Ω) ((threeSixEmb K Ω σ r : ModGL
        TwistTag.D4.tag Ω) : Module.End Ω (RootModule TwistTag.D4.tag Ω))) '' X)) =
    Nat.card (Subfield.closure ((fun r : graphFixedRootGroup TwistTag.D4 K σ.toRingHom =>
      LinearMap.trace K (RootModule TwistTag.D4.tag K)
        ((r : ModGL TwistTag.D4.tag K) : Module.End K (RootModule TwistTag.D4.tag K))) '' X)) := by
  have himg : (fun r : graphFixedRootGroup TwistTag.D4 K σ.toRingHom =>
      LinearMap.trace Ω (RootModule TwistTag.D4.tag Ω) ((threeSixEmb K Ω σ r : ModGL
        TwistTag.D4.tag Ω) : Module.End Ω (RootModule TwistTag.D4.tag Ω))) '' X =
      algebraMap K Ω '' ((fun r : graphFixedRootGroup TwistTag.D4 K σ.toRingHom =>
        LinearMap.trace K (RootModule TwistTag.D4.tag K)
          ((r : ModGL TwistTag.D4.tag K) : Module.End K (RootModule TwistTag.D4.tag K))) '' X) := by
    rw [Set.image_image]
    refine Set.image_congr fun r _ => ?_
    exact trace_baseChangeGL (algebraMap K Ω) (r : ModGL TwistTag.D4.tag K)
  rw [himg, natCard_closure_image_of_injective]

end CFSG.RankThree.Chevalley
