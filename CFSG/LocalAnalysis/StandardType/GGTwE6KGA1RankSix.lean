module

public import CFSG.LocalAnalysis.StandardType.GGTwE6KGA1Defs
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeToralCentHolds
public import CFSG.HardMathSupport.Lang.E6Descent.RankTwistedE6
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType.NoOffTwE6Three

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.HardMathSupport.Lang.E6Descent CFSG.Open
  CFSG.HardMathSupport.Lang.E6Descent.TwistedDiag CFSG.StandardType.TableBExc.E6Three
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical2

private theorem rs_zetaVec_mem_cubeRootTuples {Ω : Type} [Field Ω] {ζ : Ωˣ} (hζ : ζ ^ 3 = 1)
    (v : Fin Tag.E6.rank → ZMod 3) : zetaVec ζ hζ v ∈ cubeRootTuples Ω := by
  rw [mem_cubeRootTuples]
  intro i
  rw [zetaVec_apply, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]

private theorem rs_rootDiagUnit_mem_thetaFixed_of_cube {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (Fr : Ω →+* Ω) {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) (h3 : 3 ∣ q + 1)
    {b : Fin Tag.E6.rank → Ωˣ} (hb : ∀ i, b i ^ 3 = 1) :
    rootDiagUnit Tag.E6 b ∈ thetaFixed Fr := by
  rw [mem_thetaFixed]
  refine ⟨torusGroup_le_adjointGroup_E6 (rootDiagUnit_mem_torusGroup b), ?_⟩
  simpa [TwistedDiag.theta, TwistedDiag.n0] using
    (conj_twistE6_rootDiagUnit_of_cube (Fr := Fr) hFr h3 b hb)

private theorem rs_exists_three_six_thetaFixed {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    {Fr : Ω →+* Ω} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) (h3 : 3 ∣ q + 1)
    (h30 : (3 : Ω) ≠ 0) {ζ : Ωˣ} (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3) :
    ∃ H3 : Subgroup (ModGL Tag.E6 Ω), H3 ≤ thetaFixed Fr ∧ IsElemAbelian 3 H3 ∧
      Nat.card H3 = 3 ^ 6 ∧
      ∀ h, h ∈ H3 ↔ ∃ v, h = rootDiagUnit Tag.E6 (zetaVec ζ hζ v) := by
  refine ⟨(cubeRootTuples Ω).map (rootDiagUnitHom Tag.E6 Ω), ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    exact rs_rootDiagUnit_mem_thetaFixed_of_cube Fr hFr h3 (mem_cubeRootTuples.1 hb)
  · exact CFSG.HardMathSupport.Lang.E6Descent.isElemAbelian_map (rootDiagUnitHom Tag.E6 Ω)
      (cubeRootTuples Ω) (fun a ha => funext fun i => mem_cubeRootTuples.1 ha i)
  · rw [Subgroup.card_map_of_injective (rootDiagUnit_injective (τ := Tag.E6) (K := Ω)),
      natCard_cubeRootTuples (Ω := Ω) h30]
  · intro h
    constructor
    · rintro ⟨b, hb, rfl⟩
      have hb3 : b ^ 3 = 1 := by funext i; exact (mem_cubeRootTuples.1 hb) i
      obtain ⟨v, hv⟩ := exists_zetaVec_eq (τ := Tag.E6) (p := 3) hζo hζ hb3
      refine ⟨v, ?_⟩
      rw [hv]
      rfl
    · rintro ⟨v, rfl⟩
      exact (Subgroup.mem_map (f := rootDiagUnitHom Tag.E6 Ω)).2
        ⟨zetaVec ζ hζ v, rs_zetaVec_mem_cubeRootTuples hζ v, rfl⟩

theorem exists_overgroup_of_isToral (h84 : GGTwE6ThreeToralTypeMinusOneInput) {f : ℕ} (hf : 1 ≤ f)
    (h3 : 3 ∣ 2 ^ f + 1) (Ω : Type) [Field Ω] [Algebra (GaloisField 2 (2 * f)) Ω]
    [IsAlgClosure (GaloisField 2 (2 * f)) Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ f)
    (Φ : ↥(TwistedDiag.Rgrp Ω Fr) →*
      MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))
    (hΦinj : Function.Injective Φ) (hΦrange : Φ.range = LayerSixE.twInndiagAut f)
    {X : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))}
    (hXI : X ≤ LayerSixE.twInndiagAut f) (hel : IsElemAbelian 3 X) (hc : Nat.card X = 3 ^ 4)
    (htor : IsToralE6 Ω ((X.comap Φ).map (TwistedDiag.Rgrp Ω Fr).subtype)) :
    ∃ Y : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
        (frobQ 2 f))),
      Y ≤ LayerSixE.twInndiagAut f ∧ X ≤ Y ∧ IsElemAbelian 3 Y ∧ Nat.card Y = 3 ^ 6 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K := GaloisField 2 (2 * f)
  haveI : CharP K 2 := inferInstance
  haveI : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have h30 : (3 : Ω) ≠ 0 := three_ne_zero_of_dvd_card_add_one (ℓ := 2) hf h3
  obtain ⟨ζ, hζ, hζo⟩ := exists_cube_root (Ω := Ω) h30
  let R := TwistedDiag.Rgrp Ω Fr
  let X_R : Subgroup (ModGL Tag.E6 Ω) := (X.comap Φ).map R.subtype
  have hXR : X_R ≤ R := Subgroup.map_subtype_le (X.comap Φ)
  have hSrange : X ≤ Φ.range := by rw [hΦrange]; exact hXI
  have hXcard : Nat.card X_R = Nat.card X := by
    change Nat.card ↥(Subgroup.map R.subtype (Subgroup.comap Φ X)) = Nat.card ↥X
    have h1 : Nat.card ((X.comap Φ).map Φ) = Nat.card (X.comap Φ) :=
      Subgroup.card_map_of_injective hΦinj
    have h2 : (X.comap Φ).map Φ = X := Subgroup.map_comap_eq_self hSrange
    have h3 : Nat.card (X.comap Φ) = Nat.card X := by rw [← h1, h2]
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective R), h3]
  have hXel : IsElemAbelian 3 X_R := (hel.comap hΦinj).map R.subtype
  have hcXR : Nat.card X_R = 3 ^ 4 := by rw [hXcard, hc]
  obtain ⟨g, hg, hgn, hgX⟩ := h84 hf h3 Ω Fr hFr hζ hζo hXR hXel hcXR htor
  obtain ⟨H3, hH3θ, hH3el, hH3card, hH3shape⟩ :=
    rs_exists_three_six_thetaFixed hFr h3 h30 hζ hζo
  let Y_R : Subgroup (ModGL Tag.E6 Ω) := H3.map (MulAut.conj g).toMonoidHom
  have hYRel : IsElemAbelian 3 Y_R := hH3el.map (MulAut.conj g).toMonoidHom
  have hYR_R : Y_R ≤ R := by
    rintro _ ⟨h, hh, rfl⟩
    exact (TwistedDiag.mem_thetaFixed_iff_conj Fr hg hgn h).1 (hH3θ hh)
  have hXle : X_R ≤ Y_R := by
    intro x hx
    obtain ⟨v, hv⟩ := hgX x hx
    refine (Subgroup.mem_map (f := (MulAut.conj g).toMonoidHom)).2
      ⟨rootDiagUnit Tag.E6 (zetaVec ζ hζ v), ?_, ?_⟩
    · exact (hH3shape _).2 ⟨v, rfl⟩
    · change g * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * g⁻¹ = x
      rw [← hv]
  let Y : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 K (frobQ 2 f))) :=
    (Y_R.subgroupOf R).map Φ
  have hYle : Y ≤ LayerSixE.twInndiagAut f := by
    rw [← hΦrange]
    exact Subgroup.map_le_range Φ _
  have hXY : X ≤ Y := by
    intro s hs
    obtain ⟨x, hxeq⟩ := MonoidHom.mem_range.1 (hSrange hs)
    have hxcomap : x ∈ X.comap Φ := by
      rw [Subgroup.mem_comap, hxeq]
      exact hs
    have hxX : (x : ModGL Tag.E6 Ω) ∈ X_R := Subgroup.mem_map.2 ⟨x, hxcomap, rfl⟩
    have hxYR : (x : ModGL Tag.E6 Ω) ∈ Y_R := hXle hxX
    have hxsub : x ∈ Y_R.subgroupOf R := Subgroup.mem_subgroupOf.2 hxYR
    have hxY : Φ x ∈ Y := Subgroup.mem_map.2 ⟨x, hxsub, rfl⟩
    rwa [hxeq] at hxY
  have hYel : IsElemAbelian 3 Y := (hYRel.subgroupOf R).map Φ
  have hYcard : Nat.card Y = 3 ^ 6 := by
    calc Nat.card Y = Nat.card (Y_R.subgroupOf R) :=
          Subgroup.card_map_of_injective hΦinj
      _ = Nat.card Y_R := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYR_R).toEquiv
      _ = Nat.card H3 := Subgroup.card_map_of_injective (MulAut.conj g).injective
      _ = 3 ^ 6 := hH3card
  exact ⟨Y, hYle, hXY, hYel, hYcard⟩

end CFSG.StandardType.NoOffTwE6Three
