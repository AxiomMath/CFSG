module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveAmbient
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveSylow
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeA2BlockTwist
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveInner
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeSCShapeBridge
public import CFSG.GroupTheory.ElemAbelianClosure

public noncomputable section

namespace CFSG.StandardType.NoOffTwE6Three

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Universal
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.HardMathSupport.Lang.E6Descent.TwistedDiag
  CFSG.StandardType.TableBExc.E6Three CFSG.RankThree.Classical2

section Helpers


private theorem zetaVec_mem_cubeRootTuples {Ω : Type} [Field Ω] {ζ : Ωˣ} (hζ : ζ ^ 3 = 1)
    (v : Fin Tag.E6.rank → ZMod 3) : zetaVec ζ hζ v ∈ cubeRootTuples Ω := by
  rw [mem_cubeRootTuples]
  intro i
  rw [zetaVec_apply, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]

private theorem rootDiagUnit_mem_thetaFixed_of_cube {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (Fr : Ω →+* Ω) {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) (h3 : 3 ∣ q + 1)
    {b : Fin Tag.E6.rank → Ωˣ} (hb : ∀ i, b i ^ 3 = 1) :
    rootDiagUnit Tag.E6 b ∈ thetaFixed Fr := by
  rw [mem_thetaFixed]
  refine ⟨torusGroup_le_adjointGroup_E6 (rootDiagUnit_mem_torusGroup b), ?_⟩
  simpa [TwistedDiag.theta, TwistedDiag.n0] using
    (conj_twistE6_rootDiagUnit_of_cube (Fr := Fr) hFr h3 b hb)

private theorem exists_three_six_thetaFixed {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    {Fr : Ω →+* Ω} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) (h3 : 3 ∣ q + 1)
    (h30 : (3 : Ω) ≠ 0) {ζ : Ωˣ} (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3) :
    ∃ H3 : Subgroup (ModGL Tag.E6 Ω), H3 ≤ thetaFixed Fr ∧ IsElemAbelian 3 H3 ∧
      Nat.card H3 = 3 ^ 6 ∧
      ∀ h, h ∈ H3 ↔ ∃ v, h = rootDiagUnit Tag.E6 (zetaVec ζ hζ v) := by
  refine ⟨(cubeRootTuples Ω).map (rootDiagUnitHom Tag.E6 Ω), ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    exact rootDiagUnit_mem_thetaFixed_of_cube Fr hFr h3 (mem_cubeRootTuples.1 hb)
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
        ⟨zetaVec ζ hζ v, zetaVec_mem_cubeRootTuples hζ v, rfl⟩

end Helpers

theorem ggTwE6ThreeRankFiveInput_of_a2Block
    (hblock : A2BlockTwoInput) : GGTwE6ThreeRankFiveInput := by
  intro f hf h3 S hSel hSI h5
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K := GaloisField 2 (2 * f)
  let Ω := AlgebraicClosure K
  haveI : CharP K 2 := inferInstance
  haveI : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  let Fr : Ω →+* Ω := iterateFrobenius Ω 2 f
  have hFr : ∀ c, Fr c = c ^ 2 ^ f := fun c => iterateFrobenius_def 2 f c
  have hσ : ∀ c : K, frobQ 2 f c = c ^ 2 ^ f := fun c => frobQ_apply 2 f c
  have hK : Nat.card K = (2 ^ f) ^ 2 := card_galoisField_two_mul 2 f hf
  have hq0 : ((2 ^ f : ℕ) : Ω) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero Ω 2, zero_pow (by omega)]
  have h30 : (3 : Ω) ≠ 0 := three_ne_zero_of_dvd_card_add_one (ℓ := 2) hf h3
  obtain ⟨ζ, hζ, hζo⟩ := exists_cube_root (Ω := Ω) h30
  obtain ⟨Φ, hΦinj, hΦrange, hΦC⟩ := exists_rgrpAut (f := f) hf Ω Fr hFr
  obtain ⟨g, hg, hgn⟩ := exists_inv_mul_twistE6_eq (ℓ := 2) (f := f) hf hFr
    (canonicalRep_mem_adjointGroup (coxeterSystem Tag.E6) Ω twE6W0)
  let R := TwistedDiag.Rgrp Ω Fr
  let C := TwistedDiag.Cgrp K (frobQ 2 f) Ω
  let X : Subgroup (ModGL Tag.E6 Ω) := (S.comap Φ).map R.subtype
  have hXR : X ≤ R := Subgroup.map_subtype_le (S.comap Φ)
  have hSrange : S ≤ Φ.range := by rw [hΦrange]; exact hSI
  have hXcard : Nat.card X = Nat.card S := by
    change Nat.card ↥(Subgroup.map R.subtype (Subgroup.comap Φ S)) = Nat.card ↥S
    have h1 : Nat.card ((S.comap Φ).map Φ) = Nat.card (S.comap Φ) :=
      Subgroup.card_map_of_injective hΦinj
    have h2 : (S.comap Φ).map Φ = S := Subgroup.map_comap_eq_self hSrange
    have h3 : Nat.card (S.comap Φ) = Nat.card S := by rw [← h1, h2]
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective R), h3]
  have hXel : IsElemAbelian 3 X := (hSel.comap hΦinj).map R.subtype
  have hXp : IsPGroup 3 X := hXel.isPGroup
  have h5X : 3 ^ 5 ≤ Nat.card X := by rw [hXcard]; exact h5
  obtain ⟨k, hkθ, r, hrR, hX₁le⟩ := exists_conj_le_xHat (ℓ := 2) hf K hK
    (frobQ 2 f) hσ h3 Ω Fr hFr hg hgn hXR hXp
  let c₁ : ModGL Tag.E6 Ω := k * g⁻¹ * r
  let E : Subgroup (ModGL Tag.E6 Ω) := X.map (MulAut.conj c₁).toMonoidHom
  have hEel : IsElemAbelian 3 E := hXel.map (MulAut.conj c₁).toMonoidHom
  have hEX : E ≤ xHat Tag.E6 Ω modelHomE6.range := hX₁le.trans inf_le_left
  have hEθ : E ≤ TwistedDiag.thetaFixed Fr := hX₁le.trans inf_le_right
  have hEcard : 3 ^ 5 ≤ Nat.card E := by
    change 3 ^ 5 ≤ Nat.card ↥(Subgroup.map (MulAut.conj c₁).toMonoidHom X)
    rw [Subgroup.card_map_of_injective (MulAut.conj c₁).injective]
    exact h5X
  have hcase := torus_or_cyclic (ζ := ζ) hζo hζ hEel hEX hEcard
  obtain ⟨z, hzθ, hzconj⟩ : ∃ z ∈ TwistedDiag.thetaFixed Fr,
      ∀ e ∈ E, ∃ v, z * e * z⁻¹ = rootDiagUnit Tag.E6 (zetaVec ζ hζ v) := by
    rcases hcase with htor | ⟨i, hEXi⟩
    · exact ⟨1, one_mem _, fun e he => by
        obtain ⟨v, hv⟩ := htor e he
        exact ⟨v, by rw [one_mul, inv_one, mul_one, hv]⟩⟩
    · exact exists_thetaFixed_conj_of_cyclic hblock hFr hq0 h3 hζ hζo i hEel hEθ hEXi
  obtain ⟨H3, hH3θ, hH3el, hH3card, hH3shape⟩ :=
    exists_three_six_thetaFixed hFr h3 h30 hζ hζo
  let c : ModGL Tag.E6 Ω := z * c₁
  let Y_R : Subgroup (ModGL Tag.E6 Ω) := H3.map (MulAut.conj c⁻¹).toMonoidHom
  have hYRel : IsElemAbelian 3 Y_R := hH3el.map (MulAut.conj c⁻¹).toMonoidHom
  have hYR_R : Y_R ≤ R := by
    rintro _ ⟨h, hh, rfl⟩
    change c⁻¹ * h * (c⁻¹)⁻¹ ∈ R
    rw [inv_inv]
    have hzkθ : k⁻¹ * z⁻¹ * h * z * k ∈ TwistedDiag.thetaFixed Fr :=
      mul_mem (mul_mem (mul_mem (mul_mem (inv_mem hkθ) (inv_mem hzθ)) (hH3θ hh)) hzθ) hkθ
    have hgR : g * (k⁻¹ * z⁻¹ * h * z * k) * g⁻¹ ∈ R :=
      (TwistedDiag.mem_thetaFixed_iff_conj Fr hg hgn _).1 hzkθ
    have hident : c⁻¹ * h * c = r⁻¹ * (g * (k⁻¹ * z⁻¹ * h * z * k) * g⁻¹) * r := by
      simp only [c, c₁]
      group
    rw [hident]
    exact mul_mem (mul_mem (inv_mem hrR) hgR) hrR
  have hXle : X ≤ Y_R := by
    intro x hx
    have hxE : c₁ * x * c₁⁻¹ ∈ E := ⟨x, hx, rfl⟩
    obtain ⟨v, hv⟩ := hzconj _ hxE
    refine (Subgroup.mem_map (f := (MulAut.conj c⁻¹).toMonoidHom)).2
      ⟨rootDiagUnit Tag.E6 (zetaVec ζ hζ v), ?_, ?_⟩
    · exact (hH3shape _).2 ⟨v, rfl⟩
    · change c⁻¹ * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * (c⁻¹)⁻¹ = x
      rw [inv_inv]
      rw [← hv]
      simp only [c]
      group
  let Y : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 K (frobQ 2 f))) :=
    (Y_R.subgroupOf R).map Φ
  have hYle : Y ≤ LayerSixE.twInndiagAut f := by
    rw [← hΦrange]
    exact Subgroup.map_le_range Φ _
  have hSY : S ≤ Y := by
    intro s hs
    obtain ⟨x, hxeq⟩ := MonoidHom.mem_range.1 (hSrange hs)
    have hxcomap : x ∈ S.comap Φ := by
      rw [Subgroup.mem_comap, hxeq]
      exact hs
    have hxX : (x : ModGL Tag.E6 Ω) ∈ X := Subgroup.mem_map.2 ⟨x, hxcomap, rfl⟩
    have hxYR : (x : ModGL Tag.E6 Ω) ∈ Y_R := hXle hxX
    have hxsub : x ∈ Y_R.subgroupOf R := Subgroup.mem_subgroupOf.2 hxYR
    have hxY : Φ x ∈ Y := Subgroup.mem_map.2 ⟨x, hxsub, rfl⟩
    rwa [hxeq] at hxY
  have hYel : IsElemAbelian 3 Y :=
    (hYRel.subgroupOf R).map Φ
  have hYcard : Nat.card Y = 3 ^ 6 := by
    calc Nat.card Y = Nat.card (Y_R.subgroupOf R) :=
          Subgroup.card_map_of_injective hΦinj
      _ = Nat.card Y_R := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYR_R).toEquiv
      _ = Nat.card H3 := Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective
      _ = 3 ^ 6 := hH3card
  obtain ⟨-, hCR, hCnorm, -, -⟩ :=
    TwistedDiag.cgrp_facts hf K hK (frobQ 2 f) hσ h3 Ω Fr hFr
  refine ⟨Y, hYle, hSY, hYel, hYcard, ?_⟩
  intro h9
  intro y hy
  obtain ⟨yR, hyRmem, rfl⟩ := Subgroup.mem_map.1 hy
  have hyYR : (yR : ModGL Tag.E6 Ω) ∈ Y_R := Subgroup.mem_subgroupOf.1 hyRmem
  obtain ⟨h, hhH3, hhy⟩ := Subgroup.mem_map.1 hyYR
  have hyRC : (yR : ModGL Tag.E6 Ω) ∈ C := by
    obtain ⟨v, hv⟩ := (hH3shape h).1 hhH3
    have hghC : g * h * g⁻¹ ∈ C := by
      rw [hv]
      exact conj_rootDiagUnit_mem_Cgrp_of_nine_dvd (ℓ := 2) hf K hK (frobQ 2 f) hσ h9
        Ω Fr hFr hg hgn hζ v
    let u : ModGL Tag.E6 Ω := g * (z * k) * g⁻¹
    have hzkθ : z * k ∈ TwistedDiag.thetaFixed Fr := mul_mem hzθ hkθ
    have huR : u ∈ R := (TwistedDiag.mem_thetaFixed_iff_conj Fr hg hgn _).1 hzkθ
    have hmidC : u⁻¹ * (g * h * g⁻¹) * u ∈ C := by
      have hN : (C.subgroupOf R).Normal := hCnorm
      have hn : (⟨g * h * g⁻¹, hCR hghC⟩ : ↥R) ∈ C.subgroupOf R :=
        Subgroup.mem_subgroupOf.2 hghC
      have h := hN.conj_mem' (⟨g * h * g⁻¹, hCR hghC⟩ : ↥R) hn (⟨u, huR⟩ : ↥R)
      simpa [u] using Subgroup.mem_subgroupOf.1 h
    have hmidR : u⁻¹ * (g * h * g⁻¹) * u ∈ R := hCR hmidC
    have hfinalC : r⁻¹ * (u⁻¹ * (g * h * g⁻¹) * u) * r ∈ C := by
      have hN : (C.subgroupOf R).Normal := hCnorm
      have hn : (⟨u⁻¹ * (g * h * g⁻¹) * u, hmidR⟩ : ↥R) ∈ C.subgroupOf R :=
        Subgroup.mem_subgroupOf.2 hmidC
      have h := hN.conj_mem' (⟨u⁻¹ * (g * h * g⁻¹) * u, hmidR⟩ : ↥R) hn (⟨r, hrR⟩ : ↥R)
      simpa using Subgroup.mem_subgroupOf.1 h
    have hgroup : c⁻¹ * h * c = r⁻¹ * (u⁻¹ * (g * h * g⁻¹) * u) * r := by
      simp only [c, c₁, u]
      group
    have hhy' : (yR : ModGL Tag.E6 Ω) = c⁻¹ * h * c := by
      rw [← hhy]
      rfl
    rw [hhy', hgroup]
    exact hfinalC
  exact hΦC (yR : ModGL Tag.E6 Ω) yR.2 hyRC

end CFSG.StandardType.NoOffTwE6Three
