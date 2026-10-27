module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveAmbient
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveSylow
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeA2BlockTwo
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveInner
public import CFSG.GroupTheory.ElemAbelianClosure

public noncomputable section

namespace CFSG.StandardType.TwE6DD2

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Universal
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.StandardType.TableBExc.E6Three
  CFSG.RankThree.Classical2 CFSG.StandardType.NoOffTwE6Three

section Diag


variable {Ω : Type} [Field Ω]

theorem isElemAbelian_cubeTorus :
    IsElemAbelian 3 ((cubeRootTuples Ω).map (rootDiagUnitHom Tag.E6 Ω)) :=
  CFSG.HardMathSupport.Lang.E6Descent.isElemAbelian_map (rootDiagUnitHom Tag.E6 Ω)
    (cubeRootTuples Ω)
    (fun a ha => funext fun i => mem_cubeRootTuples.1 ha i)

theorem rootDiagUnit_mem_cubeTorus {b : Fin Tag.E6.rank → Ωˣ} (hb : ∀ i, b i ^ 3 = 1) :
    rootDiagUnit Tag.E6 b ∈ (cubeRootTuples Ω).map (rootDiagUnitHom Tag.E6 Ω) :=
  ⟨b, mem_cubeRootTuples.2 hb, rfl⟩

theorem card_cubeTorus [IsAlgClosed Ω] (h30 : (3 : Ω) ≠ 0) :
    Nat.card ((cubeRootTuples Ω).map (rootDiagUnitHom Tag.E6 Ω)) = 3 ^ 6 := by
  rw [Subgroup.card_map_of_injective (rootDiagUnit_injective (τ := Tag.E6) (K := Ω)),
    natCard_cubeRootTuples (Ω := Ω) h30]

end Diag

section Lang


variable {Ω : Type} [Field Ω] (Fr : Ω →+* Ω)

theorem twistE6_of_mem_thetaFixed {x : ModGL Tag.E6 Ω} (hx : x ∈ TwistedDiag.thetaFixed Fr) :
    twistE6 Ω Fr x = (TwistedDiag.n0 Ω)⁻¹ * x * TwistedDiag.n0 Ω := by
  have h := ((TwistedDiag.mem_thetaFixed Fr).1 hx).2
  rw [TwistedDiag.theta_apply] at h
  calc twistE6 Ω Fr x = (TwistedDiag.n0 Ω)⁻¹ *
        (TwistedDiag.n0 Ω * twistE6 Ω Fr x * (TwistedDiag.n0 Ω)⁻¹) * TwistedDiag.n0 Ω := by
          group
    _ = (TwistedDiag.n0 Ω)⁻¹ * x * TwistedDiag.n0 Ω := by rw [h]

theorem mul_inv_mem_Rgrp {g₁ g₂ : ModGL Tag.E6 Ω} (hg₁ : g₁ ∈ adjointGroup Tag.E6 Ω)
    (hgn₁ : g₁⁻¹ * twistE6 Ω Fr g₁ = TwistedDiag.n0 Ω) (hg₂ : g₂ ∈ adjointGroup Tag.E6 Ω)
    (hgn₂ : g₂⁻¹ * twistE6 Ω Fr g₂ = TwistedDiag.n0 Ω) :
    g₂ * g₁⁻¹ ∈ TwistedDiag.Rgrp Ω Fr := by
  refine (TwistedDiag.mem_Rgrp Fr).2 ⟨mul_mem hg₂ (inv_mem hg₁), ?_⟩
  have h₁ : twistE6 Ω Fr g₁ = g₁ * TwistedDiag.n0 Ω := by rw [← hgn₁, mul_inv_cancel_left]
  have h₂ : twistE6 Ω Fr g₂ = g₂ * TwistedDiag.n0 Ω := by rw [← hgn₂, mul_inv_cancel_left]
  rw [map_mul, map_inv, h₁, h₂]
  group

theorem conj_cubeTorus_le_Rgrp [IsAlgClosed Ω] {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    (h3 : 3 ∣ q + 1) {g : ModGL Tag.E6 Ω} (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = TwistedDiag.n0 Ω) :
    ((cubeRootTuples Ω).map (rootDiagUnitHom Tag.E6 Ω)).map (MulAut.conj g).toMonoidHom ≤
      TwistedDiag.Rgrp Ω Fr := by
  rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
  change g * rootDiagUnit Tag.E6 b * g⁻¹ ∈ TwistedDiag.Rgrp Ω Fr
  refine (TwistedDiag.mem_thetaFixed_iff_conj Fr hg hgn _).1 ?_
  rw [TwistedDiag.mem_thetaFixed]
  refine ⟨torusGroup_le_adjointGroup_E6 (rootDiagUnit_mem_torusGroup b), ?_⟩
  simpa [TwistedDiag.theta, TwistedDiag.n0] using
    (conj_twistE6_rootDiagUnit_of_cube (Fr := Fr) hFr h3 b (mem_cubeRootTuples.1 hb))

end Lang

section Cube


variable {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
  (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) {Ω : Type} [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)

@[expose] noncomputable def langCube (g : ModGL Tag.E6 Ω) :
    Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :=
  ((((cubeRootTuples Ω).map (rootDiagUnitHom Tag.E6 Ω)).map
      (MulAut.conj g).toMonoidHom).subgroupOf (TwistedDiag.Rgrp Ω Fr)).map
    (rgrpConjAut hn hK σ hσ Fr hFr)

theorem mem_langCube {g : ModGL Tag.E6 Ω}
    {y : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)} :
    y ∈ langCube hn hK σ hσ Fr hFr g ↔ ∃ b : Fin Tag.E6.rank → Ωˣ, (∀ i, b i ^ 3 = 1) ∧
      ∃ hx : g * rootDiagUnit Tag.E6 b * g⁻¹ ∈ TwistedDiag.Rgrp Ω Fr,
        rgrpConjAut hn hK σ hσ Fr hFr ⟨_, hx⟩ = y := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨_, ⟨b, hb, rfl⟩, hbx⟩ := Subgroup.mem_subgroupOf.1 hx
    have hbx' : g * rootDiagUnit Tag.E6 b * g⁻¹ = (x : ModGL Tag.E6 Ω) := hbx
    refine ⟨b, mem_cubeRootTuples.1 hb, hbx' ▸ x.2, ?_⟩
    congr 1
    exact Subtype.ext hbx'
  · rintro ⟨b, hb, hx, rfl⟩
    exact ⟨⟨_, hx⟩, Subgroup.mem_subgroupOf.2 ⟨_, rootDiagUnit_mem_cubeTorus hb, rfl⟩, rfl⟩

theorem langCube_le_range (g : ModGL Tag.E6 Ω) :
    langCube hn hK σ hσ Fr hFr g ≤ (RecipeExcLang.twConj K σ).range := by
  rw [← rgrpConjAut_range hn hK σ hσ Fr hFr]
  exact Subgroup.map_le_range _ _

theorem isElemAbelian_langCube (g : ModGL Tag.E6 Ω) :
    IsElemAbelian 3 (langCube hn hK σ hσ Fr hFr g) :=
  ((isElemAbelian_cubeTorus.map (MulAut.conj g).toMonoidHom).subgroupOf _).map _

theorem card_langCube (h3 : 3 ∣ 2 ^ n + 1) {g : ModGL Tag.E6 Ω}
    (hg : g ∈ adjointGroup Tag.E6 Ω) (hgn : g⁻¹ * twistE6 Ω Fr g = TwistedDiag.n0 Ω) :
    Nat.card (langCube hn hK σ hσ Fr hFr g) = 3 ^ 6 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  haveI : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have h30 : (3 : Ω) ≠ 0 := three_ne_zero_of_dvd_card_add_one (ℓ := 2) hn h3
  have hle := conj_cubeTorus_le_Rgrp Fr hFr h3 hg hgn
  calc Nat.card (langCube hn hK σ hσ Fr hFr g) = Nat.card ((((cubeRootTuples Ω).map
          (rootDiagUnitHom Tag.E6 Ω)).map (MulAut.conj g).toMonoidHom).subgroupOf
            (TwistedDiag.Rgrp Ω Fr)) :=
        Subgroup.card_map_of_injective (rgrpConjAut_injective hn hK σ hσ Fr hFr)
    _ = Nat.card (((cubeRootTuples Ω).map (rootDiagUnitHom Tag.E6 Ω)).map
          (MulAut.conj g).toMonoidHom) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    _ = Nat.card ((cubeRootTuples Ω).map (rootDiagUnitHom Tag.E6 Ω)) :=
        Subgroup.card_map_of_injective (MulAut.conj g).injective
    _ = 3 ^ 6 := card_cubeTorus h30

theorem exists_conj_langCube {g₁ g₂ : ModGL Tag.E6 Ω} (hg₁ : g₁ ∈ adjointGroup Tag.E6 Ω)
    (hgn₁ : g₁⁻¹ * twistE6 Ω Fr g₁ = TwistedDiag.n0 Ω) (hg₂ : g₂ ∈ adjointGroup Tag.E6 Ω)
    (hgn₂ : g₂⁻¹ * twistE6 Ω Fr g₂ = TwistedDiag.n0 Ω) :
    ∃ β ∈ (RecipeExcLang.twConj K σ).range,
      (langCube hn hK σ hσ Fr hFr g₁).map (MulAut.conj β).toMonoidHom =
        langCube hn hK σ hσ Fr hFr g₂ := by
  set Φ := rgrpConjAut hn hK σ hσ Fr hFr with hΦ
  have hx := mul_inv_mem_Rgrp Fr hg₁ hgn₁ hg₂ hgn₂
  set x : ↥(TwistedDiag.Rgrp Ω Fr) := ⟨g₂ * g₁⁻¹, hx⟩ with hxdef
  refine ⟨Φ x, (rgrpConjAut_range hn hK σ hσ Fr hFr) ▸ ⟨x, rfl⟩, ?_⟩
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨b, hb, hz', rfl⟩ := (mem_langCube hn hK σ hσ Fr hFr).1 hz
    have hmem : g₂ * rootDiagUnit Tag.E6 b * g₂⁻¹ ∈ TwistedDiag.Rgrp Ω Fr := by
      have h := mul_mem (mul_mem hx hz') (inv_mem hx)
      rwa [show g₂ * g₁⁻¹ * (g₁ * rootDiagUnit Tag.E6 b * g₁⁻¹) * (g₂ * g₁⁻¹)⁻¹ =
        g₂ * rootDiagUnit Tag.E6 b * g₂⁻¹ by group] at h
    refine (mem_langCube hn hK σ hσ Fr hFr).2 ⟨b, hb, hmem, ?_⟩
    change Φ _ = Φ x * Φ _ * (Φ x)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    refine Subtype.ext ?_
    change g₂ * rootDiagUnit Tag.E6 b * g₂⁻¹ =
      g₂ * g₁⁻¹ * (g₁ * rootDiagUnit Tag.E6 b * g₁⁻¹) * (g₂ * g₁⁻¹)⁻¹
    group
  · intro hy
    obtain ⟨b, hb, hy', rfl⟩ := (mem_langCube hn hK σ hσ Fr hFr).1 hy
    have hmem : g₁ * rootDiagUnit Tag.E6 b * g₁⁻¹ ∈ TwistedDiag.Rgrp Ω Fr := by
      have h := mul_mem (mul_mem (inv_mem hx) hy') hx
      rwa [show (g₂ * g₁⁻¹)⁻¹ * (g₂ * rootDiagUnit Tag.E6 b * g₂⁻¹) * (g₂ * g₁⁻¹) =
        g₁ * rootDiagUnit Tag.E6 b * g₁⁻¹ by group] at h
    refine ⟨Φ ⟨_, hmem⟩, (mem_langCube hn hK σ hσ Fr hFr).2 ⟨b, hb, hmem, rfl⟩, ?_⟩
    change Φ x * Φ _ * (Φ x)⁻¹ = Φ _
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    refine Subtype.ext ?_
    change g₂ * g₁⁻¹ * (g₁ * rootDiagUnit Tag.E6 b * g₁⁻¹) * (g₂ * g₁⁻¹)⁻¹ =
      g₂ * rootDiagUnit Tag.E6 b * g₂⁻¹
    group

theorem rgrpConjAut_mem_range_conj {x : ModGL Tag.E6 Ω} (hx : x ∈ TwistedDiag.Rgrp Ω Fr)
    (hxC : x ∈ TwistedDiag.Cgrp K σ.toRingHom Ω) :
    rgrpConjAut hn hK σ hσ Fr hFr ⟨x, hx⟩ ∈
      (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) →*
        MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)).range := by
  obtain ⟨c, hc, hcx⟩ := hxC
  set c₀ : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := ⟨c, hc⟩ with hc₀
  have hcΓ : (c₀ : ModGL TwistTag.E6.tag K) ∈ RecipeExcLang.twInndiagGroup K σ :=
    RecipeExcLang.graphFixedRootGroup_le_twInndiag σ c₀.2
  have h1 : twInndiagEquivRgrp hn hK σ hσ Fr hFr ⟨c₀, hcΓ⟩ = ⟨x, hx⟩ := by
    refine Subtype.ext ?_
    change (baseChangeGL (algebraMap K Ω)) c = x
    exact hcx
  have hval : rgrpConjAut hn hK σ hσ Fr hFr ⟨x, hx⟩ = MulAut.conj c₀ := by
    rw [← h1, rgrpConjAut_apply_baseChange]
    exact RecipeExcLang.twConj_of_mem_C0 σ c₀
  exact ⟨c₀, hval.symm⟩

end Cube

section Rowley


theorem exists_cubeTorus_lang {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1) {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    {S : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))}
    (hS : IsElemAbelian 3 S) (hSI : S ≤ (RecipeExcLang.twConj K σ).range)
    (h5 : 3 ^ 5 ≤ Nat.card S) :
    ∃ g ∈ adjointGroup Tag.E6 Ω, g⁻¹ * twistE6 Ω Fr g = TwistedDiag.n0 Ω ∧
      S ≤ langCube hn hK σ hσ Fr hFr g := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  haveI : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hq0 : ((2 ^ n : ℕ) : Ω) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero Ω 2, zero_pow (by omega)]
  have h30 : (3 : Ω) ≠ 0 := three_ne_zero_of_dvd_card_add_one (ℓ := 2) hn h3
  obtain ⟨ζ, hζ, hζo⟩ := TwistedDiag.exists_cube_root (Ω := Ω) h30
  set Φ := rgrpConjAut hn hK σ hσ Fr hFr with hΦdef
  have hΦinj : Function.Injective Φ := rgrpConjAut_injective hn hK σ hσ Fr hFr
  have hΦrange : Φ.range = (RecipeExcLang.twConj K σ).range :=
    rgrpConjAut_range hn hK σ hσ Fr hFr
  obtain ⟨g₀, hg₀, hgn₀⟩ := exists_inv_mul_twistE6_eq (ℓ := 2) (f := n) hn hFr
    (canonicalRep_mem_adjointGroup (coxeterSystem Tag.E6) Ω twE6W0)
  have hgn₀' : g₀⁻¹ * twistE6 Ω Fr g₀ = TwistedDiag.n0 Ω := hgn₀
  let R := TwistedDiag.Rgrp Ω Fr
  let X : Subgroup (ModGL Tag.E6 Ω) := (S.comap Φ).map R.subtype
  have hXR : X ≤ R := Subgroup.map_subtype_le (S.comap Φ)
  have hSrange : S ≤ Φ.range := by rw [hΦrange]; exact hSI
  have hXcard : Nat.card X = Nat.card S := by
    change Nat.card ↥(Subgroup.map R.subtype (Subgroup.comap Φ S)) = Nat.card ↥S
    have h1 : Nat.card ((S.comap Φ).map Φ) = Nat.card (S.comap Φ) :=
      Subgroup.card_map_of_injective hΦinj
    have h2 : (S.comap Φ).map Φ = S := Subgroup.map_comap_eq_self hSrange
    have h3' : Nat.card (S.comap Φ) = Nat.card S := by rw [← h1, h2]
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective R), h3']
  have hXel : IsElemAbelian 3 X := (hS.comap hΦinj).map R.subtype
  have h5X : 3 ^ 5 ≤ Nat.card X := by rw [hXcard]; exact h5
  obtain ⟨k, hkθ, r, hrR, hX₁le⟩ := exists_conj_le_xHat (ℓ := 2) hn K hK
    σ.toRingHom hσ h3 Ω Fr hFr hg₀ hgn₀' hXR hXel.isPGroup
  let c₁ : ModGL Tag.E6 Ω := k * g₀⁻¹ * r
  let E : Subgroup (ModGL Tag.E6 Ω) := X.map (MulAut.conj c₁).toMonoidHom
  have hEel : IsElemAbelian 3 E := hXel.map (MulAut.conj c₁).toMonoidHom
  have hEX : E ≤ xHat Tag.E6 Ω modelHomE6.range := hX₁le.trans inf_le_left
  have hEθ : E ≤ TwistedDiag.thetaFixed Fr := hX₁le.trans inf_le_right
  have hEcard : 3 ^ 5 ≤ Nat.card E := by
    change 3 ^ 5 ≤ Nat.card ↥(Subgroup.map (MulAut.conj c₁).toMonoidHom X)
    rw [Subgroup.card_map_of_injective (MulAut.conj c₁).injective]
    exact h5X
  obtain ⟨z, hzθ, hzconj⟩ : ∃ z ∈ TwistedDiag.thetaFixed Fr,
      ∀ e ∈ E, ∃ v, z * e * z⁻¹ = rootDiagUnit Tag.E6 (zetaVec ζ hζ v) := by
    rcases torus_or_cyclic (ζ := ζ) hζo hζ hEel hEX hEcard with htor | ⟨i, hEXi⟩
    · exact ⟨1, one_mem _, fun e he => by
        obtain ⟨v, hv⟩ := htor e he
        exact ⟨v, by rw [one_mul, inv_one, mul_one, hv]⟩⟩
    · exact exists_thetaFixed_conj_of_cyclic a2BlockTwoInput_holds hFr hq0 h3 hζ hζo i hEel
        hEθ hEXi
  let g : ModGL Tag.E6 Ω := r⁻¹ * g₀ * k⁻¹ * z⁻¹
  have hkG : k ∈ adjointGroup Tag.E6 Ω := ((TwistedDiag.mem_thetaFixed Fr).1 hkθ).1
  have hzG : z ∈ adjointGroup Tag.E6 Ω := ((TwistedDiag.mem_thetaFixed Fr).1 hzθ).1
  have hrG : r ∈ adjointGroup Tag.E6 Ω := ((TwistedDiag.mem_Rgrp Fr).1 hrR).1
  have hgG : g ∈ adjointGroup Tag.E6 Ω :=
    mul_mem (mul_mem (mul_mem (inv_mem hrG) hg₀) (inv_mem hkG)) (inv_mem hzG)
  have hFr_r : twistE6 Ω Fr r = r := ((TwistedDiag.mem_Rgrp Fr).1 hrR).2
  have hFg₀ : twistE6 Ω Fr g₀ = g₀ * TwistedDiag.n0 Ω := by
    rw [← hgn₀', mul_inv_cancel_left]
  have hgn : g⁻¹ * twistE6 Ω Fr g = TwistedDiag.n0 Ω := by
    change (r⁻¹ * g₀ * k⁻¹ * z⁻¹)⁻¹ * twistE6 Ω Fr (r⁻¹ * g₀ * k⁻¹ * z⁻¹) = TwistedDiag.n0 Ω
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_inv, hFr_r, hFg₀,
      twistE6_of_mem_thetaFixed Fr hkθ, twistE6_of_mem_thetaFixed Fr hzθ]
    group
  refine ⟨g, hgG, hgn, ?_⟩
  intro s hs
  obtain ⟨x, hxeq⟩ := MonoidHom.mem_range.1 (hSrange hs)
  have hxX : (x : ModGL Tag.E6 Ω) ∈ X :=
    Subgroup.mem_map.2 ⟨x, by rw [Subgroup.mem_comap, hxeq]; exact hs, rfl⟩
  have hxE : c₁ * x * c₁⁻¹ ∈ E := ⟨x, hxX, rfl⟩
  obtain ⟨v, hv⟩ := hzconj _ hxE
  have hxg : (x : ModGL Tag.E6 Ω) =
      g * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * g⁻¹ := by
    rw [← hv]
    change (x : ModGL Tag.E6 Ω) = r⁻¹ * g₀ * k⁻¹ * z⁻¹ * (z * (k * g₀⁻¹ * r * x *
      (k * g₀⁻¹ * r)⁻¹) * z⁻¹) * (r⁻¹ * g₀ * k⁻¹ * z⁻¹)⁻¹
    group
  have hb : ∀ i, zetaVec ζ hζ v i ^ 3 = 1 := by
    intro i
    rw [zetaVec_apply, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  refine (mem_langCube hn hK σ hσ Fr hFr).2 ⟨zetaVec ζ hζ v, hb, hxg ▸ x.2, ?_⟩
  rw [← hxeq]
  congr 1
  exact Subtype.ext hxg.symm

theorem exists_eq_langCube {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1) {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    {Y : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))}
    (hY : IsElemAbelian 3 Y) (hYI : Y ≤ (RecipeExcLang.twConj K σ).range)
    (hYc : Nat.card Y = 3 ^ 6) :
    ∃ g ∈ adjointGroup Tag.E6 Ω, g⁻¹ * twistE6 Ω Fr g = TwistedDiag.n0 Ω ∧
      Y = langCube hn hK σ hσ Fr hFr g := by
  obtain ⟨g, hg, hgn, hle⟩ := exists_cubeTorus_lang hn hK σ hσ h3 Fr hFr hY hYI
    (by rw [hYc]; norm_num)
  have hc := card_langCube hn hK σ hσ Fr hFr h3 hg hgn
  haveI : Finite ↥(langCube hn hK σ hσ Fr hFr g) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  exact ⟨g, hg, hgn, Subgroup.eq_of_le_of_card_ge hle (by rw [hc, hYc])⟩

theorem exists_conj_of_card {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1)
    {Y₁ Y₂ : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))}
    (hY₁ : IsElemAbelian 3 Y₁) (hY₁I : Y₁ ≤ (RecipeExcLang.twConj K σ).range)
    (hY₁c : Nat.card Y₁ = 3 ^ 6) (hY₂ : IsElemAbelian 3 Y₂)
    (hY₂I : Y₂ ≤ (RecipeExcLang.twConj K σ).range) (hY₂c : Nat.card Y₂ = 3 ^ 6) :
    ∃ β ∈ (RecipeExcLang.twConj K σ).range, Y₁.map (MulAut.conj β).toMonoidHom = Y₂ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hFr : ∀ c, iterateFrobenius (AlgebraicClosure K) 2 n c = c ^ 2 ^ n :=
    fun c => iterateFrobenius_def 2 n c
  obtain ⟨g₁, hg₁, hgn₁, rfl⟩ := exists_eq_langCube hn hK σ hσ h3 _ hFr hY₁ hY₁I hY₁c
  obtain ⟨g₂, hg₂, hgn₂, rfl⟩ := exists_eq_langCube hn hK σ hσ h3 _ hFr hY₂ hY₂I hY₂c
  exact exists_conj_langCube hn hK σ hσ _ hFr hg₁ hgn₁ hg₂ hgn₂

theorem exists_cubeTorus {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1)
    {S : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))}
    (hS : IsElemAbelian 3 S) (hSI : S ≤ (RecipeExcLang.twConj K σ).range)
    (h5 : 3 ^ 5 ≤ Nat.card S) :
    ∃ Y : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)),
      S ≤ Y ∧ Y ≤ (RecipeExcLang.twConj K σ).range ∧ IsElemAbelian 3 Y ∧ Nat.card Y = 3 ^ 6 ∧
      (9 ∣ 2 ^ n + 1 →
        Y ≤ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) →*
          MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)).range ∧
        ∃ W : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)),
          (∀ w ∈ W, ∀ w' ∈ W, w * w' = w' * w) ∧ (∀ w ∈ W, w ^ 9 = 1) ∧
          ∀ y ∈ Y, ∃ w ∈ W, w ^ 3 = y) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  set Ω := AlgebraicClosure K
  haveI : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  set Fr : Ω →+* Ω := iterateFrobenius Ω 2 n with hFrdef
  have hFr : ∀ c, Fr c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  set Φ := rgrpConjAut hn hK σ hσ Fr hFr with hΦdef
  obtain ⟨g, hg, hgn, hSY⟩ := exists_cubeTorus_lang hn hK σ hσ h3 Fr hFr hS hSI h5
  refine ⟨langCube hn hK σ hσ Fr hFr g, hSY, langCube_le_range hn hK σ hσ Fr hFr g,
    isElemAbelian_langCube hn hK σ hσ Fr hFr g, card_langCube hn hK σ hσ Fr hFr h3 hg hgn,
    fun h9 => ⟨?_, ?_⟩⟩
  ·
    intro y hy
    obtain ⟨b, hb, hx, rfl⟩ := (mem_langCube hn hK σ hσ Fr hFr).1 hy
    have h30 : (3 : Ω) ≠ 0 := three_ne_zero_of_dvd_card_add_one (ℓ := 2) hn h3
    obtain ⟨ζ, hζ, hζo⟩ := TwistedDiag.exists_cube_root (Ω := Ω) h30
    have hb3 : b ^ 3 = 1 := by funext i; exact hb i
    obtain ⟨v, hv⟩ := exists_zetaVec_eq (τ := Tag.E6) (p := 3) hζo hζ hb3
    have hC : g * rootDiagUnit Tag.E6 b * g⁻¹ ∈ TwistedDiag.Cgrp K σ.toRingHom Ω := by
      rw [← hv]
      exact conj_rootDiagUnit_mem_Cgrp_of_nine_dvd (ℓ := 2) hn K hK σ.toRingHom hσ h9 Ω Fr
        hFr hg hgn hζ v
    exact rgrpConjAut_mem_range_conj hn hK σ hσ Fr hFr hx hC
  ·
    have hR9 : ∀ c : Fin Tag.E6.rank → Ωˣ, (∀ i, c i ^ 9 = 1) →
        g * rootDiagUnit Tag.E6 c * g⁻¹ ∈ TwistedDiag.Rgrp Ω Fr := by
      intro c hc
      refine (TwistedDiag.mem_thetaFixed_iff_conj Fr hg hgn _).1 ?_
      rw [TwistedDiag.mem_thetaFixed]
      refine ⟨torusGroup_le_adjointGroup_E6 (rootDiagUnit_mem_torusGroup c),
        (TwistedDiag.theta_rootDiagUnit_eq_iff Fr hFr c).2 fun i => ?_⟩
      obtain ⟨m, hm⟩ := h9
      rw [hm, pow_mul, hc i, one_pow]
    let D9 : Subgroup (ModGL Tag.E6 Ω) :=
      ((powMonoidHom 9 : (Fin Tag.E6.rank → Ωˣ) →* (Fin Tag.E6.rank → Ωˣ)).ker).map
        (rootDiagUnitHom Tag.E6 Ω)
    have hD9 : ∀ x, x ∈ D9 ↔ ∃ c : Fin Tag.E6.rank → Ωˣ, (∀ i, c i ^ 9 = 1) ∧
        rootDiagUnit Tag.E6 c = x := by
      intro x
      constructor
      · rintro ⟨c, hc, rfl⟩
        have hc' : c ^ 9 = 1 := hc
        exact ⟨c, fun i => by simpa using congrFun hc' i, rfl⟩
      · rintro ⟨c, hc, rfl⟩
        exact ⟨c, (MonoidHom.mem_ker).2 (funext fun i => by simpa using hc i), rfl⟩
    let w : ∀ c : Fin Tag.E6.rank → Ωˣ, (∀ i, c i ^ 9 = 1) →
        MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :=
      fun c hc => Φ ⟨_, hR9 c hc⟩
    let W : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :=
      ((D9.map (MulAut.conj g).toMonoidHom).subgroupOf (TwistedDiag.Rgrp Ω Fr)).map Φ
    have hmemW : ∀ u ∈ W, ∃ c, ∃ hc : ∀ i, c i ^ 9 = 1, w c hc = u := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨_, hd, hdx⟩ := Subgroup.mem_subgroupOf.1 hx
      obtain ⟨c, hc, rfl⟩ := (hD9 _).1 hd
      refine ⟨c, hc, ?_⟩
      change Φ _ = Φ x
      congr 1
      exact Subtype.ext hdx
    have hwW : ∀ c (hc : ∀ i, c i ^ 9 = 1), w c hc ∈ W := fun c hc =>
      ⟨⟨_, hR9 c hc⟩, Subgroup.mem_subgroupOf.2 ⟨_, (hD9 _).2 ⟨c, hc, rfl⟩, rfl⟩, rfl⟩
    have hwpow : ∀ c (hc : ∀ i, c i ^ 9 = 1) (m : ℕ) (hcm : ∀ i, (c ^ m) i ^ 9 = 1),
        w c hc ^ m = w (c ^ m) hcm := by
      intro c hc m hcm
      change Φ _ ^ m = Φ _
      rw [← map_pow]
      congr 1
      refine Subtype.ext ?_
      change (g * rootDiagUnit Tag.E6 c * g⁻¹) ^ m = g * rootDiagUnit Tag.E6 (c ^ m) * g⁻¹
      rw [conj_pow, rootDiagUnit_pow]
    refine ⟨W, ?_, ?_, ?_⟩
    · intro u hu u' hu'
      obtain ⟨c, hc, rfl⟩ := hmemW u hu
      obtain ⟨c', hc', rfl⟩ := hmemW u' hu'
      change Φ _ * Φ _ = Φ _ * Φ _
      rw [← map_mul, ← map_mul]
      congr 1
      refine Subtype.ext ?_
      change g * rootDiagUnit Tag.E6 c * g⁻¹ * (g * rootDiagUnit Tag.E6 c' * g⁻¹) =
        g * rootDiagUnit Tag.E6 c' * g⁻¹ * (g * rootDiagUnit Tag.E6 c * g⁻¹)
      rw [show g * rootDiagUnit Tag.E6 c * g⁻¹ * (g * rootDiagUnit Tag.E6 c' * g⁻¹) =
          g * (rootDiagUnit Tag.E6 c * rootDiagUnit Tag.E6 c') * g⁻¹ by group,
        show g * rootDiagUnit Tag.E6 c' * g⁻¹ * (g * rootDiagUnit Tag.E6 c * g⁻¹) =
          g * (rootDiagUnit Tag.E6 c' * rootDiagUnit Tag.E6 c) * g⁻¹ by group,
        ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm c c']
    · intro u hu
      obtain ⟨c, hc, rfl⟩ := hmemW u hu
      have hc9 : ∀ i, (c ^ 9) i ^ 9 = 1 := fun i => by
        rw [Pi.pow_apply, hc i, one_pow]
      rw [hwpow c hc 9 hc9]
      have h1 : c ^ 9 = 1 := funext fun i => by rw [Pi.pow_apply, hc i]; rfl
      change Φ _ = 1
      rw [← map_one Φ]
      congr 1
      refine Subtype.ext ?_
      change g * rootDiagUnit Tag.E6 (c ^ 9) * g⁻¹ = 1
      rw [h1, rootDiagUnit_one, mul_one, mul_inv_cancel]
    · intro y hy
      obtain ⟨b, hb, hx, rfl⟩ := (mem_langCube hn hK σ hσ Fr hFr).1 hy
      choose c hc9 hc3 using fun i =>
        exists_pow_nine_eq_one_and_pow_three_eq (Ω := Ω) (hb i)
      have hc3' : ∀ i, (c ^ 3) i ^ 9 = 1 := fun i => by
        rw [Pi.pow_apply, hc3 i, show (9 : ℕ) = 3 * 3 by norm_num, pow_mul, hb i, one_pow]
      refine ⟨w c hc9, hwW c hc9, ?_⟩
      rw [hwpow c hc9 3 hc3']
      change Φ _ = Φ _
      congr 1
      refine Subtype.ext ?_
      change g * rootDiagUnit Tag.E6 (c ^ 3) * g⁻¹ = g * rootDiagUnit Tag.E6 b * g⁻¹
      rw [show c ^ 3 = b from funext fun i => by rw [Pi.pow_apply, hc3 i]]

end Rowley

end CFSG.StandardType.TwE6DD2
