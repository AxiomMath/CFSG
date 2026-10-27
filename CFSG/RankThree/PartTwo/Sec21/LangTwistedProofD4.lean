module

public import CFSG.RankThree.PartTwo.Sec8.Item8ModelProofD4
public import CFSG.RankThree.PartOne.KGD.D4Frame
public import CFSG.LieType.AlgebraicGroups.E6GraphCentralizerLangCurves
public import CFSG.LieType.AlgebraicGroups.ConnectedToralLangFrobenius
public import CFSG.LieType.Chevalley.E6GraphRootSL2Basic

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups

@[expose] def d4TrialityY0 (L : Type)
    [Field L] :
    ModGL TwistTag.D4.tag L :=
  xUnit TwistTag.D4.tag L 2 1 * yUnit TwistTag.D4.tag L 2 1

@[expose] def D4TrialityGeomClasses :
    Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2],
    (letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L) →
    ∀ x ∈ adjointGroup TwistTag.D4.tag L, (x * (diagramMap TwistTag.D4 L)⁻¹) ^ 3 = 1 →
      ∃ g ∈ adjointGroup TwistTag.D4.tag L,
        g * (x * (diagramMap TwistTag.D4 L)⁻¹) * g⁻¹ = (diagramMap TwistTag.D4 L)⁻¹ ∨
          g * (x * (diagramMap TwistTag.D4 L)⁻¹) * g⁻¹ =
            d4TrialityY0 L * (diagramMap TwistTag.D4 L)⁻¹

@[expose] def D4DiagramCentIrred :
    Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2],
    IsPointIrreducible L (transportPoints (modGLPoint TwistTag.D4.tag L)
      (graphCentralizer TwistTag.D4.tag L (diagramMap TwistTag.D4 L)⁻¹))

@[expose] def D4SecondCentIrred :
    Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2],
    IsPointIrreducible L (transportPoints (modGLPoint TwistTag.D4.tag L)
      (graphCentralizer TwistTag.D4.tag L (d4TrialityY0 L * (diagramMap TwistTag.D4 L)⁻¹)))

namespace LangTwistedProof


section Y0

variable {K : Type} [Field K]

theorem d4TrialityY0_eq_rankOneHom :
    d4TrialityY0 K = rankOneHom TwistTag.D4 K 2 (uSL 1 * vSL 1) := by
  rw [map_mul, rankOneHom_uSL, rankOneHom_vSL]
  rfl

theorem d4TrialityY0_pow_three
    (h2 : (2 : K) = 0) : d4TrialityY0 K ^ 3 = 1 := by
  rw [d4TrialityY0_eq_rankOneHom, ← map_pow, E6GraphRootSL2.uSL_mul_vSL_pow_three h2, map_one]

theorem twistHom_d4TrialityY0 (σ : K →+* K) :
    twistHom TwistTag.D4 K σ (d4TrialityY0 K) = d4TrialityY0 K := by
  rw [d4TrialityY0, map_mul, twistHom_xUnit, twistHom_yUnit, map_one]
  rfl

theorem entrywise_d4TrialityY0 (σ : K →+* K) :
    Units.map (entrywiseHom σ) (d4TrialityY0 K) = d4TrialityY0 K := by
  refine Units.ext ?_
  rw [d4TrialityY0, map_mul, Units.val_mul, Units.coe_map, Units.coe_map]
  change entrywise σ (xOp TwistTag.D4.tag K 2 1) * entrywise σ (yOp TwistTag.D4.tag K 2 1) = _
  rw [entrywise_xOp, entrywise_yOp, map_one]
  rfl

theorem d4TrialityY0_mem
    (σ : K →+* K) : d4TrialityY0 K ∈ graphFixedRootGroup TwistTag.D4 K σ := by
  have hx : xUnit TwistTag.D4.tag K 2 1 ∈ graphFixedPosUnipotent TwistTag.D4 K σ := by
    refine Subgroup.mem_inf.2 ⟨xUnit_mem_posUnipotent 2 1, ?_⟩
    refine (mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨xUnit_mem_adjointGroup 2 1, ?_⟩
    rw [twistHom_xUnit, map_one]
    rfl
  have hy : yUnit TwistTag.D4.tag K 2 1 ∈ graphFixedNegUnipotent TwistTag.D4 K σ := by
    refine Subgroup.mem_inf.2 ⟨yUnit_mem_negUnipotent 2 1, ?_⟩
    refine (mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨yUnit_mem_adjointGroup 2 1, ?_⟩
    rw [twistHom_yUnit, map_one]
    rfl
  exact mul_mem (graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _ hx)
    (graphFixedNegUnipotent_le_graphFixedRootGroup _ _ _ hy)

variable {L : Type} [Field L]

theorem baseChangeGL_d4TrialityY0
    (ι : K →+* L) :
    baseChangeGL ι (d4TrialityY0 K) = d4TrialityY0 L := by
  rw [d4TrialityY0, map_mul, baseChangeGL_xUnit, baseChangeGL_yUnit, map_one]
  rfl

end Y0

theorem conj_mul_pow_three {X : Type*} [Group X] (α : MulAut X) (hα : α ^ 3 = 1) (g : X) :
    (MulAut.conj g * α) ^ 3 = MulAut.conj (g * α g * α (α g)) := by
  have h1 : α * MulAut.conj g = MulAut.conj (α g) * α := by
    ext u
    simp [MulAut.conj_apply, map_mul, map_inv]
  have h3 : α * α * α = 1 := by rw [← hα, pow_three, mul_assoc]
  calc (MulAut.conj g * α) ^ 3 = MulAut.conj g * (α * MulAut.conj g) * (α * MulAut.conj g) * α :=
        by rw [pow_three]; group
    _ = MulAut.conj g * (MulAut.conj (α g) * α) * (MulAut.conj (α g) * α) * α := by rw [h1]
    _ = MulAut.conj g * MulAut.conj (α g) * (α * MulAut.conj (α g)) * (α * α) := by group
    _ = MulAut.conj g * MulAut.conj (α g) * (MulAut.conj (α (α g)) * α) * (α * α) := by
        rw [show α * MulAut.conj (α g) = MulAut.conj (α (α g)) * α by
          ext u; simp [MulAut.conj_apply, map_mul, map_inv]]
    _ = MulAut.conj g * MulAut.conj (α g) * MulAut.conj (α (α g)) * (α * α * α) := by group
    _ = MulAut.conj (g * α g * α (α g)) := by rw [h3, mul_one, map_mul, map_mul]

theorem norm_eq_one_of_pow_three {X : Type*} [Group X] (hZ : Subgroup.center X = ⊥)
    (α : MulAut X) (hα : α ^ 3 = 1) (g : X) (hg : (MulAut.conj g * α) ^ 3 = 1) :
    g * α g * α (α g) = 1 := by
  rw [conj_mul_pow_three α hα] at hg
  have hc : g * α g * α (α g) ∈ Subgroup.center X := by
    refine Subgroup.mem_center_iff.2 fun u => ?_
    have h1 := congrArg (fun φ : MulAut X => φ u) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc u * (g * α g * α (α g)) =
        (g * α g * α (α g)) * u * (g * α g * α (α g))⁻¹ * (g * α g * α (α g)) := by rw [h1]
      _ = (g * α g * α (α g)) * u := by group
  rw [hZ] at hc
  exact Subgroup.mem_bot.1 hc

theorem isAlgebraic_zmod_algebraicClosure (K : Type) [Field K] [Finite K] (p : ℕ)
    [Fact p.Prime] [CharP (AlgebraicClosure K) p] :
    letI := ZMod.algebra (AlgebraicClosure K) p
    Algebra.IsAlgebraic (ZMod p) (AlgebraicClosure K) := by
  let _ : Algebra (ZMod p) (AlgebraicClosure K) := ZMod.algebra (AlgebraicClosure K) p
  refine ⟨fun y => ?_⟩
  obtain ⟨E, hEf, hyE, -⟩ :=
    exists_finite_subfield_of_finset (K := K) ({y} : Finset (AlgebraicClosure K))
  have hy : y ∈ E := hyE (Finset.mem_coe.2 (Finset.mem_singleton_self y))
  have : Fintype E := Fintype.ofFinite E
  have hpow : y ^ Fintype.card E = y :=
    congrArg Subtype.val (FiniteField.pow_card (⟨y, hy⟩ : E))
  refine ⟨Polynomial.X ^ Fintype.card E - Polynomial.X,
    FiniteField.X_pow_card_sub_X_ne_zero (ZMod p) Fintype.one_lt_card, ?_⟩
  rw [map_sub, map_pow, Polynomial.aeval_X, hpow, sub_self]

section Lang

variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]

theorem frobTwistGL_mem_adjointGroup
    [Fact (Nat.Prime 2)] (e : ℕ)
    {g : ModGL TwistTag.D4.tag L} (hg : g ∈ adjointGroup TwistTag.D4.tag L) :
    frobTwistGL TwistTag.D4.tag L 2 e (diagramMap TwistTag.D4 L) g ∈
      adjointGroup TwistTag.D4.tag L := by
  have hQ := conj_mem_adjointGroup_of_map_eq (map_conj_diagramMap_zpow TwistTag.D4 L 1)
  rw [zpow_one] at hQ
  exact hQ _ (entrywiseFrobGL_mem 2 e hg)

theorem exists_inv_mul_frob_of_irred
    [Fact (Nat.Prime 2)] {e : ℕ}
    (he : 1 ≤ e) {A : ModGL TwistTag.D4.tag L}
    (hA : frobTwistGL TwistTag.D4.tag L 2 e (diagramMap TwistTag.D4 L) A = A)
    (hirr : IsPointIrreducible L (transportPoints (modGLPoint TwistTag.D4.tag L)
      (graphCentralizer TwistTag.D4.tag L A))) :
    ∀ c ∈ graphCentralizer TwistTag.D4.tag L A, ∃ z ∈ graphCentralizer TwistTag.D4.tag L A,
      z⁻¹ * frobTwistGL TwistTag.D4.tag L 2 e (diagramMap TwistTag.D4 L) z = c := by
  obtain ⟨hZ, -, -, -⟩ := graphCentralizer_realization A hirr
  have hFZ : ∀ g ∈ graphCentralizer TwistTag.D4.tag L A,
      frobTwistGL TwistTag.D4.tag L 2 e (diagramMap TwistTag.D4 L) g ∈
        graphCentralizer TwistTag.D4.tag L A := by
    intro g hg
    obtain ⟨hgG, hgc⟩ := Subgroup.mem_inf.1 hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hgc
    refine Subgroup.mem_inf.2 ⟨frobTwistGL_mem_adjointGroup e hgG, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    conv_lhs => rw [← hA]
    conv_rhs => rw [← hA]
    rw [← map_mul, ← map_mul, hgc]
  obtain ⟨-, -, -, hlang⟩ := exists_frobTwist_restriction 2 hZ he (diagramMap TwistTag.D4 L) hFZ
  exact hlang

theorem exists_fixed_conj_of_lang
    [Fact (Nat.Prime 2)] {e : ℕ}
    (he : 1 ≤ e) {A s x : ModGL TwistTag.D4.tag L}
    (hA : frobTwistGL TwistTag.D4.tag L 2 e (diagramMap TwistTag.D4 L) A = A)
    (hs : frobTwistGL TwistTag.D4.tag L 2 e (diagramMap TwistTag.D4 L) s = s)
    (hirr : IsPointIrreducible L (transportPoints (modGLPoint TwistTag.D4.tag L)
      (graphCentralizer TwistTag.D4.tag L A)))
    (hx : x ∈ adjointGroup TwistTag.D4.tag L) (hxs : x * s * x⁻¹ = A) :
    ∃ y ∈ adjointGroup TwistTag.D4.tag L,
      frobTwistGL TwistTag.D4.tag L 2 e (diagramMap TwistTag.D4 L) y = y ∧ y * s * y⁻¹ = A := by
  set F := frobTwistGL TwistTag.D4.tag L 2 e (diagramMap TwistTag.D4 L) with hFdef
  have hFx : F x * s * (F x)⁻¹ = A := by
    have h := congrArg F hxs
    rwa [map_mul, map_mul, map_inv, hs, hA] at h
  have hcZ : x * (F x)⁻¹ ∈ graphCentralizer TwistTag.D4.tag L A := by
    refine Subgroup.mem_inf.2 ⟨mul_mem hx (inv_mem (frobTwistGL_mem_adjointGroup e hx)), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * (F x)⁻¹ * A = x * ((F x)⁻¹ * A * F x) * (F x)⁻¹ := by group
      _ = x * s * x⁻¹ * (x * (F x)⁻¹) := by rw [← hFx]; group
      _ = A * (x * (F x)⁻¹) := by rw [hxs]
  obtain ⟨z, hzZ, hzc⟩ := exists_inv_mul_frob_of_irred he hA hirr _ hcZ
  have hzc' : z⁻¹ * F z = x * (F x)⁻¹ := hzc
  obtain ⟨hzG, hzA⟩ := Subgroup.mem_inf.1 hzZ
  rw [Subgroup.mem_centralizer_singleton_iff] at hzA
  refine ⟨z * x, mul_mem hzG hx, ?_, ?_⟩
  · have hFz : F z = z * (x * (F x)⁻¹) := by rw [← hzc']; group
    rw [map_mul, hFz]
    group
  · calc z * x * s * (z * x)⁻¹ = z * (x * s * x⁻¹) * z⁻¹ := by group
      _ = A := by rw [hxs, hzA]; group

end Lang

end LangTwistedProof

open LangTwistedProof


theorem exists_conj_eq_of_geom (hG : D4TrialityGeomClasses) (hP : D4DiagramCentIrred)
    (hY : D4SecondCentIrred) {n : ℕ} {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hK : Nat.card K = (2 ^ n) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hg3 : (MulAut.conj g * fieldActor σ σ) ^ 3 = 1) :
    ∃ (h y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      ((y : ModGL TwistTag.D4.tag K) = 1 ∨ (y : ModGL TwistTag.D4.tag K) = d4TrialityY0 K) ∧
        MulAut.conj g * fieldActor σ σ =
          MulAut.conj h⁻¹ * (MulAut.conj y * fieldActor σ σ) * (MulAut.conj h⁻¹)⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · have : 2 ≤ Nat.card K := Finite.one_lt_card
      rw [hK] at this
      norm_num at this
    · exact h
  have : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := n * 3) (by
      rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have h2K : (2 : K) = 0 := CharP.cast_eq_zero K 2
  set σ₀ := fieldActor (t := TwistTag.D4) σ σ with hσ₀def
  set P := diagramMap TwistTag.D4 K with hPdef
  have hσ₀ : ∀ x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      ((σ₀ x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) =
        P⁻¹ * x * P := by
    intro x
    have hx := ((mem_twistedFixedGroup_iff_twistHom _ _ _).1
      (graphFixedRootGroup_le _ _ _ x.2)).2
    rw [twistHom_apply] at hx
    rw [coe_fieldActor]
    calc Units.map (entrywiseHom σ.toRingHom) (x : ModGL TwistTag.D4.tag K) =
        P⁻¹ * (P * Units.map (entrywiseHom σ.toRingHom) (x : ModGL TwistTag.D4.tag K) * P⁻¹) *
          P := by group
      _ = P⁻¹ * x * P := by rw [hx]
  have hσ3 : σ ^ 3 = 1 := by
    ext c
    rw [pow_three, RingAut.mul_apply, RingAut.mul_apply]
    exact ringEquiv_cube_apply_eq hK hσ c
  have hσ₀3 : σ₀ ^ 3 = 1 := by
    have h1 : fieldActor (t := TwistTag.D4) σ (σ ^ 3) = fieldActor σ σ ^ 3 :=
      map_pow (fieldActorHom (t := TwistTag.D4) σ) σ 3
    rw [hσ₀def, ← h1, hσ3, fieldActor_one]
  have hN := norm_eq_one_of_pow_three (exceptional_fixed_center_trivial TwistTag.D4 K σ) σ₀ hσ₀3
    g hg3
  have hP3 : P ^ 3 = 1 := diagramMap_pow_order TwistTag.D4 K
  have hgP : ((g : ModGL TwistTag.D4.tag K) * P⁻¹) ^ 3 = 1 := by
    have h1 := congrArg (fun x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom =>
      (x : ModGL TwistTag.D4.tag K)) hN
    simp only [Subgroup.coe_mul, Subgroup.coe_one] at h1
    rw [hσ₀ (σ₀ g), hσ₀ g] at h1
    have hP3' : P⁻¹ * P⁻¹ * P⁻¹ = 1 := by
      rw [← mul_inv_rev, ← mul_inv_rev, ← pow_three, hP3, inv_one]
    calc ((g : ModGL TwistTag.D4.tag K) * P⁻¹) ^ 3 =
        g * (P⁻¹ * g * P) * (P⁻¹ * (P⁻¹ * g * P) * P) * (P⁻¹ * P⁻¹ * P⁻¹) := by
          rw [pow_three]; group
      _ = 1 := by rw [h1, hP3', mul_one]
  set L := AlgebraicClosure K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have halg := isAlgebraic_zmod_algebraicClosure K 2
  set ι := algebraMap K L with hιdef
  set PL := diagramMap TwistTag.D4 L with hPLdef
  have hιP : baseChangeGL ι P = PL := baseChangeGL_diagramMap ι TwistTag.D4
  set Fr : L →+* L := iterateFrobenius L 2 n with hFrdef
  have hFr : ∀ c, Fr c = c ^ (2 ^ n) := fun c => iterateFrobenius_def 2 n c
  set F := frobTwistGL TwistTag.D4.tag L 2 n PL with hFdef
  have hFtw : ∀ u, F u = twistHom TwistTag.D4 L Fr u := fun u => rfl
  have hcomm : ι.comp σ.toRingHom = Fr.comp ι := by
    ext c
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [hFr, hσ, map_pow]
  set gL := CFSG.RankThree.PartOne.KGD.triEmb K σ L g with hgLdef
  have hgLC : gL ∈ adjointGroup TwistTag.D4.tag L :=
    CFSG.RankThree.PartOne.KGD.triEmb_mem_adjointGroup g
  have hgL3 : (gL * PL⁻¹) ^ 3 = 1 := by
    have h := congrArg (baseChangeGL ι) hgP
    rwa [map_pow, map_mul, map_inv, hιP, map_one] at h
  have hFgL : F gL = gL := by
    rw [hFtw]
    exact CFSG.RankThree.PartOne.KGD.triEmb_fixed Fr hcomm g
  have hFPL : F PL = PL := by
    rw [hFdef, frobTwistGL_apply]
    have h := entrywiseFrobGL_diagramMap_zpow TwistTag.D4 (L := L) 2 n 1
    rw [zpow_one] at h
    rw [h]
    exact mul_inv_cancel_right PL PL
  have hFPLi : F PL⁻¹ = PL⁻¹ := by rw [map_inv, hFPL]
  have hFs : F (gL * PL⁻¹) = gL * PL⁻¹ := by rw [map_mul, hFgL, hFPLi]
  have hFY : F (d4TrialityY0 L) = d4TrialityY0 L := by
    rw [hFtw]
    exact twistHom_d4TrialityY0 Fr
  obtain ⟨x, hxC, hx⟩ := hG L halg gL hgLC hgL3
  have hrange := CFSG.RankThree.PartOne.KGD.triEmb_range (σ := σ) (L := L) Nat.prime_two hn hK
    hσ Fr hFr
  have key : ∀ (A : ModGL TwistTag.D4.tag K), F (baseChangeGL ι A) = baseChangeGL ι A →
      IsPointIrreducible L (transportPoints (modGLPoint TwistTag.D4.tag L)
        (graphCentralizer TwistTag.D4.tag L (baseChangeGL ι A))) →
      x * (gL * PL⁻¹) * x⁻¹ = baseChangeGL ι A →
      ∃ h : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (h : ModGL TwistTag.D4.tag K) * (g * P⁻¹) * (h : ModGL TwistTag.D4.tag K)⁻¹ = A := by
    intro A hFA hirr hxA
    obtain ⟨y, hyC, hFy, hyA⟩ := exists_fixed_conj_of_lang hn hFA hFs hirr hxC hxA
    have hymem : y ∈ (CFSG.RankThree.PartOne.KGD.triEmb K σ L).range := by
      rw [hrange]
      exact Subgroup.mem_inf.2 ⟨hyC, hFy⟩
    obtain ⟨h, rfl⟩ := hymem
    refine ⟨h, baseChangeGL_injective ι ?_⟩
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hιP]
    exact hyA
  have hιY := baseChangeGL_d4TrialityY0 (K := K) ι
  rcases hx with hx | hx
  ·
    have hA : x * (gL * PL⁻¹) * x⁻¹ = baseChangeGL ι P⁻¹ := by rw [map_inv, hιP]; exact hx
    obtain ⟨h, hh⟩ := key P⁻¹ (by rw [map_inv, hιP]; exact hFPLi)
      (by rw [map_inv, hιP]; exact hP L) hA
    refine ⟨h, 1, Or.inl rfl, ?_⟩
    have hgeq : g = h⁻¹ * σ₀ h := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hσ₀ h]
      calc (g : ModGL TwistTag.D4.tag K) =
          (h : ModGL TwistTag.D4.tag K)⁻¹ *
            ((h : ModGL TwistTag.D4.tag K) * (g * P⁻¹) * (h : ModGL TwistTag.D4.tag K)⁻¹) *
              (h : ModGL TwistTag.D4.tag K) * P := by group
        _ = _ := by rw [hh]; group
    rw [hgeq, map_one, one_mul, map_mul, mul_assoc,
      show MulAut.conj (σ₀ h) * σ₀ = σ₀ * MulAut.conj h by
        rw [← KFacts.mul_mulAutConj_mul_inv σ₀ h]; group]
    simp only [map_inv, inv_inv]
    group
  ·
    obtain ⟨y0, hy0⟩ : ∃ y0 : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
        (y0 : ModGL TwistTag.D4.tag K) = d4TrialityY0 K :=
      ⟨⟨d4TrialityY0 K, d4TrialityY0_mem σ.toRingHom⟩, rfl⟩
    have hA : x * (gL * PL⁻¹) * x⁻¹ = baseChangeGL ι (d4TrialityY0 K * P⁻¹) := by
      rw [map_mul, map_inv, hιP, hιY]; exact hx
    obtain ⟨h, hh⟩ := key (d4TrialityY0 K * P⁻¹)
      (by rw [map_mul, map_inv, hιP, hιY, map_mul, hFY, hFPLi])
      (by rw [map_mul, map_inv, hιP, hιY]; exact hY L) hA
    refine ⟨h, y0, Or.inr hy0, ?_⟩
    have hgeq : g = h⁻¹ * y0 * σ₀ h := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hσ₀ h, hy0]
      calc (g : ModGL TwistTag.D4.tag K) =
          (h : ModGL TwistTag.D4.tag K)⁻¹ *
            ((h : ModGL TwistTag.D4.tag K) * (g * P⁻¹) * (h : ModGL TwistTag.D4.tag K)⁻¹) *
              (h : ModGL TwistTag.D4.tag K) * P := by group
        _ = _ := by rw [hh]; group
    rw [hgeq, map_mul, map_mul, mul_assoc,
      show MulAut.conj (σ₀ h) * σ₀ = σ₀ * MulAut.conj h by
        rw [← KFacts.mul_mulAutConj_mul_inv σ₀ h]; group]
    simp only [map_inv, inv_inv]
    group

theorem kF82D4LangCoset_of_geom (hG : D4TrialityGeomClasses) (hP : D4DiagramCentIrred)
    (hY : D4SecondCentIrred) : KF82D4LangCoset := by
  intro n K _ _ σ hK hσ g hg3
  obtain ⟨h, y, hy, hgy⟩ := exists_conj_eq_of_geom hG hP hY hK hσ g hg3
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · have : 2 ≤ Nat.card K := Finite.one_lt_card
      rw [hK] at this
      norm_num at this
    · exact h
  have : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (f := n * 3) (by
      rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have h2K : (2 : K) = 0 := CharP.cast_eq_zero K 2
  refine ⟨MulAut.conj h⁻¹, y, ?_, ?_, hgy⟩
  · apply Subtype.ext
    rw [coe_fieldActor]
    rcases hy with hy | hy
    · rw [hy, map_one]
    · rw [hy]
      exact entrywise_d4TrialityY0 σ.toRingHom
  · apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    rcases hy with hy | hy
    · rw [hy, one_pow]
    · rw [hy]
      exact d4TrialityY0_pow_three h2K

end CFSG.RankThree.PartTwo.Sec8
