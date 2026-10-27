module

public import CFSG.RankThree.PartTwo.Sec21.LangTwisted2ProofD4Unitary

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  LangTwistedProof LangTwisted2Proof Matrix
open CFSG.Assembly.RankThreeEven (projImage)
open scoped MatrixGroups



namespace LangTwisted2Proof

variable {L : Type} [Field L] [CharP L 2]

theorem twistHom_secZ {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0) {Fr : L →+* L}
    (hFr : Fr (μ : L) = (μ : L) ^ 2) :
    twistHom TwistTag.D4 L Fr (yUnit TwistTag.D4.tag L 2 μ * xUnit TwistTag.D4.tag L 2 1) =
      yUnit TwistTag.D4.tag L 2 μ * xUnit TwistTag.D4.tag L 2 1 *
        weylElt TwistTag.D4.tag L 2 1 := by
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  have hp2 : TwistTag.D4.perm 2 = 2 := by decide
  rw [map_mul, twistHom_xUnit, twistHom_yUnit, hp2, hFr, map_one,
    Blueprint.Chevalley.weylElt_eq_xUnit_mul]
  have e1 : xUnit TwistTag.D4.tag L 2 1 * xUnit TwistTag.D4.tag L 2 1 = 1 := by
    rw [← xUnit_add, show (1 : L) + 1 = 0 by rw [one_add_one_eq_two, h2], xUnit_zero]
  have e2 : yUnit TwistTag.D4.tag L 2 (μ : L) * yUnit TwistTag.D4.tag L 2
      (-(((1 : Lˣ)⁻¹ : Lˣ) : L)) = yUnit TwistTag.D4.tag L 2 ((μ : L) ^ 2) := by
    rw [← yUnit_add]
    congr 1
    simp only [inv_one, Units.val_one]
    linear_combination -hμ + (μ : L) * h2
  calc yUnit TwistTag.D4.tag L 2 ((μ : L) ^ 2) * xUnit TwistTag.D4.tag L 2 1 =
      yUnit TwistTag.D4.tag L 2 (μ : L) * yUnit TwistTag.D4.tag L 2 (-(((1 : Lˣ)⁻¹ : Lˣ) : L)) *
        xUnit TwistTag.D4.tag L 2 1 := by rw [e2]
    _ = yUnit TwistTag.D4.tag L 2 (μ : L) * (xUnit TwistTag.D4.tag L 2 1 *
        xUnit TwistTag.D4.tag L 2 1) * yUnit TwistTag.D4.tag L 2 (-(((1 : Lˣ)⁻¹ : Lˣ) : L)) *
          xUnit TwistTag.D4.tag L 2 1 := by rw [e1, mul_one]
    _ = _ := by simp only [Units.val_one, mul_assoc]

theorem exists_cube_root_unit {L : Type} [Field L] [IsAlgClosed L] :
    ∃ μ : Lˣ, (μ : L) ^ 2 + μ + 1 = 0 := by
  have hdeg : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial L).degree ≠ 0 := by
    have h : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial L).degree = 2 := by
      compute_degree!
    rw [h]
    decide
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hdeg
  have hz' : z ^ 2 + z + 1 = 0 := by
    simpa [Polynomial.IsRoot] using hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hz'
  exact ⟨Units.mk0 z hz0, by simpa using hz'⟩

theorem pow_two_pow_odd {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0) {n : ℕ} (hn : Odd n) :
    (μ : L) ^ 2 ^ n = (μ : L) ^ 2 := by
  have h3 : (μ : L) ^ 3 = 1 := by linear_combination ((μ : L) - 1) * hμ
  obtain ⟨k, rfl⟩ := hn
  have hmod : 2 ^ (2 * k + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  rw [← Nat.div_add_mod (2 ^ (2 * k + 1)) 3, hmod, pow_add, pow_mul, h3, one_pow, one_mul]

theorem nonempty_autFix_equiv_secFixG {n : ℕ} (hn1 : 1 ≤ n) {K : Type} [Field K] [Finite K]
    [CharP K 2] {σ : K ≃+* K} (hK : Nat.card K = (2 ^ n) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    [CharP (AlgebraicClosure K) 2] {μ : (AlgebraicClosure K)ˣ}
    (hμ : (μ : AlgebraicClosure K) ^ 2 + μ + 1 = 0)
    (hFrμ : iterateFrobenius (AlgebraicClosure K) 2 n (μ : AlgebraicClosure K) =
      (μ : AlgebraicClosure K) ^ 2) :
    Nonempty (Sec4.autFix (MulAut.conj (d4TrialityY0Elt K σ) * fieldActor σ σ) ≃*
      secFixG μ (iterateFrobenius (AlgebraicClosure K) 2 n)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := AlgebraicClosure K
  have h2L : (2 : L) = 0 := CharP.cast_eq_zero L 2
  set C₀ := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC₀
  set σ₀ := fieldActor (t := TwistTag.D4) σ σ with hσ₀def
  set P := diagramMap TwistTag.D4 K with hPdef
  have hσ₀ : ∀ x : C₀, ((σ₀ x : C₀) : ModGL TwistTag.D4.tag K) = P⁻¹ * x * P := by
    intro x
    have hx := ((mem_twistedFixedGroup_iff_twistHom _ _ _).1
      (graphFixedRootGroup_le _ _ _ x.2)).2
    rw [twistHom_apply] at hx
    rw [coe_fieldActor]
    calc Units.map (entrywiseHom σ.toRingHom) (x : ModGL TwistTag.D4.tag K) =
        P⁻¹ * (P * Units.map (entrywiseHom σ.toRingHom) (x : ModGL TwistTag.D4.tag K) * P⁻¹) *
          P := by group
      _ = P⁻¹ * x * P := by rw [hx]
  set ι := algebraMap K L with hιdef
  set PL := diagramMap TwistTag.D4 L with hPLdef
  have hιP : baseChangeGL ι P = PL := baseChangeGL_diagramMap ι TwistTag.D4
  set Fr : L →+* L := iterateFrobenius L 2 n with hFrdef
  have hFr : ∀ c, Fr c = c ^ (2 ^ n) := fun c => iterateFrobenius_def 2 n c
  have hcomm : ι.comp σ.toRingHom = Fr.comp ι := by
    ext c
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [hFr, hσ, map_pow]
  set z := yUnit TwistTag.D4.tag L 2 μ * xUnit TwistTag.D4.tag L 2 1 with hz
  have hzG : z ∈ adjointGroup TwistTag.D4.tag L :=
    mul_mem (yUnit_mem_adjointGroup 2 _) (xUnit_mem_adjointGroup 2 _)
  have hy0 : d4TrialityY0 L * PL⁻¹ = z * (secElt μ)⁻¹ * z⁻¹ := by
    rw [hz, ← wordUnit_secZWord]
    exact d4TrialityY0_mul_eq_conj h2L hμ
  have hcent : graphCentralizer TwistTag.D4.tag L (d4TrialityY0 L * PL⁻¹) =
      (secM μ).map (MulAut.conj z).toMonoidHom := by
    rw [hy0, graphCentralizer_conj hzG, graphCentralizer_inv, graphCentralizer_secElt_eq h2L hμ]
  have hFz : twistHom TwistTag.D4 L Fr z = z * weylElt TwistTag.D4.tag L 2 1 :=
    twistHom_secZ hμ hFrμ
  have hrange := CFSG.RankThree.PartOne.KGD.triEmb_range (σ := σ) (L := L) Nat.prime_two hn1 hK
    hσ Fr hFr
  set y₀ := d4TrialityY0Elt K σ with hy₀
  have hιy₀ : baseChangeGL ι (y₀ : ModGL TwistTag.D4.tag K) = d4TrialityY0 L :=
    baseChangeGL_d4TrialityY0 ι
  have key : ∀ x : C₀, (MulAut.conj y₀ * σ₀) x = x ↔
      CFSG.RankThree.PartOne.KGD.triEmb K σ L x ∈
        Subgroup.centralizer {d4TrialityY0 L * PL⁻¹} := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff, CFSG.RankThree.PartOne.KGD.triEmb_apply,
      ← hιy₀, ← hιP, ← map_inv, ← map_mul, ← map_mul, ← map_mul,
      (baseChangeGL_injective ι).eq_iff]
    rw [MulAut.mul_apply, MulAut.conj_apply]
    constructor
    · intro h
      have h' := congrArg (fun u : C₀ => (u : ModGL TwistTag.D4.tag K)) h
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hσ₀] at h'
      calc (x : ModGL TwistTag.D4.tag K) * ((y₀ : ModGL TwistTag.D4.tag K) * P⁻¹) =
          ((y₀ : ModGL TwistTag.D4.tag K) * (P⁻¹ * x * P) * (y₀ : ModGL TwistTag.D4.tag K)⁻¹) *
            ((y₀ : ModGL TwistTag.D4.tag K) * P⁻¹) := by rw [h']
        _ = (y₀ : ModGL TwistTag.D4.tag K) * P⁻¹ * x := by group
    · intro h
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hσ₀]
      calc (y₀ : ModGL TwistTag.D4.tag K) * (P⁻¹ * x * P) * (y₀ : ModGL TwistTag.D4.tag K)⁻¹ =
          ((y₀ : ModGL TwistTag.D4.tag K) * P⁻¹ * x) *
            ((y₀ : ModGL TwistTag.D4.tag K) * P⁻¹)⁻¹ := by group
        _ = ((x : ModGL TwistTag.D4.tag K) * ((y₀ : ModGL TwistTag.D4.tag K) * P⁻¹)) *
            ((y₀ : ModGL TwistTag.D4.tag K) * P⁻¹)⁻¹ := by rw [h]
        _ = x := by group
  have hF'' : ∀ g, secFrob Fr (z⁻¹ * g * z) = z⁻¹ * twistHom TwistTag.D4 L Fr g * z := by
    intro g
    rw [secFrob_apply, map_mul, map_mul, map_inv, hFz]
    group
  set X := Sec4.autFix (MulAut.conj y₀ * σ₀)
  set f : X →* ModGL TwistTag.D4.tag L := (MulAut.conj z⁻¹).toMonoidHom.comp
    ((CFSG.RankThree.PartOne.KGD.triEmb K σ L).comp X.subtype) with hf
  have hfx : ∀ x : X, f x = z⁻¹ * CFSG.RankThree.PartOne.KGD.triEmb K σ L x.1 * z := by
    intro x
    change (MulAut.conj z⁻¹) (CFSG.RankThree.PartOne.KGD.triEmb K σ L x.1) = _
    rw [MulAut.conj_apply, inv_inv]
  have hmem : ∀ x : X, f x ∈ secFixG μ Fr := by
    intro x
    rw [hfx]
    set g := CFSG.RankThree.PartOne.KGD.triEmb K σ L x.1
    have hgC : g ∈ graphCentralizer TwistTag.D4.tag L (d4TrialityY0 L * PL⁻¹) :=
      Subgroup.mem_inf.2 ⟨CFSG.RankThree.PartOne.KGD.triEmb_mem_adjointGroup x.1,
        (key x.1).1 x.2⟩
    rw [hcent] at hgC
    obtain ⟨m, hm, hmg⟩ := hgC
    have hmz : z⁻¹ * g * z = m := by
      rw [← hmg]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    refine ⟨hmz ▸ hm, ?_⟩
    change secFrob Fr (z⁻¹ * g * z) = z⁻¹ * g * z
    rw [hF'', CFSG.RankThree.PartOne.KGD.triEmb_fixed Fr hcomm x.1]
  have hfinj : Function.Injective f := by
    intro x x' h
    rw [hfx, hfx] at h
    have h'' := mul_left_cancel (mul_right_cancel h)
    exact Subtype.ext (CFSG.RankThree.PartOne.KGD.triEmb_injective h'')
  refine ⟨MulEquiv.ofBijective (f.codRestrict (secFixG μ Fr) hmem) ⟨fun x x' h => hfinj
    (congrArg Subtype.val h), fun m => ?_⟩⟩
  set g := z * (m : ModGL TwistTag.D4.tag L) * z⁻¹ with hg
  have hgC : g ∈ graphCentralizer TwistTag.D4.tag L (d4TrialityY0 L * PL⁻¹) := by
    rw [hcent]
    exact ⟨m, m.2.1, rfl⟩
  have hFg : twistHom TwistTag.D4 L Fr g = g := by
    have hm2 : secFrob Fr (m : ModGL TwistTag.D4.tag L) = m := m.2.2
    have e : (m : ModGL TwistTag.D4.tag L) = z⁻¹ * g * z := by rw [hg]; group
    rw [e, hF''] at hm2
    calc twistHom TwistTag.D4 L Fr g = z * (z⁻¹ * twistHom TwistTag.D4 L Fr g * z) * z⁻¹ := by
          group
      _ = z * (z⁻¹ * g * z) * z⁻¹ := by rw [hm2]
      _ = g := by group
  have hgr : g ∈ (CFSG.RankThree.PartOne.KGD.triEmb K σ L).range := by
    rw [hrange]
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hgC).1, hFg⟩
  obtain ⟨x, hx⟩ := hgr
  have hxX : x ∈ X := (key x).2 (hx ▸ (Subgroup.mem_inf.1 hgC).2)
  refine ⟨⟨x, hxX⟩, Subtype.ext ?_⟩
  change f ⟨x, hxX⟩ = m
  rw [hfx]
  change z⁻¹ * CFSG.RankThree.PartOne.KGD.triEmb K σ L x * z = m
  rw [hx, hg]
  group

end LangTwisted2Proof

theorem kF82D4SecondCentY0_holds : KF82D4SecondCentY0 := by
  intro n hn K _ _ σ hK hσ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn1 : 1 ≤ n := hn.pos
  have : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := n * 3)
      (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨μ, hμ⟩ := exists_cube_root_unit (L := AlgebraicClosure K)
  set Fr := iterateFrobenius (AlgebraicClosure K) 2 n with hFrdef
  have hFr : ∀ c, Fr c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  have hFrμ : Fr (μ : AlgebraicClosure K) = (μ : AlgebraicClosure K) ^ 2 := by
    rw [hFr]
    exact pow_two_pow_odd hμ hn
  obtain ⟨e₁⟩ := nonempty_autFix_equiv_secFixG hn1 hK hσ hμ hFrμ
  have e₂ := secFixEquiv hμ hFrμ
  have hcard : Nat.card (GaloisField 2 (2 * n)) = 2 ^ (2 * n) :=
    GaloisField.card 2 (2 * n) (by omega)
  let _ : Fintype (GaloisField 2 (2 * n)) := Fintype.ofFinite _
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n (GaloisField 2 (2 * n)) :=
    ⟨Nat.prime_two, hn1, hcard⟩
  let _ := ZMod.algebra (AlgebraicClosure K) 2
  let ι : GaloisField 2 (2 * n) →+* AlgebraicClosure K :=
    (IsAlgClosed.lift (R := ZMod 2) (S := GaloisField 2 (2 * n))
      (M := AlgebraicClosure K)).toRingHom
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (μ : AlgebraicClosure K)
    (Nat.succ_pos (2 ^ n))
  have hcF : c * Fr c = μ := by
    rw [hFr, ← pow_succ']
    exact hc
  have hdet : (secG0Mat (μ : AlgebraicClosure K) c).det ≠ 0 := by
    rw [det_secG0Mat hμ]
    rintro rfl
    rw [zero_pow (Nat.succ_ne_zero _)] at hc
    exact Units.ne_zero μ hc.symm
  set G₀ : GL (Fin 3) (AlgebraicClosure K) := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet
  have hG : (G₀ : Matrix (Fin 3) (Fin 3) (AlgebraicClosure K)) *
      ((G₀ : Matrix (Fin 3) (Fin 3) (AlgebraicClosure K)).map Fr)ᵀ =
        secH (μ : AlgebraicClosure K) :=
    secG0_mul_frob_transpose hμ hFrμ hcF
  have e₃ := pguEquivPglFix ι hU hFr μ hG
  refine ⟨GaloisField 2 (2 * n), inferInstance, inferInstance, ?_, ⟨e₁.trans (e₂.trans e₃.symm)⟩⟩
  rw [hcard, ← pow_mul, mul_comm]

theorem kF82D4SecondCent_holds :
    KF82D4SecondCent :=
  kF82D4SecondCent_of_secondCentY0 kF82D4SecondCentY0_holds

end CFSG.RankThree.PartTwo.Sec8
