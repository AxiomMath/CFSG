module

public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofEven
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofD4
public import CFSG.RankThree.PartTwo.Sec21.LangTwisted2ProofD4

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  LangTwistedProof LangTwisted2Proof Matrix
open CFSG.Assembly.RankThreeEven (projImage)
open scoped MatrixGroups



namespace Item8KFacts2Proof

variable {L : Type} [Field L] [CharP L 2]

theorem twistHom_secZ_even {μ : Lˣ} {Fr : L →+* L} (hFr : Fr (μ : L) = (μ : L)) :
    twistHom TwistTag.D4 L Fr (yUnit TwistTag.D4.tag L 2 μ * xUnit TwistTag.D4.tag L 2 1) =
      yUnit TwistTag.D4.tag L 2 μ * xUnit TwistTag.D4.tag L 2 1 := by
  have hp2 : TwistTag.D4.perm 2 = 2 := by decide
  rw [map_mul, twistHom_xUnit, twistHom_yUnit, hp2, hFr, map_one]

theorem pow_two_pow_even {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0) {n : ℕ} (hn : Even n) :
    (μ : L) ^ 2 ^ n = (μ : L) := by
  have h3 : (μ : L) ^ 3 = 1 := by linear_combination ((μ : L) - 1) * hμ
  obtain ⟨k, rfl⟩ := hn
  have hmod : 2 ^ (k + k) % 3 = 1 := by
    rw [← two_mul, pow_mul, Nat.pow_mod]
    norm_num
  rw [← Nat.div_add_mod (2 ^ (k + k)) 3, hmod, pow_add, pow_mul, h3, one_pow, one_mul, pow_one]

theorem nonempty_autFix_equiv_secFixEvenG {n : ℕ} (hn1 : 1 ≤ n) {K : Type} [Field K] [Finite K]
    [CharP K 2] {σ : K ≃+* K} (hK : Nat.card K = (2 ^ n) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    [CharP (AlgebraicClosure K) 2] {μ : (AlgebraicClosure K)ˣ}
    (hμ : (μ : AlgebraicClosure K) ^ 2 + μ + 1 = 0)
    (hFrμ : iterateFrobenius (AlgebraicClosure K) 2 n (μ : AlgebraicClosure K) =
      (μ : AlgebraicClosure K)) :
    Nonempty (Sec4.autFix (MulAut.conj (d4TrialityY0Elt K σ) * fieldActor σ σ) ≃*
      secFixEvenG μ (iterateFrobenius (AlgebraicClosure K) 2 n)) := by
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
  have hFz : twistHom TwistTag.D4 L Fr z = z := twistHom_secZ_even hFrμ
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
  have hF : ∀ g, twistHom TwistTag.D4 L Fr (z⁻¹ * g * z) =
      z⁻¹ * twistHom TwistTag.D4 L Fr g * z := by
    intro g
    rw [map_mul, map_mul, map_inv, hFz]
  set X := Sec4.autFix (MulAut.conj y₀ * σ₀)
  set f : X →* ModGL TwistTag.D4.tag L := (MulAut.conj z⁻¹).toMonoidHom.comp
    ((CFSG.RankThree.PartOne.KGD.triEmb K σ L).comp X.subtype) with hf
  have hfx : ∀ x : X, f x = z⁻¹ * CFSG.RankThree.PartOne.KGD.triEmb K σ L x.1 * z := by
    intro x
    change (MulAut.conj z⁻¹) (CFSG.RankThree.PartOne.KGD.triEmb K σ L x.1) = _
    rw [MulAut.conj_apply, inv_inv]
  have hmem : ∀ x : X, f x ∈ secFixEvenG μ Fr := by
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
    change twistHom TwistTag.D4 L Fr (z⁻¹ * g * z) = z⁻¹ * g * z
    rw [hF, CFSG.RankThree.PartOne.KGD.triEmb_fixed Fr hcomm x.1]
  have hfinj : Function.Injective f := by
    intro x x' h
    rw [hfx, hfx] at h
    have h'' := mul_left_cancel (mul_right_cancel h)
    exact Subtype.ext (CFSG.RankThree.PartOne.KGD.triEmb_injective h'')
  refine ⟨MulEquiv.ofBijective (f.codRestrict (secFixEvenG μ Fr) hmem) ⟨fun x x' h => hfinj
    (congrArg Subtype.val h), fun m => ?_⟩⟩
  set g := z * (m : ModGL TwistTag.D4.tag L) * z⁻¹ with hg
  have hgC : g ∈ graphCentralizer TwistTag.D4.tag L (d4TrialityY0 L * PL⁻¹) := by
    rw [hcent]
    exact ⟨m, m.2.1, rfl⟩
  have hFg : twistHom TwistTag.D4 L Fr g = g := by
    have hm2 : twistHom TwistTag.D4 L Fr (m : ModGL TwistTag.D4.tag L) = m := m.2.2
    have e : (m : ModGL TwistTag.D4.tag L) = z⁻¹ * g * z := by rw [hg]; group
    rw [e, hF] at hm2
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

end Item8KFacts2Proof


theorem kF82D4SecondCentY0Even_holds : KF82D4SecondCentY0Even := by
  intro n hn hn1 K _ _ σ hK hσ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := n * 3)
      (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨μ, hμ⟩ := exists_cube_root_unit (L := AlgebraicClosure K)
  set Fr := iterateFrobenius (AlgebraicClosure K) 2 n with hFrdef
  have hFr : ∀ c, Fr c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  have hFrμ : Fr (μ : AlgebraicClosure K) = (μ : AlgebraicClosure K) := by
    rw [hFr]
    exact Item8KFacts2Proof.pow_two_pow_even hμ hn
  obtain ⟨e₁⟩ := Item8KFacts2Proof.nonempty_autFix_equiv_secFixEvenG hn1 hK hσ hμ hFrμ
  have e₂ := Item8KFacts2Proof.secFixEvenEquiv hμ hFrμ
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  let _ : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  let _ := ZMod.algebra (AlgebraicClosure K) 2
  let ι : GaloisField 2 n →+* AlgebraicClosure K :=
    (IsAlgClosed.lift (R := ZMod 2) (S := GaloisField 2 n)
      (M := AlgebraicClosure K)).toRingHom
  have hq : 2 ≤ 2 ^ n := le_trans (by norm_num) (Nat.le_self_pow (by omega) 2)
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq ((μ⁻¹ : (AlgebraicClosure K)ˣ) :
    AlgebraicClosure K) (by omega : 0 < 2 ^ n - 1)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hc
    exact (Units.ne_zero _) hc.symm
  set cu : (AlgebraicClosure K)ˣ := Units.mk0 c hc0 with hcu
  have hcF : (μ : AlgebraicClosure K) * Fr (cu : AlgebraicClosure K) = cu := by
    rw [hcu, Units.val_mk0, hFr]
    have hsq : c ^ 2 ^ n = c ^ (2 ^ n - 1) * c := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hsq, hc, ← mul_assoc, Units.val_inv_eq_inv_val, mul_inv_cancel₀ (Units.ne_zero μ),
      one_mul]
  have hFr' : ∀ c, Fr c = c ^ Nat.card (GaloisField 2 n) := by
    rw [hcard]
    exact hFr
  have e₃ := Item8KFacts2Proof.pglEquivPglFixEven ι hFr' μ hcF
  have hP : ∀ a b : ℕ, projImage (Sec4.glPi true 3 a (GaloisField 2 n)) =
      projImage (Sec4.glPi true 3 b (GaloisField 2 n)) := fun a b =>
    congrArg projImage (Subgroup.ext fun A =>
      ⟨fun _ => Sec4.mem_glPi_true b A, fun _ => Sec4.mem_glPi_true a A⟩)
  refine ⟨GaloisField 2 n, inferInstance, inferInstance, hcard, ⟨?_⟩⟩
  exact (e₁.trans (e₂.trans e₃.symm)).trans (MulEquiv.subgroupCongr (hP _ _))

end CFSG.RankThree.PartTwo.Sec8
