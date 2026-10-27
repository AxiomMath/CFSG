module

public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeDefs
public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeExcPlusAux
public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeExcPlusAux2
public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeF4ThreeAux
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitTwE6Plus
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitTwE6Three
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitTwE6SplitHolds
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitTwE6SplitFrame
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6RankOuter
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaCenter
public import CFSG.LieType.Steinberg.Exceptional.Fields
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6ThreeTorus
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6ThreeSC
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6ThreeNormalizer
public import CFSG.LocalAnalysis.StandardType.GGIrred937TwE6
public import CFSG.LocalAnalysis.StandardType.GGIrred937TwE6Transport
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937TwE6Inn
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937TwE6Center
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6SplitLift
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6Lift

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.RootSystem CFSG.LieType.SeitzGeneration CFSG.LieType.Steinberg.Exceptional

theorem ggWTTw_isWeylMatrix_E6 :
    GGIsWeylMatrix (coxeterMatrix (isFiniteType_cartan .E6)) := by
  have hc : CFSG.Blueprint.Chevalley.Tag.cartan .E6 = CartanMatrix.E 6 :=
    CFSG.LieType.Chevalley.cartanE_eq 6
  have hmat : CoxeterMatrix.E₆ = CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Chevalley.isFiniteType_cartan .E6) := by
    exact (coxeterMatrix_eq_of_ggIntCartan
      (C := CFSG.Blueprint.Chevalley.Tag.cartan .E6)
      (M := CoxeterMatrix.E₆)
      (CFSG.LieType.Chevalley.isFiniteType_cartan .E6)
      (hc.symm ▸ ggIntCartan_E₆)).symm
  exact hmat ▸ (Or.inr (Or.inl ⟨Equiv.refl _, rfl⟩))

theorem ggWTTw_card_E6 :
    Nat.card (coxeterMatrix (isFiniteType_cartan .E6)).Group ≠ 12 := by
  have hc : CFSG.Blueprint.Chevalley.Tag.cartan .E6 = CartanMatrix.E 6 :=
    CFSG.LieType.Chevalley.cartanE_eq 6
  have hmat : CoxeterMatrix.E₆ = CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Chevalley.isFiniteType_cartan .E6) := by
    exact (coxeterMatrix_eq_of_ggIntCartan
      (C := CFSG.Blueprint.Chevalley.Tag.cartan .E6)
      (M := CoxeterMatrix.E₆)
      (CFSG.LieType.Chevalley.isFiniteType_cartan .E6)
      (hc.symm ▸ ggIntCartan_E₆)).symm
  have hgroup : (CoxeterMatrix.E₆).Group = (coxeterMatrix (isFiniteType_cartan .E6)).Group :=
    congrArg CoxeterMatrix.Group hmat
  have hcard : Nat.card (coxeterMatrix (isFiniteType_cartan .E6)).Group =
      Nat.card (CoxeterMatrix.E₆).Group :=
    Nat.card_congr (Equiv.cast hgroup.symm)
  rw [hcard]
  have h : Nat.card (CoxeterMatrix.E₆).Group = 51840 := by
    have hgroup2 : CFSG.LieType.Chevalley.WeylGroup .E6 = (CoxeterMatrix.E₆).Group :=
      congrArg CoxeterMatrix.Group hmat.symm
    have hcardW : Nat.card (CFSG.LieType.Chevalley.WeylGroup .E6) =
        Nat.card (CoxeterMatrix.E₆).Group :=
      Nat.card_congr (Equiv.cast hgroup2)
    rw [← hcardW]
    exact NoOffExc.card_weyl_E6
  rw [h]
  norm_num

theorem ggWTTw_weylTypeW_twE6Plus
    {n p : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpn : p ∣ 2 ^ n + 1) :
    GGTorusWeylTypeW p 5 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  haveI : CharP K 2 := charP_two_of_card (K := K) (m := 2 * n) (by rw [hK, ← pow_mul, mul_comm])
  obtain ⟨e⟩ := TwE6Rank.exists_mulEquiv_graphFixedRootGroup hn hK (iterateFrobenius K 2 n)
    (fun c => iterateFrobenius_def 2 n c)
  exact ggWTEx1_weylTypeW_of_excPlusModel hp hp2 ggWTTw_isWeylMatrix_E6 ggWTTw_card_E6
    (ggExcPlusWeylModelSCr_of_frameModelOn hp (TwE6Delta.center_recipeR_eq_bot hn hK)
      (fun φ hφ hφp => TwE6Delta.ggOutdiagPrime_twE6 hn hK hp hp3 φ hφ hφp)
      (TwE6Delta.ggCenterPrime_twE6 hn hK hp hp2 hp3)
      ((excPlusFrameModelOn_twE6Plus hp hp5 hn hpn K hK (iterateFrobenius K 2 n)
        (fun c => iterateFrobenius_def 2 n c)).of_mulEquiv e))

theorem ggWTTw_excPlusFrameModelOn_twE6Three_gf
    {f : ℕ} (hf : 1 ≤ f) (h3 : ¬ 3 ∣ 2 ^ f + 1) :
    GGExcPlusFrameModelOn .F4 3 4
      (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) := by
  classical
  obtain ⟨ζ, hζ, -, hζo, -⟩ := ExcFrames.exists_threeFrame hf h3
  have hFinj := ExcFrames.twE6ThreeFrameHom_injective hf h3 hζo hζ
  choose m hm using fun i => Irred937.exists_normalizer_realization_twE6 hf h3 hζo hζ i
  intro E hE hcard hsc
  have hEsc : ∀ c ∈ Subgroup.centralizer (E : Set
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))), c ^ 3 = 1 →
        c ∈ E :=
    fun c hc hc3 => hsc c (fun e he => (Subgroup.mem_centralizer_iff.mp hc e he).symm) hc3
  obtain ⟨c, hc⟩ := ExcFrames.twistedE6ThreeSCReference_holds hf h3 hζo hζ hE hcard hEsc
  refine ⟨(MulAut.conj c).toMonoidHom.comp (ExcFrames.twE6ThreeFrameHom hf h3 ζ hζ),
    fun i => c * m i * c⁻¹, (MulAut.conj c).injective.comp hFinj,
    by rw [MonoidHom.range_comp, hc], ?_, ?_⟩
  · intro i s
    have h1 := hm i s
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← h1]
    group
  · intro g hg
    rw [hc, ← Subgroup.map_equiv_normalizer_eq] at hg
    obtain ⟨x, hx, rfl⟩ := hg
    have hxs : ∀ s, x * ExcFrames.twE6ThreeFrameHom hf h3 ζ hζ s * x⁻¹ ∈
        (ExcFrames.twE6ThreeFrameHom hf h3 ζ hζ).range :=
      fun s => (Subgroup.mem_normalizer_iff.mp hx _).mp ⟨s, rfl⟩
    have hxM := ExcFrames.mem_graphFixedRootMonomial_of_normalizes_twE6ThreeFrame hf h3 hζo hζ hxs
    refine ⟨foldedWeylEquiv TwistTag.E6
      ⟨graphFixedRootWeylHom TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)
        ⟨(x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))), hxM⟩,
        (graphFixedRootWeylHom_range TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)).le
          ⟨⟨(x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))), hxM⟩, rfl⟩⟩, fun s => ?_⟩
    have h1 := ExcFrames.twE6ThreeFrameHom_conj hf h3 hζo hζ hxM s
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have h2 : x * ExcFrames.twE6ThreeFrameHom hf h3 ζ hζ (Multiplicative.ofAdd s) * x⁻¹ =
        ExcFrames.twE6ThreeFrameHom hf h3 ζ hζ (Multiplicative.ofAdd (TableBExc.torusAct .F4 3
          (foldedWeylEquiv TwistTag.E6
            ⟨graphFixedRootWeylHom TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)
              ⟨(x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))), hxM⟩,
              (graphFixedRootWeylHom_range TwistTag.E6 (GaloisField 2 (2 * f))
                (frobQ 2 f)).le ⟨⟨(x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))), hxM⟩,
                  rfl⟩⟩) s)) :=
      Subtype.ext (by simpa using h1)
    rw [show c * x * c⁻¹ * (c * ExcFrames.twE6ThreeFrameHom hf h3 ζ hζ (Multiplicative.ofAdd s) *
        c⁻¹) * (c * x * c⁻¹)⁻¹ =
        c * (x * ExcFrames.twE6ThreeFrameHom hf h3 ζ hζ (Multiplicative.ofAdd s) * x⁻¹) * c⁻¹ by
      group, h2]

theorem ggWTTw_weylTypeW_twE6Three
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (h3 : 3 ∣ 2 ^ n - 1) :
    GGTorusWeylTypeW 3 4 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) := by
  have hchar : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  set σ : K →+* K := iterateFrobenius K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  have := Fintype.ofFinite K
  have := Fintype.ofFinite (GaloisField 2 (2 * n))
  have hcard : Fintype.card (GaloisField 2 (2 * n)) = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      CFSG.LieType.Universal.card_galoisField_two_mul 2 n hn, hK]
  set τ := FiniteField.ringEquivOfCardEq hcard with hτdef
  have hτ : ∀ c : GaloisField 2 (2 * n), τ (frobQ 2 n c) = σ (τ c) := fun c => by
    rw [frobQ_apply, hσ, map_pow]
  obtain ⟨e⟩ := TwE6Rank.exists_mulEquiv_graphFixedRootGroup (K := K) hn hK σ hσ
  obtain ⟨e₂⟩ := Irred937.graphFixedRootGroup_mulEquiv_of_ringEquiv
    (K := GaloisField 2 (2 * n)) (K' := K) τ (frobQ 2 n) σ (fun c => (hτ c).symm)
  have h3' : ¬ 3 ∣ 2 ^ n + 1 := by
    intro h
    have hd : 3 ∣ 2 := by
      have h1 : 3 ∣ 2 ^ n + 1 - (2 ^ n - 1) := Nat.dvd_sub h h3
      have h2 : 2 ^ n + 1 - (2 ^ n - 1) = 2 := by
        have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        omega
      rwa [h2] at h1
    have := Nat.le_of_dvd (by norm_num : 0 < 2) hd
    omega
  refine ggWTEx1_weylTypeW_of_excPlusModel Nat.prime_three (by norm_num)
    ggWTEx1_isWeylMatrix_F4 ggWTEx1_card_F4
    (ggExcPlusWeylModelSCr_of_frameModelOn Nat.prime_three
      (TwE6Delta.center_recipeR_eq_bot hn hK)
      (fun φ hφ _ => TwE6Delta.recipeI_subset_inn_of_not_dvd hn hK h3' hφ)
      (TwE6Delta.ggCenterPrime_three_twE6 hn hK h3')
      ((ggWTTw_excPlusFrameModelOn_twE6Three_gf hn h3').of_mulEquiv (e.trans e₂.symm)))

theorem ggWTTw_weylTypeW_twE6Split
    {n p : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpn : p ∣ 2 ^ n - 1) :
    GGTorusWeylTypeW p 4 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  haveI : CharP K 2 := charP_two_of_card (K := K) (m := 2 * n) (by rw [hK, ← pow_mul, mul_comm])
  obtain ⟨e⟩ := TwE6Rank.exists_mulEquiv_graphFixedRootGroup hn hK (iterateFrobenius K 2 n)
    (fun c => iterateFrobenius_def 2 n c)
  refine ggWTEx1_weylTypeW_of_excPlusModel hp hp2 ggWTEx1_isWeylMatrix_F4 ggWTEx1_card_F4
    (ggExcPlusWeylModelSCr_of_frameModelOn hp (TwE6Delta.center_recipeR_eq_bot hn hK)
      (fun φ hφ hφp => TwE6Delta.ggOutdiagPrime_twE6 hn hK hp hp3 φ hφ hφp)
      (TwE6Delta.ggCenterPrime_twE6 hn hK hp hp2 hp3)
      ((excPlusFrameModelOn_twE6Split hn hK (iterateFrobenius K 2 n)
        (fun c => iterateFrobenius_def 2 n c) hp5 hpn).of_mulEquiv e))

theorem ggWTTw_largeEvenLabelAll_weylTypeW_twE6Plus
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGTorusWeylTypeW p r R I) := by
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    have h4 : p ≠ 4 := fun h4 => by subst h4; exact absurd hp (by norm_num)
    omega
  have hW : LargeEvenLabelAll lab fun R _ I _ => GGTorusWeylTypeW p 5 R I :=
    TwE6Delta.labelAll h.1 fun _ _ _ hK => ggWTTw_weylTypeW_twE6Plus hlab.1 hK hp hp5 h.2
  refine (largeEvenLabelAll_and (largeEvenLabelAll_torusLift_twE6Add_holds hp hlab h) hW).mono
    fun _ _ _ _ ⟨hl, hw⟩ _ _ => ⟨5, ?_, hw⟩
  rwa [TwE6Delta.liftRank_of_ne hp3] at hl

theorem ggWTTw_largeEvenLabelAll_weylTypeW_twE6Three
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ =>
      ∃ r, GGTorusLift 3 r R ∧ GGTorusWeylTypeW 3 r R I) :=
  TwE6Delta.labelAll h.1 fun _ _ _ hK _ _ =>
    ⟨4, ggTorusLift_twE6Dvd_holds hlab.1 hK Nat.prime_three (by norm_num) h.2,
      ggWTTw_weylTypeW_twE6Three hlab.1 hK h.2⟩

end CFSG.StandardType

end
