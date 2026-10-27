module

public import CFSG.HardMathSupport.U4FF.Disp
public import CFSG.HardMathSupport.U4FF.ClassFinalRep
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mIsometry
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mLowRank
import all CFSG.Timmesfeld.Orders.Distinct
import CFSG.Adapters.LieModelOrders
import CFSG.RankThree.GF2n.Stroth80.Sec3Zsig
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallField
import CFSG.RankThree.GF2n.Stroth80.Sec41iiIrred
import CFSG.RankThree.GF2n.Stroth80.Sec78NatIrredOmega
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallNatural
import CFSG.LieType.SpecialLinear.BinaryDescent.Basic
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.QuasithinUnique.Setup.Family
open CFSG.Timmesfeld CFSG.Timmesfeld.Orders
open CFSG.QuasithinUnique.Setup.SL2Modules (EndRing)
open CFSG.HardMathSupport.U4FF.ClassFinal (binRep)
open CFSG.LieType.RootSystem
open CFSG.LieType.Universal.Spin
open scoped Matrix
open scoped TensorProduct



theorem eight_mul_le_finrank_of_isOmega8m {G : Type} [Group G] [Finite G] {e : ℕ}
    (hG : IsOmega8m G e) {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : G →* (W ≃ₗ[ZMod 2] W)) (hρ : Function.Injective ρ) :
    8 * e ≤ Module.finrank (ZMod 2) W := by
  have he : 1 ≤ e := hG.admissible.2.1
  obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor (k := 8 * e) (by omega) (by omega)
  have hcard : Nat.card G = ordTwistedD 4 (2 ^ e) := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using hG.card_eq_lieOrd (by norm_num)
  have hdvd : p ∣ Nat.card G := by
    rw [hcard]
    apply ((profile_ordTwistedD (n := 4) (by norm_num) he).prim p (8 * e) hp (by omega)).mpr
    unfold z2D
    left
    constructor
    · convert dvd_refl (8 * e) using 1; ring
    · exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have : Fact p.Prime := ⟨hp.prime⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hord : orderOf (ρ x) = p := (orderOf_injective ρ hρ x).trans hx
  have horder : orderOf (2 : ZMod p) = 8 * e :=
    CFSG.RankThree.GF2n.Stroth80.orderOf_two_zmod_eq_of_primitive hp.prime (by omega) hp.dvd
      hp.2.2
  rw [← horder]
  have hp2 : p ≠ 2 := by
    intro h
    subst h
    exact (Nat.not_even_iff_odd.mpr (odd_two_pow_sub_one (by omega)))
      (even_iff_two_dvd.mpr hp.dvd)
  exact CFSG.HardMathSupport.U4FF.orderOf_two_le_finrank_of_orderOf_eq (ρ x) hp.prime hp2 hord

theorem commute_endRing_of_two_mul_finrank_range_lt {G W : Type} [Group G]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W] (ρ : Representation (ZMod 2) G W)
    (hirr : ρ.IsIrreducible) (s : W ≃ₗ[ZMod 2] W) (hs : ∀ w, s (s w) = w)
    (hN : ∀ g, ∃ g', ∀ w, s (ρ g (s w)) = ρ g' w)
    (hsmall : 2 * Module.finrank (ZMod 2) (LinearMap.range (s.toLinearMap - 1)) <
      Module.finrank (ZMod 2) W) : ∀ d : EndRing ρ, ∀ w, s (d w) = d (s w) := by
  classical
  intro d w
  by_contra hcomm
  have : Fact ρ.IsIrreducible := ⟨hirr⟩
  have hD : ∃ d : EndRing ρ, ∃ w, s (d (s w)) ≠ d w :=
    ⟨d, s w, by simpa only [hs] using hcomm⟩
  have hcard := card_fix_sq_of_not_commute_endRing ρ s hs hN hD
  have hfix : Nat.card {w : W // s w = w} =
      Nat.card (LinearMap.ker (s.toLinearMap - 1)) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun w => by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      rfl)
  have hW : Nat.card W = 2 ^ Module.finrank (ZMod 2) W := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hker : Nat.card (LinearMap.ker (s.toLinearMap - 1)) =
      2 ^ Module.finrank (ZMod 2) (LinearMap.ker (s.toLinearMap - 1)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [hfix, hker, hW, ← pow_mul] at hcard
  have hdim := (Nat.pow_right_injective (by norm_num : 2 ≤ 2)) hcard
  have hrank := LinearMap.finrank_range_add_finrank_ker (s.toLinearMap - 1)
  omega

theorem commute_endRing_of_isOmega8m_small_involution {I : Type} [CommGroup I] [Finite I]
    [Fact (∀ x : I, x * x = 1)] {L : Subgroup (MulAut I)} {e : ℕ} (he : 2 ≤ e)
    (hL : IsOmega8m ↥L e) (hirr : IsIrrOn L ⊤ ⊥) {t : MulAut I}
    (htN : t ∈ Subgroup.normalizer (L : Set (MulAut I))) (ht : t * t = 1)
    (hrank : CFSG.HardMathSupport.U4FF.disp t ≤ 2 * e + 1) :
    ∀ d : EndRing (binRep L (MulEquiv.refl ↥L)), ∀ w : Additive I,
      binaryLin t (d w) = d (binaryLin t w) := by
  have : Nontrivial I := by
    obtain ⟨x, -, hx⟩ := SetLike.exists_of_lt hirr.1
    exact ⟨x, 1, fun h => hx (h ▸ Subgroup.one_mem _)⟩
  have hirrL : CFSG.LocalAnalysis.RankThreeUC.IsIrrOn L := fun U hU =>
    hirr.2.2.2 U hU bot_le le_top
  have hρ := CFSG.HardMathSupport.U4FF.ClassFinal.binRep_isIrreducible
    (MulEquiv.refl ↥L) hirrL
  have hdim := eight_mul_le_finrank_of_isOmega8m hL (binaryLin.comp L.subtype)
    (binaryLin_injective.comp L.subtype_injective)
  apply commute_endRing_of_two_mul_finrank_range_lt (binRep L (MulEquiv.refl ↥L)) hρ
    (binaryLin t)
  · intro w
    change Additive.ofMul (t (t (Additive.toMul w))) = w
    have h := congrArg (fun g : MulAut I => g (Additive.toMul w)) ht
    exact congrArg Additive.ofMul h
  · intro g
    let g' : ↥L := ⟨t * (g : MulAut I) * t⁻¹, (Subgroup.mem_normalizer_iff.mp htN _).mp g.2⟩
    refine ⟨g', fun w => ?_⟩
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht
    change binaryLin t (binaryLin (g : MulAut I) (binaryLin t w)) = binaryLin (g' : MulAut I) w
    dsimp only [g']
    rw [htinv, map_mul, map_mul]
    rfl
  · change 2 * CFSG.HardMathSupport.U4FF.disp t < Module.finrank (ZMod 2) (Additive I)
    omega

theorem bijective_of_equivariant_omegaMinus {m : ℕ} (hm : 3 ≤ m) {K : Type} [Field K]
    [Finite K] [CharP K 2] {b c : K} (hirrQ : ∀ x : K, x ^ 2 + b * x + c ≠ 0)
    {I : Type} [CommGroup I] [Finite I] {L : Subgroup (MulAut I)} (hirr : IsIrrOn L ⊤ ⊥)
    (φ : ↥L ≃* ↥(StatedOmega (StatedQuadMinus m K b c)))
    (f : Additive I →+ (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K)) (hf : f ≠ 0)
    (heq : ∀ (l : ↥L) (w : I), f (Additive.ofMul ((l : MulAut I) w)) =
      ((φ l : Matrix.GeneralLinearGroup
        (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) :
        Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) *ᵥ f (Additive.ofMul w)) :
    Function.Bijective f := by
  classical
  have hker : f.ker = ⊥ := by
    let U : Subgroup I :=
      { carrier := {w | f (Additive.ofMul w) = 0}
        one_mem' := f.map_zero
        mul_mem' := fun {a b} ha hb => by
          change f (Additive.ofMul (a * b)) = 0
          rw [show Additive.ofMul (a * b) = Additive.ofMul a + Additive.ofMul b from rfl,
            map_add, ha, hb, add_zero]
        inv_mem' := fun {a} ha => by
          change f (Additive.ofMul a⁻¹) = 0
          rw [show Additive.ofMul a⁻¹ = -Additive.ofMul a from rfl, map_neg, ha, neg_zero] }
    have hU : StableUnder L U := by
      intro l hl w hw
      change f (Additive.ofMul (l w)) = 0
      rw [heq ⟨l, hl⟩ w, hw, Matrix.mulVec_zero]
    rcases hirr.2.2.2 U hU bot_le le_top with h0 | h1
    · ext w
      rw [AddMonoidHom.mem_ker, AddSubgroup.mem_bot]
      constructor
      · intro hw
        have hmem : Additive.toMul w ∈ U := hw
        rw [h0, Subgroup.mem_bot] at hmem
        exact congrArg Additive.ofMul hmem
      · rintro rfl
        exact map_zero _
    · exact (hf (AddMonoidHom.ext fun w => by
        have hw : Additive.toMul w ∈ U := h1 ▸ Subgroup.mem_top _
        exact hw)).elim
  have hne : f.range ≠ ⊥ := by
    intro h0
    apply hf
    exact AddMonoidHom.ext fun w => by
      have hw : f w ∈ f.range := ⟨w, rfl⟩
      rwa [h0, AddSubgroup.mem_bot] at hw
  have htop : f.range = ⊤ :=
    CFSG.RankThree.GF2n.Stroth80.eq_top_of_addInvariant
      (CFSG.RankThree.GF2n.Stroth80.natIrred_statedOmegaMinus_of_three_le hm hirrQ)
      (CFSG.RankThree.GF2n.Stroth80.addCommutantScalar_statedOmegaMinus (by omega) hirrQ)
      hne (fun g hg w hw => by
        obtain ⟨l, hl⟩ := φ.surjective ⟨g, hg⟩
        obtain ⟨v, rfl⟩ := hw
        have hlg : (φ l : Matrix.GeneralLinearGroup _ K) = g := congrArg Subtype.val hl
        rw [← hlg]
        have hact := heq l (Additive.toMul v)
        change f (Additive.ofMul ((l : MulAut I) (Additive.toMul v))) =
          ((φ l : Matrix.GeneralLinearGroup (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) :
            Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
              (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) *ᵥ f v at hact
        rw [← hact]
        exact ⟨_, rfl⟩)
  exact ⟨(AddMonoidHom.ker_eq_bot_iff f).mp hker, (AddMonoidHom.range_eq_top).mp htop⟩

theorem natOmegaMinus_eight_of_equivariant_map {I : Type} [CommGroup I] [Finite I]
    [Fact (∀ x : I, x * x = 1)] {L : Subgroup (MulAut I)} (hirr : IsIrrOn L ⊤ ⊥)
    {e : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hK : Nat.card K = 2 ^ e) (hirrQ : ∀ x : K, x ^ 2 + b * x + c ≠ 0)
    (φ : ↥L ≃* ↥(StatedOmega (StatedQuadMinus 4 K b c)))
    (f : Additive I →+ (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K)) (hf : f ≠ 0)
    (heq : ∀ (l : ↥L) (w : I), f (Additive.ofMul ((l : MulAut I) w)) =
      ((φ l : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K) :
        Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K) *ᵥ f (Additive.ofMul w)) :
    NatOmegaMinus L ⊤ ⊥ 8 e := by
  let ψ : Additive I ≃+ (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K) := AddEquiv.ofBijective f
    (bijective_of_equivariant_omegaMinus (m := 4) (by norm_num) hirrQ hirr φ f hf heq)
  let θ : I ≃* Multiplicative (Additive I) :=
    { toFun := fun w => Multiplicative.ofAdd (Additive.ofMul w)
      invFun := fun w => Additive.toMul (Multiplicative.toAdd w)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨⟨4, rfl⟩, K, inferInstance, inferInstance, b, c, hK, hirrQ, ?_⟩
  exact realizes_nat_of_equiv θ φ ψ fun l w => heq l (Additive.toMul w)

theorem exists_equivariant_map_of_natural_isCurtisType
    {K E k W : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Field k]
    [CharP k 2] [Algebra E k] [AddCommGroup W] [Module E W] [Nontrivial W]
    {b c : K} (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hq : 4 ≤ Nat.card K)
    [Finite (spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c))]
    (ρ : Representation E (spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c)) W)
    (hsimp : CFSG.Quasithin.SmithCurtis.IsSimpleRep
      (CFSG.Theory.Representation.extendScalars k ρ))
    (φ : K →+* k) {y : k ⊗[E] W}
    {χ : spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c) → k}
    (ht : (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).IsCurtisType
      (CFSG.Theory.Representation.extendScalars k ρ) y χ 0)
    (hχ : ∀ h ∈ (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).H,
      χ h = SmallO8mCurtis.highestChar φ h) :
    ∃ f : W →+ (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K), f ≠ 0 ∧ ∀ g w,
      f (ρ g w) = (CFSG.LieType.Universal.Spin.Twisted.mat 4 g) *ᵥ f w := by
  classical
  let : Algebra K k := φ.toAlgebra
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let D := SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ
  let τ := CFSG.Theory.Representation.extendScalars k ρ
  have hnat := SmallO8mCurtis.naturalRep_isCurtisType hirrQ φ hq
  have hnat' : D.IsCurtisType (SmallO8mCurtis.naturalRep 4 b c φ)
      SmallO8mCurtis.highestVec χ 0 :=
    ⟨hnat.1, hnat.2.1, fun h hh => by rw [hχ h hh]; exact hnat.2.2.1 h hh, hnat.2.2.2⟩
  obtain ⟨β, hβ⟩ := D.iso_of_isCurtisType hsimp
    (SmallO8mCurtis.naturalRep_isSimple (by norm_num : 4 ≤ 4) hirrQ φ) ht hnat'
  obtain ⟨w, hw⟩ : ∃ w : W, w ≠ 0 := exists_ne 0
  let F : W →+ (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → k) :=
    { toFun := fun w => β ((1 : k) ⊗ₜ[E] w)
      map_zero' := by simp
      map_add' := fun w w' => by simp [TensorProduct.tmul_add] }
  have hF : F ≠ 0 := by
    intro h
    have hzero : β ((1 : k) ⊗ₜ[E] w) = 0 := DFunLike.congr_fun h w
    have htzero := β.injective (hzero.trans (map_zero β).symm)
    exact hw ((Module.FaithfullyFlat.one_tmul_eq_zero_iff E W (A := k) w).mp htzero)
  let : DistribMulAction (spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c)) W :=
    { smul := fun g w => ρ g w
      one_smul := fun w => by change ρ 1 w = w; rw [map_one]; rfl
      mul_smul := fun g h w => by change ρ (g * h) w = ρ g (ρ h w); rw [map_mul]; rfl
      smul_zero := fun g => map_zero (ρ g)
      smul_add := fun g w w' => map_add (ρ g) w w' }
  have hFeq : ∀ (g : spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c)) (w : W),
      F (g • w) =
      (CFSG.LieType.Universal.Spin.Twisted.mat 4 g).map (algebraMap K k) *ᵥ F w := by
    intro g w
    have h := hβ g ((1 : k) ⊗ₜ[E] w)
    rw [CFSG.Theory.Representation.extendScalars_apply, LinearMap.baseChange_tmul,
      SmallO8mCurtis.naturalRep_apply] at h
    exact h
  exact CFSG.LieType.SpecialLinear.exists_addHom_of_extend
    (fun g => CFSG.LieType.Universal.Spin.Twisted.mat 4 g) F hF hFeq

theorem natOmegaMinus_eight_of_natural_isCurtisType
    {I : Type} [CommGroup I] [Finite I] [Fact (∀ x : I, x * x = 1)]
    {L : Subgroup (MulAut I)} (hirr : IsIrrOn L ⊤ ⊥) {e : ℕ}
    {K E k W : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Field k]
    [CharP k 2] [Algebra E k] [AddCommGroup W] [Module E W] [Nontrivial W]
    {b c : K} (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hK : Nat.card K = 2 ^ e) (hq : 4 ≤ Nat.card K)
    [Finite (spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c))]
    (Θ : ↥L ≃* spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c))
    (θ : Additive I ≃+ W)
    (ρ : Representation E (spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c)) W)
    (hρ : ∀ (l : ↥L) (w : I),
      θ (Additive.ofMul ((l : MulAut I) w)) = ρ (Θ l) (θ (Additive.ofMul w)))
    (hsimp : CFSG.Quasithin.SmithCurtis.IsSimpleRep
      (CFSG.Theory.Representation.extendScalars k ρ))
    (φ : K →+* k) {y : k ⊗[E] W}
    {χ : spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c) → k}
    (ht : (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).IsCurtisType
      (CFSG.Theory.Representation.extendScalars k ρ) y χ 0)
    (hχ : ∀ h ∈ (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).H,
      χ h = SmallO8mCurtis.highestChar φ h) : NatOmegaMinus L ⊤ ⊥ 8 e := by
  obtain ⟨f, hf, heq⟩ := exists_equivariant_map_of_natural_isCurtisType hirrQ hq ρ hsimp φ ht hχ
  let F : Additive I →+ (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K) := f.comp θ.toAddMonoidHom
  have hF : F ≠ 0 := by
    intro h
    apply hf
    exact AddMonoidHom.ext fun w => by
      obtain ⟨v, rfl⟩ := θ.surjective w
      exact DFunLike.congr_fun h v
  let Γ := CFSG.SeitzReduction.SymplecticPilot.peRhoMEquiv (by norm_num : 4 ≤ 4) hirrQ
  refine natOmegaMinus_eight_of_equivariant_map hirr hK hirrQ (Θ.trans Γ) F hF ?_
  intro l w
  change f (θ (Additive.ofMul ((l : MulAut I) w))) =
    (CFSG.LieType.Universal.Spin.Twisted.mat 4 (Θ l)) *ᵥ f (θ (Additive.ofMul w))
  rw [hρ, heq]

theorem natural_isCurtisType_of_small_isometry_of_finrank_le_two
    {K W : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] {e : ℕ} (he : 2 ≤ e) (hK : Nat.card K = 2 ^ e)
    {b c : K} (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    [Finite (spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c))]
    (ρ : Representation (ZMod 2) (spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c)) W)
    [ρ.IsIrreducible] (hfaith : Function.Injective ρ)
    (a : W ≃ₗ[ZMod 2] W) (ha : a * a = 1) (ha1 : a ≠ 1)
    (α : MulAut (spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c)))
    (s : CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixIsometries
      (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinateQuadMinus
        4 K (by norm_num) b c)) (hs : s * s = 1)
    (hα : ∀ g, SmallO8mCurtis.coordinateEquiv hirrQ (α g) =
      CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixProjectiveConjugationHom
        (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinateQuadMinus
          4 K (by norm_num) b c)
        (CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixIsometryInclusion _ s)
        (SmallO8mCurtis.coordinateEquiv hirrQ g))
    (heq : ∀ g w, a (ρ g w) = ρ (α g) (a w))
    (hrank : Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - 1)) ≤ 2 * e + 1)
    (hcomm : ∀ d : EndRing ρ, ∀ w, a (d w) = d (a w))
    {k : Type} [Field k] [CharP k 2]
    [Algebra (Module.End (MonoidAlgebra (ZMod 2)
      (spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c))) ρ.asModule) k]
    {y : k ⊗[Module.End (MonoidAlgebra (ZMod 2)
      (spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c))) ρ.asModule] ρ.asModule}
    {χ : spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c) → k} {μ : Fin 3 → k}
    (hrankNatural : Module.finrank K
      (LinearMap.range ((CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixLinearIso
        s.val).toLinearMap - 1)) ≤ 2)
    (ht : (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).IsCurtisType
      (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)) y χ μ) :
    μ = 0 ∧ ∃ φ : K →+* k,
      ∀ h ∈ (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).H,
        χ h = SmallO8mCurtis.highestChar φ h := by
  exact SmallO8mLowRank.natural_isCurtisType_of_small_isometry_of_finrank_le_two
    he hK hirrQ ρ hfaith a ha ha1 α s hs hα heq hrank hcomm hrankNatural ht

theorem natural_isCurtisType_of_small_isometry
    {K W : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] {e : ℕ} (he : 2 ≤ e) (hK : Nat.card K = 2 ^ e)
    {b c : K} (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    [Finite (spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c))]
    (ρ : Representation (ZMod 2) (spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c)) W)
    [ρ.IsIrreducible] (hfaith : Function.Injective ρ)
    (a : W ≃ₗ[ZMod 2] W) (ha : a * a = 1) (ha1 : a ≠ 1)
    (α : MulAut (spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c)))
    (s : CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixIsometries
      (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinateQuadMinus
        4 K (by norm_num) b c)) (hs : s * s = 1)
    (hα : ∀ g, SmallO8mCurtis.coordinateEquiv hirrQ (α g) =
      CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixProjectiveConjugationHom
        (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinateQuadMinus
          4 K (by norm_num) b c)
        (CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixIsometryInclusion _ s)
        (SmallO8mCurtis.coordinateEquiv hirrQ g))
    (heq : ∀ g w, a (ρ g w) = ρ (α g) (a w))
    (hrank : Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - 1)) ≤ 2 * e + 1)
    (hcomm : ∀ d : EndRing ρ, ∀ w, a (d w) = d (a w))
    {k : Type} [Field k] [CharP k 2]
    [Algebra (Module.End (MonoidAlgebra (ZMod 2)
      (spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c))) ρ.asModule) k]
    {y : k ⊗[Module.End (MonoidAlgebra (ZMod 2)
      (spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c))) ρ.asModule] ρ.asModule}
    {χ : spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c) → k} {μ : Fin 3 → k}
    (ht : (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).IsCurtisType
      (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)) y χ μ) :
    μ = 0 ∧ ∃ φ : K →+* k,
      ∀ h ∈ (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).H,
        χ h = SmallO8mCurtis.highestChar φ h := by
  have hnatRank := SmallO8mIsometry.finrank_isometry_le_two_of_small hirrQ he hK ρ hfaith
    a ha α s hs hα heq hrank
  exact natural_isCurtisType_of_small_isometry_of_finrank_le_two he hK hirrQ ρ hfaith
    a ha ha1 α s hs hα heq hrank hcomm hnatRank ht

theorem natOmegaMinus_eight_of_small_endRing_linear_involution {I : Type} [CommGroup I]
    [Finite I] [Fact (∀ x : I, x * x = 1)] {L : Subgroup (MulAut I)} {e : ℕ} (he : 2 ≤ e)
    (hL : IsOmega8m ↥L e) (hirr : IsIrrOn L ⊤ ⊥) {t : MulAut I}
    (htN : t ∈ Subgroup.normalizer (L : Set (MulAut I))) (ht : t * t = 1) (ht1 : t ≠ 1)
    (hrank : CFSG.HardMathSupport.U4FF.disp t ≤ 2 * e + 1)
    (hcomm : ∀ d : EndRing (binRep L (MulEquiv.refl ↥L)), ∀ w : Additive I,
      binaryLin t (d w) = d (binaryLin t w)) : NatOmegaMinus L ⊤ ⊥ 8 e := by
  classical
  have : Nontrivial I := by
    obtain ⟨x, -, hx⟩ := SetLike.exists_of_lt hirr.1
    exact ⟨x, 1, fun h => hx (h ▸ Subgroup.one_mem _)⟩
  have hirrL : CFSG.LocalAnalysis.RankThreeUC.IsIrrOn L := fun U hU =>
    hirr.2.2.2 U hU bot_le le_top
  obtain ⟨hadm, K, hfield, hfinite, hK, b, c, hirrQ, ⟨φ₀⟩⟩ :=
    hL.statedClassicalModel (by decide)
  let : Field K := hfield
  let : Finite K := hfinite
  have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  let Γ := CFSG.SeitzReduction.SymplecticPilot.peRhoMEquiv (by norm_num : 4 ≤ 4) hirrQ
  let H := StatedOmega (StatedQuadMinus 4 K b c)
  have hscal : (StatedScalars (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K).subgroupOf H = ⊥ := by
    apply CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
      (CFSG.LieType.Universal.Spin.coe_quadMinus 4 K b c)
    refine ⟨CFSG.LieType.Universal.Spin.Twisted.eVec 4 0 +
      CFSG.LieType.Universal.Spin.Twisted.fVec 4 0, ?_⟩
    norm_num [CFSG.LieType.Universal.Spin.quadMinus_apply,
      CFSG.LieType.Universal.Spin.Twisted.eVec, CFSG.LieType.Universal.Spin.Twisted.fVec,
      Pi.single_apply, Fin.sum_univ_succ]
  let π : H ≃* StatedProj H :=
    ((QuotientGroup.quotientMulEquivOfEq hscal).trans QuotientGroup.quotientBot).symm
  let Θ := φ₀.trans (π.symm.trans Γ.symm)
  have : Finite (spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c)) :=
    CFSG.LieType.Steinberg.finite_spinGroup_of_ker _
      (CFSG.LieType.Universal.Spin.coe_ker_spinMatrix_quadMinus hirrQ)
  let ρ := binRep L Θ
  have hρirr : ρ.IsIrreducible := CFSG.HardMathSupport.U4FF.ClassFinal.binRep_isIrreducible Θ hirrL
  have : ρ.IsIrreducible := hρirr
  have hfaith : Function.Injective ρ := by
    intro g g' h
    apply Θ.symm.injective
    apply Subtype.ext
    apply binaryLin_injective
    ext w
    have h' := congrArg (fun f : Module.End (ZMod 2) (Additive I) => f w) h
    exact h'
  let α₀ := L.normalizerMonoidHom ⟨t, htN⟩
  let α := MulAut.congr Θ α₀
  have hα2 : α * α = 1 := by
    rw [← map_mul]
    have hα₀2 : α₀ * α₀ = 1 := by
      change L.normalizerMonoidHom ⟨t, htN⟩ * L.normalizerMonoidHom ⟨t, htN⟩ = 1
      rw [← map_mul]
      have htn : (⟨t, htN⟩ : Subgroup.normalizer (L : Set (MulAut I))) * ⟨t, htN⟩ = 1 :=
        Subtype.ext ht
      rw [htn, map_one]
    rw [hα₀2, map_one]
  obtain ⟨s, hs, hαs⟩ := SmallO8mCurtis.exists_isometry_of_involutive_aut hirrQ (by omega) hK α hα2
  have hatt : binaryLin t * binaryLin t = 1 := by rw [← map_mul, ht, map_one]
  have hat1 : binaryLin t ≠ 1 := fun h =>
    ht1 (binaryLin_injective (h.trans (map_one _).symm))
  have hconj : ∀ g w, binaryLin t (ρ g w) = ρ (α g) (binaryLin t w) := by
    intro g w
    have hval : (Θ.symm (α g) : MulAut I) = t * (Θ.symm g : MulAut I) * t⁻¹ := by
      have heq : Θ.symm (α g) = α₀ (Θ.symm g) := by simp [α]
      rw [heq]
      exact Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨t, htN⟩ (Θ.symm g)
    change binaryLin t (binaryLin (Θ.symm g : MulAut I) w) =
      binaryLin (Θ.symm (α g) : MulAut I) (binaryLin t w)
    rw [hval, map_mul, map_mul]
    simp
  have hcommρ : ∀ d : EndRing ρ, ∀ w, binaryLin t (d w) = d (binaryLin t w) := by
    intro d w
    let f := d.restrictScalars (ZMod 2)
    obtain ⟨d₀, hd₀⟩ := (CFSG.QuasithinUnique.Setup.SL2Modules.mem_endRing_iff
      (binRep L (MulEquiv.refl ↥L)) f).mpr (fun l v => by
        have h := d.map_smul
          (⟨ρ (Θ l), Algebra.subset_adjoin ⟨Θ l, rfl⟩⟩ : CFSG.QuasithinUnique.Setup.SL2Modules.spanAlg ρ) v
        change d (ρ (Θ l) v) = ρ (Θ l) (d v) at h
        rw [CFSG.HardMathSupport.U4FF.ClassFinal.binRep_eta_lin] at h
        exact h)
    have h := hcomm d₀ w
    rw [show d₀ w = d w from congrFun hd₀ w,
      show d₀ (binaryLin t w) = d (binaryLin t w) from congrFun hd₀ _] at h
    exact h
  let E := Module.End (MonoidAlgebra (ZMod 2)
    (spinGroup (CFSG.LieType.Universal.Spin.quadMinus 4 K b c))) ρ.asModule
  let k := AlgebraicClosure E
  have : CharP E 2 := CFSG.HardMathSupport.GuralnickMalle.endField_charP ρ 2
  have : CharP k 2 := charP_of_injective_algebraMap (algebraMap E k).injective 2
  let τ := CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)
  have hτ : CFSG.Quasithin.SmithCurtis.IsSimpleRep τ :=
    CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.isSimpleRep_extendScalars_endFieldRep ρ k
  have : Finite (CFSG.LieType.RootSystem.coxeterMatrix
      (isFiniteType_cartanB 3)).Group := finite_group (isFiniteType_cartanB 3)
  obtain ⟨y, χ, μ, htype⟩ := (SmallO8mCurtis.curtisDatum 4 (by norm_num) hirrQ).exists_isCurtisType
    (SmallO8mCurtis.curtisDatum_splitOver hirrQ) hτ
  obtain ⟨hμ, φ, hχ⟩ := natural_isCurtisType_of_small_isometry he hK hirrQ ρ hfaith
    (binaryLin t) hatt hat1 α s hs hαs hconj hrank hcommρ htype
  rw [hμ] at htype
  have : Nontrivial ρ.asModule := by
    obtain ⟨v, w, hvw⟩ := (inferInstance : Nontrivial (Additive I)).exists_pair_ne
    exact ⟨ρ.asModuleEquiv.symm v, ρ.asModuleEquiv.symm w,
      fun h => hvw (ρ.asModuleEquiv.symm.injective h)⟩
  exact natOmegaMinus_eight_of_natural_isCurtisType hirr hirrQ hK (by
    rw [hK]; exact Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) he)
    Θ ρ.asModuleEquiv.symm.toAddEquiv (CFSG.endFieldRep ρ)
    (fun l w => by
      rw [CFSG.endFieldRep_apply]
      change ρ.asModuleEquiv.symm (Additive.ofMul ((l : MulAut I) w)) =
        ρ.asModuleEquiv.symm (ρ (Θ l) (Additive.ofMul w))
      rw [CFSG.HardMathSupport.U4FF.ClassFinal.binRep_eta]) hτ φ htype hχ

theorem natOmegaMinus_eight_of_small_involution {I : Type} [CommGroup I] [Finite I]
    [Fact (∀ x : I, x * x = 1)] {L : Subgroup (MulAut I)} {e : ℕ} (he : 2 ≤ e)
    (hL : IsOmega8m ↥L e) (hirr : IsIrrOn L ⊤ ⊥) {t : MulAut I}
    (htN : t ∈ Subgroup.normalizer (L : Set (MulAut I))) (ht : t * t = 1) (ht1 : t ≠ 1)
    (hrank : CFSG.HardMathSupport.U4FF.disp t ≤ 2 * e + 1) :
    NatOmegaMinus L ⊤ ⊥ 8 e := by
  exact natOmegaMinus_eight_of_small_endRing_linear_involution he hL hirr htN ht ht1 hrank
    (commute_endRing_of_isOmega8m_small_involution he hL hirr htN ht hrank)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
