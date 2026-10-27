module

public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitExcPlusFrame
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitFamilies
import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusFrame
import CFSG.LocalAnalysis.StandardType.GGTwE6WeylRealize
import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusSCFive
import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusSCSeven
import CFSG.LocalAnalysis.StandardType.GGTableBTwE6RankOuter
import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaCenter
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6Lift

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem excPlusFrameModelOn_twE6Plus
    {f p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hf : 1 ≤ f) (hpq : p ∣ 2 ^ f + 1) (K : Type) [Field K]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    GGExcPlusFrameModelOn TwistTag.E6.tag p 5 (graphFixedRootGroup TwistTag.E6 K σ) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  haveI : CharP K 2 := charP_two_of_card (K := K) (m := 2 * f) (by rw [hK, ← pow_mul, mul_comm])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  let Fr : AlgebraicClosure K →+* AlgebraicClosure K := iterateFrobenius (AlgebraicClosure K) 2 f
  have hFr : ∀ c, Fr c = c ^ (2 ^ f) := fun c => iterateFrobenius_def 2 f c
  obtain ⟨ζK, hζ, g₀, T, ι₀, -, hg₀C, hg₀, hι₀, hbase, hTcomm, hrangeT, htors, -, hcent⟩ :=
    ExcFrames.exists_langFrame hp5 hf hpq K hK σ hσ (AlgebraicClosure K) Fr hFr
  obtain ⟨m, -, hm⟩ :=
    ExcFrames.exists_langFrame_weyl hf K hK σ hσ (AlgebraicClosure K) Fr hFr hζ hg₀C hg₀ ι₀ hbase
  have hle : graphFixedRootGroup TwistTag.E6 K σ ≤ adjointGroup TwistTag.E6.tag K :=
    (graphFixedRootGroup_le TwistTag.E6 K σ).trans inf_le_left
  intro E hE hcard hsc
  have hFsc : ∀ c : graphFixedRootGroup TwistTag.E6 K σ, (∀ a ∈ ι₀.range, c * a = a * c) →
      c ^ p = 1 → c ∈ ι₀.range := fun c hc hcp =>
    htors c (hcent c fun x hx => hc x hx) hcp
  obtain ⟨c, hc⟩ : ∃ c, E = ι₀.range.map (MulAut.conj c).toMonoidHom := by
    by_cases h7 : 7 ≤ p
    · obtain ⟨c, hc⟩ := ExcFrames.twistedE6SCUnique_ge_seven h7 hf hpq K hK σ hσ hι₀ hTcomm
        hrangeT htors hcent hE hsc
      exact ⟨c, hc.symm⟩
    · have hp5' : p = 5 := by
        have h56 : p = 5 ∨ p = 6 := by omega
        rcases h56 with h | h
        · exact h
        · exact absurd (h ▸ hp) (by norm_num)
      subst hp5'
      have hFel : IsElemAbelian 5 ι₀.range := by
        refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
        · obtain ⟨s, hs⟩ := a.2
          obtain ⟨t, ht⟩ := b.2
          apply Subtype.ext
          change (a : graphFixedRootGroup TwistTag.E6 K σ) * b = b * a
          rw [← hs, ← ht, ← map_mul, ← map_mul, mul_comm]
        · obtain ⟨s, rfl⟩ := hx
          rw [← map_pow]
          have : s ^ 5 = 1 := by
            apply Multiplicative.toAdd.injective
            funext i
            simp only [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
            have h5z : ((5 : ℕ) : ZMod 5) = 0 := ZMod.natCast_self 5
            rw [h5z, zero_mul]
          rw [this, map_one]
      have hFcard : 5 ^ 4 ≤ Nat.card ι₀.range := by
        rw [Nat.card_congr (MonoidHom.ofInjective hι₀).toEquiv.symm,
          Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
        decide
      exact ExcFrames.twistedE6SCUnique_five hf hpq K hK σ hσ hFel hFcard hFsc hE
        (le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) hcard) hsc
  refine ⟨(MulAut.conj c).toMonoidHom.comp ι₀, fun i => c * m (simple TwistTag.E6.tag i) * c⁻¹,
    (MulAut.conj c).injective.comp hι₀, by rw [MonoidHom.range_comp, hc], ?_, ?_⟩
  · intro i s
    have h1 := hm (simple TwistTag.E6.tag i) s
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← h1]
    group
  · intro g hg
    rw [hc, ← Subgroup.map_equiv_normalizer_eq] at hg
    obtain ⟨x, hx, rfl⟩ := hg
    let ι₀' := (Subgroup.inclusion hle).comp ι₀
    have hι₀' : Function.Injective ι₀' := (Subgroup.inclusion_injective hle).comp hι₀
    have hx' : Subgroup.inclusion hle x ∈ Subgroup.normalizer (ι₀'.range : Set _) := by
      rw [MonoidHom.range_comp]
      exact Subgroup.le_normalizer_map _ ⟨x, hx, rfl⟩
    obtain ⟨u, hu⟩ := exists_weyl_of_mem_normalizer_of_frame hg₀C hι₀' rfl
      (fun s => hbase s) hx'
    refine ⟨u, fun s => ?_⟩
    have hxs : x * ι₀ (Multiplicative.ofAdd s) * x⁻¹ =
        ι₀ (Multiplicative.ofAdd (TableBExc.torusAct TwistTag.E6.tag p u s)) :=
      Subgroup.inclusion_injective hle (by simpa [ι₀'] using hu s)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hxs]
    group


theorem ggTorusReflGenW_twE6Plus
    {n p : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpn : p ∣ 2 ^ n + 1) :
    GGTorusReflGenW p 5 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  haveI : CharP K 2 := charP_two_of_card (K := K) (m := 2 * n) (by rw [hK, ← pow_mul, mul_comm])
  obtain ⟨e⟩ := TwE6Rank.exists_mulEquiv_graphFixedRootGroup hn hK (iterateFrobenius K 2 n)
    (fun c => iterateFrobenius_def 2 n c)
  exact ggTorusReflGenW_of_excPlusModel hp hp2
    (ggExcPlusWeylModelSCr_of_frameModelOn hp (TwE6Delta.center_recipeR_eq_bot hn hK)
      (fun φ hφ hφp => TwE6Delta.ggOutdiagPrime_twE6 hn hK hp hp3 φ hφ hφp)
      (TwE6Delta.ggCenterPrime_twE6 hn hK hp hp2 hp3)
      ((excPlusFrameModelOn_twE6Plus hp hp5 hn hpn K hK (iterateFrobenius K 2 n)
        (fun c => iterateFrobenius_def 2 n c)).of_mulEquiv e))

theorem largeEvenLabelAll_reflGenW_twE6Plus
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGTorusReflGenW p r R I) := by
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    have h4 : p ≠ 4 := fun h4 => by subst h4; exact absurd hp (by norm_num)
    omega
  have hW : LargeEvenLabelAll lab fun R _ I _ => GGTorusReflGenW p 5 R I :=
    TwE6Delta.labelAll h.1 fun _ _ _ hK => ggTorusReflGenW_twE6Plus hlab.1 hK hp hp5 h.2
  refine (largeEvenLabelAll_and (largeEvenLabelAll_torusLift_twE6Add_holds hp hlab h) hW).mono
    fun _ _ _ _ ⟨hl, hw⟩ _ _ => ⟨5, ?_, hw⟩
  rwa [TwE6Delta.liftRank_of_ne hp3] at hl

end CFSG.StandardType

end
