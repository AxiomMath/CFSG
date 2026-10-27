module

public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitTwE6SplitFrame
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitTwE6
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6SplitNormalizer
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6Split
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusFrameFusion
import CFSG.LocalAnalysis.StandardType.GGTableBTwE6RankOuter
import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaCenter
import CFSG.LocalAnalysis.StandardType.GGTwE6ToralCent

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem excPlusFrameModelOn_twE6Split
    {n p : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) [Fact p.Prime] (hp5 : 5 ≤ p) (hpn : p ∣ 2 ^ n - 1) :
    GGExcPlusFrameModelOn .F4 p 4 ↥(graphFixedRootGroup TwistTag.E6 K σ) := by
  classical
  have hp : p.Prime := Fact.out
  have hpK : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    have h1 : 2 ^ n - 1 ∣ (2 ^ n) ^ 2 - 1 := by
      simpa using Nat.sub_dvd_pow_sub_pow (2 ^ n) 1 2
    exact hpn.trans h1
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' p hpK
  have hζ : ζ ^ p = 1 := hζo ▸ pow_orderOf_eq_one ζ
  have hζσ : σ (ζ : K) = ζ := by
    obtain ⟨k, hk⟩ := hpn
    have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
    have hq : 2 ^ n = p * k + 1 := by omega
    rw [hσ, ← Units.val_pow_eq_pow_val, hq, pow_add, pow_mul, hζ, one_pow, one_mul, pow_one]
  choose m hm using fun i => ExcFrames.exists_realization_twE6Split σ hζ hζσ (p := p) i
  set ι := ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ with hιdef
  have hιinj : Function.Injective ι := ExcFrames.twE6SplitFrameHom_injective σ hp5 hζo hζ hζσ
  have hEl : IsElemAbelian p ι.range := by
    refine ⟨IsMulCommutative.of_comm fun a b => Subtype.ext ?_, fun x hx => ?_⟩
    · obtain ⟨u, hu⟩ := a.2
      obtain ⟨v, hv⟩ := b.2
      change (a : ↥(graphFixedRootGroup TwistTag.E6 K σ)) * b = b * a
      rw [← hu, ← hv, ← map_mul, ← map_mul, mul_comm]
    · obtain ⟨u, rfl⟩ := hx
      rw [← map_pow, ← ofAdd_toAdd u, ← ofAdd_nsmul, ZModModule.char_nsmul_eq_zero, ofAdd_zero,
        map_one]
  have hcard : Nat.card ι.range = p ^ 4 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hιinj).toEquiv,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin Tag.F4.rank → ZMod p) ≃ _),
      Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  obtain ⟨e⟩ := TwE6Rank.exists_mulEquiv_graphFixedRootGroup hn hK σ hσ
  have hT : SylowTorus ↥(graphFixedRootGroup TwistTag.E6 K σ) p 4 :=
    (sylowTorus_recipeR_split hn hK hp hp5 hpn).of_mulEquiv e
  intro E _hE _hcardE hsc
  obtain ⟨c, hc⟩ := exists_conj_eq_of_selfCentralizing_of_sylowTorus hp hT hEl hcard _hE hsc
  refine ⟨(MulAut.conj c).toMonoidHom.comp ι, fun i => c * m i * c⁻¹,
    (MulAut.conj c).injective.comp hιinj, by rw [MonoidHom.range_comp, hc], ?_, ?_⟩
  · intro i s
    have h1 := hm i s
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← h1]
    group
  · intro g hg
    rw [hc, ← Subgroup.map_equiv_normalizer_eq] at hg
    obtain ⟨x, hx, rfl⟩ := hg
    have hxs : ∀ s, x * ι s * x⁻¹ ∈ ι.range :=
      fun s => (Subgroup.mem_normalizer_iff.mp hx _).mp ⟨s, rfl⟩
    have hxC : (x : ModGL TwistTag.E6.tag K) ∈ adjointGroup Tag.E6 K :=
      TwE6Toral.graphFixedRootGroup_le_adjointGroup x.2
    have hxMono : (x : ModGL TwistTag.E6.tag K) ∈ monomialSubgroup Tag.E6 K := by
      refine ExcFrames.mem_monomialSubgroup_of_conj_e6SplitTorsion hp5 hζo hxC fun v hv => ?_
      obtain ⟨c, hc, h05, h24, rfl⟩ := hv
      obtain ⟨s, hs⟩ := ExcFrames.exists_frameDiag_twE6SplitTheta_eq hp5 hζo hζ hc h05 h24
      obtain ⟨t, ht⟩ := hxs (Multiplicative.ofAdd s)
      obtain ⟨c', hc', h05', h24', hc'eq⟩ :=
        ExcFrames.frameDiag_twE6SplitTheta_eq_rootDiagUnit hζ (Multiplicative.toAdd t)
      refine ⟨c', hc', h05', h24', ?_⟩
      have h1 := congrArg (fun y : ↥(graphFixedRootGroup TwistTag.E6 K σ) =>
        (y : ModGL TwistTag.E6.tag K)) ht
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
      rw [← hc'eq, ← hs]
      exact h1.symm
    have hxM : (x : ModGL TwistTag.E6.tag K) ∈ graphFixedRootMonomial TwistTag.E6 K σ :=
      Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hxMono,
        graphFixedRootGroup_le TwistTag.E6 K σ x.2⟩, x.2⟩
    refine ⟨foldedWeylEquiv TwistTag.E6
      ⟨graphFixedRootWeylHom TwistTag.E6 K σ ⟨(x : ModGL TwistTag.E6.tag K), hxM⟩,
        (graphFixedRootWeylHom_range TwistTag.E6 K σ).le
          ⟨⟨(x : ModGL TwistTag.E6.tag K), hxM⟩, rfl⟩⟩, fun s => ?_⟩
    have h2 := ExcFrames.twE6SplitFrameHom_conj σ hζ hζσ hxM s
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show c * x * c⁻¹ * (c * ι (Multiplicative.ofAdd s) * c⁻¹) * (c * x * c⁻¹)⁻¹ =
        c * (x * ι (Multiplicative.ofAdd s) * x⁻¹) * c⁻¹ by group, h2]

theorem ggTorusReflGenW_twE6Split
    {n p : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpn : p ∣ 2 ^ n - 1) :
    GGTorusReflGenW p 4 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  haveI : CharP K 2 := charP_two_of_card (K := K) (m := 2 * n) (by rw [hK, ← pow_mul, mul_comm])
  obtain ⟨e⟩ := TwE6Rank.exists_mulEquiv_graphFixedRootGroup hn hK (iterateFrobenius K 2 n)
    (fun c => iterateFrobenius_def 2 n c)
  exact ggTorusReflGenW_of_excPlusModel hp hp2
    (ggExcPlusWeylModelSCr_of_frameModelOn hp (TwE6Delta.center_recipeR_eq_bot hn hK)
      (fun φ hφ hφp => TwE6Delta.ggOutdiagPrime_twE6 hn hK hp hp3 φ hφ hφp)
      (TwE6Delta.ggCenterPrime_twE6 hn hK hp hp2 hp3)
      ((excPlusFrameModelOn_twE6Split hn hK (iterateFrobenius K 2 n)
        (fun c => iterateFrobenius_def 2 n c) hp5 hpn).of_mulEquiv e))

theorem ggTwE6SplitWeylInput_holds :
    GGTwE6SplitWeylInput :=
  fun _ _ _ _ _ hn hK hp hp5 hpn => ggTorusReflGenW_twE6Split hn hK hp hp5 hpn

theorem ggNbrTableBWeylNonSplitOn_twE6 :
    GGNbrTableBWeylNonSplitOn GGNbrNonSplitTwE6Label :=
  ggNbrTableBWeylNonSplitOn_twE6_of ggTwE6SplitWeylInput_holds

end CFSG.StandardType

end
