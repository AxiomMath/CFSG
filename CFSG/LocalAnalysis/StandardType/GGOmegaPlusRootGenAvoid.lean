module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenAvoidKG
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenKGDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylNSRootGen
public import CFSG.LocalAnalysis.StandardType.GGOmegaPlusCentrallyClosed
public import CFSG.LocalAnalysis.StandardType.GGOmegaPlusRootGenDefs
import CFSG.LocalAnalysis.StandardType.GGTorusRootGenAvoidModel
import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticOmega
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaPlus
import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenAvoid
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySp
import CFSG.LieType.Universal.SpinOmega.Center
import CFSG.LocalAnalysis.StandardType.GGOmegaPlusRootGenWeyl
import CFSG.LocalAnalysis.StandardType.GGOmegaPlusRootGenComp
import CFSG.LocalAnalysis.StandardType.GGOmegaPlusRootGenGen
import CFSG.LocalAnalysis.StandardType.GGOmegaPlusRootGenConj

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open

theorem ggTorusRootGenAvoidKG_statedOmegaPlus {K : Type} [Field K] [Finite K] {n m p : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (hm : 4 ≤ m) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) :
    GGTorusRootGenAvoidKG p m (StatedOmega (StatedQuadPlus m K))
      (Set.range (MulAut.conj : StatedOmega (StatedQuadPlus m K) →*
        MulAut (StatedOmega (StatedQuadPlus m K)))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero m := ⟨by omega⟩
  have : CharP K 2 := charP_two_of_card hK
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hpK : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units]
    exact hpq
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' p hpK
  have hζ : ζ ^ p = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  have hW : ∀ x : OmPlusIdx m, ∃ w : StatedOmega (StatedQuadPlus m K),
      (w : GL (Fin m ⊕ Fin m) K) ∈ omPlusBlock K x ∧
        ∀ f, w * omPlusTorus hζ f * w⁻¹ = omPlusTorus hζ (omPlusRefl p x f) := by
    intro x
    obtain ⟨w, hw, hwf⟩ := exists_mem_omPlusBlock_conj hζ x
    exact ⟨⟨w, omPlusBlock_le h4 x hw⟩, hw, fun f => Subtype.ext (hwf f)⟩
  choose w hw hw' using hW
  have hτ : Function.Injective (omPlusTorus hζ :
      (Fin m → Multiplicative (ZMod p)) →* StatedOmega (StatedQuadPlus m K)) := by
    intro x y h
    apply omPlusTorusGL_injective hζ hζo
    simpa only [coe_omPlusTorus] using congrArg Subtype.val h
  have hinj : ∀ (L' : Type) [Group L'] [Finite L']
      (ψ : L' →* StatedOmega (StatedQuadPlus m K)), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → Function.Injective ψ := by
    intro L' _ _ ψ hψ hker hperf
    have h := rPlus_injective_of_cover hK hn (by omega) L'
      ((rPlusEquivStatedOmega K m).symm.toMonoidHom.comp ψ)
      ((rPlusEquivStatedOmega K m).symm.surjective.comp hψ)
      (fun l hl => hker (by simpa [MonoidHom.mem_ker] using hl)) hperf
    exact fun x y hxy => h (congrArg (rPlusEquivStatedOmega K m).symm hxy)
  have hZ : Subgroup.center (StatedOmega (StatedQuadPlus m K)) = ⊥ := by
    rw [CFSG.LieType.Universal.Spin.center_statedOmega_quadPlus (by omega)]
    refine TableBOrth.scalars_subgroupOf_omega_eq_bot (Q := StatedQuadPlus m K)
      (v₀ := Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1) (fun x v => ?_) ?_
    · rw [← CFSG.LieType.Universal.Spin.coe_quadPlus, QuadraticMap.map_smul, smul_eq_mul, sq]
    · rw [← CFSG.LieType.Universal.Spin.coe_quadPlus,
        CFSG.LieType.Universal.Spin.quadPlus_apply]
      simp [Pi.single_apply]
  have htop : ∀ X : Subgroup (StatedOmega (StatedQuadPlus m K)),
      StatedOmega (StatedQuadPlus m K) ≤ X.map (StatedOmega (StatedQuadPlus m K)).subtype →
        X = ⊤ := by
    intro X hX
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨y, hy, hyx⟩ := hX x.2
    have hxy : y = x := Subtype.ext hyx
    rwa [← hxy]
  have : Nonempty (OmPlusIdx m) :=
    ⟨(⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [Fin.lt_def]⟩, false)⟩
  refine ggTorusRootGenAvoidKG_of_torusModel (ι := OmPlusIdx m) hp hinj hZ (fun _ h => h)
    (omPlusTorus hζ) hτ
    (fun E hE hr _ => exists_mulEquiv_eq_map_omPlusTorus hp2 hζ hζo hE hr) w (omPlusRefl p)
    (fun x => (omPlusBlock K x).subgroupOf (StatedOmega (StatedQuadPlus m K)))
    hw' omPlusRefl_mul_self (card_fix_omPlusRefl hp hp2) (omPlusRefl_injective hp hp2)
    (fun x => Subgroup.mem_subgroupOf.mpr (hw x)) (isComponentOf_omPlusBlock h4 hp hp2 hζ hζo)
    (dvd_card_omPlusBlock h4 hpq) fun x₀ => ?_
  apply htop
  refine (statedOmega_quadPlus_le_iSup_omPlusBlock_ne hm hK h4 x₀).trans
    (iSup₂_le fun x hx => ?_)
  intro g hg
  exact ⟨⟨g, omPlusBlock_le h4 x hg⟩, Subgroup.mem_iSup_of_mem x
    (Subgroup.mem_iSup_of_mem hx (Subgroup.mem_subgroupOf.mpr hg)), rfl⟩

theorem ggTorusRootGenAvoidKG_omegaPlus {K : Type} [Field K] [Finite K] {n m p : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (hm : 4 ≤ m) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) :
    GGTorusRootGenAvoidKG p m (OrthRest.RPlus K m) (LargeEvenInnSet (OrthRest.RPlus K m)) := by
  have : CharP K 2 := charP_two_of_card hK
  have : NeZero m := ⟨by omega⟩
  refine ggTorusRootGenAvoidKG_of_mulEquiv (rPlusEquivStatedOmega K m) (fun φ hφ => ?_)
    (ggTorusRootGenAvoidKG_statedOmegaPlus hK hn hm hp hp2 hpq)
  obtain ⟨x, rfl⟩ := hφ
  refine ⟨rPlusEquivStatedOmega K m x, MulEquiv.ext fun y => ?_⟩
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

theorem largeEvenLabelAll_rootGenAvoidKG_omegaPlus {p l n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ∣ 2 ^ n - 1) (hl : 4 ≤ l) :
    LargeEvenLabelAll ⟨.D, l, n⟩ fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGTorusRootGenAvoidKG p r R I := by
  refine largeEvenLabelAll_omegaPlus rfl hl fun K _ _ _ hK => ?_
  have hpq : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact hpn
  have hn : 2 ≤ n := by
    by_contra h
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    interval_cases n
    · rw [hK] at h1
      norm_num at h1
    · norm_num at hpn
      exact hp.one_lt.ne' hpn
  exact ⟨l, TableBSymp.ggTorusLift_omegaPlus hp hp2 hpq (by omega),
    ggTorusRootGenAvoidKG_omegaPlus hK hn hl hp hp2 hpq⟩

@[expose] def GGRootGenOrthSplitLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  p ∣ 2 ^ lab.n - 1 ∧ (lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank

theorem ggRootGenKGAvoidOn_orthSplit :
    GGRootGenKGAvoidOn GGRootGenOrthSplitLabel := by
  rintro p ⟨t, l, n⟩ hp hp2 hlab ⟨hpn, ht | ht, hl⟩
  · dsimp only at ht hpn hl
    subst ht
    exact largeEvenLabelAll_rootGenAvoidKG_omegaPlus hp hp2 hpn hl
  · dsimp only at ht hpn hl
    subst ht
    have hn1 : 1 ≤ n := hlab.1
    have hn : 2 ≤ n := by
      by_contra h
      have hn' : n = 1 := by omega
      subst hn'
      norm_num at hpn
      exact hp.one_lt.ne' hpn
    exact largeEvenLabelAll_rootGenAvoidKG_omegaMinus hp hp2 hpn hn hl

end CFSG.StandardType

end
