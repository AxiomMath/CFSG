module

public import CFSG.RankThree.PartTwo.Sec8.Hering88FNonsolv
import CFSG.HardMathSupport.Lang.E27Lie.TrialityTwo
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
public import CFSG.RankThree.PartTwo.Sec8.Item812Res7ProofD4N

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def G2TwoCentThreeSolvable : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
    ∀ g : ↥(adjointGroup .G2 K), g ^ 3 = 1 → g ≠ 1 →
      Group.IsSolvable ↥(Subgroup.centralizer ({g} : Set ↥(adjointGroup .G2 K)))

namespace Hering88F


theorem center_eq_bot_of_case1 {Q : Type} [Group Q] {m : ℕ}
    (h : IsoTrialityD4 Q m ∨ IsoGTwoEven Q (3 * m)) : Subgroup.center Q = ⊥ := by
  rcases h with hD | ⟨K, _, _, hK, ⟨e⟩⟩
  · obtain ⟨-, K, _, _, σ, -, -, ⟨e⟩⟩ := Item812Res7.exists_trialityD4_model hD
    rw [eq_bot_iff]
    intro z hz
    have hz' : e z ∈ Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
      (MulEquivClass.apply_mem_center_iff e).2 hz
    rw [exceptional_fixed_center_trivial TwistTag.D4 K σ, Subgroup.mem_bot] at hz'
    exact Subgroup.mem_bot.2 (e.injective (hz'.trans (map_one e).symm))
  · rw [eq_bot_iff]
    intro z hz
    have hz' : e z ∈ Subgroup.center (adjointGroup .G2 K) :=
      (MulEquivClass.apply_mem_center_iff e).2 hz
    rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hz'
    exact Subgroup.mem_bot.2 (e.injective (hz'.trans (map_one e).symm))

theorem isSolvable_of_isoPGUThree_two {X : Type} [Group X] [Finite X]
    (h : IsoPGUThree X (2 ^ 1)) : Group.IsSolvable X := by
  have hc := CFSG.HardMathSupport.Lang.E27Lie.card_isoPGUThree le_rfl h
  refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
  have h216 : (2 ^ 1) ^ 3 * ((2 ^ 1) ^ 2 - 1) * ((2 ^ 1) ^ 3 + 1) = 2 ^ 3 * 3 ^ 3 := by
    norm_num
  rw [hc, h216, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
    Nat.primeFactors_prime_pow (by norm_num) Nat.prime_three]
  exact (Finset.card_union_le _ _).trans (by simp)

theorem isSolvable_inf_barCentralizer_of_isoGTwoEven_one (hG : G2TwoCentThreeSolvable)
    {G : Type} [Group G] [Finite G] {Y : Subgroup G} {c d : G}
    (hcN : c ∈ Subgroup.normalizer (Y : Set G)) (hdN : d ∈ Subgroup.normalizer (Y : Set G))
    (hcd : c * d = d * c) (hd3 : d ^ 3 = 1)
    (hdin : KFacts.IsInnerAut (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩)))
    (hdne : Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩) ≠ 1)
    (hZ : Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) = ⊥)
    (hH : IsoGTwoEven (barCentralizer (Subgroup.zpowers c) Y) 1) :
    Group.IsSolvable ↥(barCentralizer (Subgroup.zpowers c) Y ⊓
      barCentralizer (Subgroup.zpowers d) Y) := by
  classical
  set α := Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩) with hα
  set β := Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨c, hcN⟩) with hβ
  have hinj := Item812Res7.conj_injective_of_center_trivial hZ
  obtain ⟨g, hg⟩ := hdin
  have hgα : MulAut.conj g = α := hg
  have hβα : β * α = α * β := by
    rw [hα, hβ, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
    exact congrArg (fun x => Sec4.thetaQuotMulAut Y (Sec4.compAction Y x))
      (Subtype.ext hcd)
  have hβg : β g = g := by
    have h1 := KFacts.mul_mulAutConj_mul_inv β g
    rw [hgα, hβα, mul_inv_cancel_right] at h1
    exact (hinj (by rw [hgα]; exact h1)).symm
  have hgH : g ∈ barCentralizer (Subgroup.zpowers c) Y :=
    (KFacts.mem_barCentralizer_zpowers_iff hcN g).mpr hβg
  have hα3 : α ^ 3 = 1 := by
    rw [hα, ← map_pow, ← map_pow]
    have : (⟨d, hdN⟩ : Subgroup.normalizer (Y : Set G)) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
    rw [this, map_one, map_one]
  have hg3 : g ^ 3 = 1 := by
    apply hinj
    rw [map_pow, hgα, hα3, map_one]
  have hg1 : g ≠ 1 := by
    rintro rfl
    apply hdne
    rw [← hgα]
    exact map_one _
  obtain ⟨K, _, _, hK, ⟨eG⟩⟩ := hH
  rw [pow_one] at hK
  set gH : ↥(barCentralizer (Subgroup.zpowers c) Y) := ⟨g, hgH⟩ with hgHdef
  have hgH3 : gH ^ 3 = 1 := Subtype.ext (by simpa [hgHdef] using hg3)
  have hgH1 : gH ≠ 1 := fun h => hg1 (congrArg Subtype.val h)
  have hcs := hG K hK (eG gH) (by rw [← map_pow, hgH3, map_one])
    (fun h => hgH1 (eG.injective (h.trans (map_one eG).symm)))
  set f₀ : ↥(barCentralizer (Subgroup.zpowers c) Y ⊓ barCentralizer (Subgroup.zpowers d) Y) →*
      ↥(adjointGroup .G2 K) :=
    (eG : ↥(barCentralizer (Subgroup.zpowers c) Y) →* ↥(adjointGroup .G2 K)).comp
      (Subgroup.inclusion inf_le_left) with hf₀
  have hf₀mem : ∀ x, f₀ x ∈ Subgroup.centralizer ({eG gH} : Set ↥(adjointGroup .G2 K)) := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hx : x.1 ∈ barCentralizer (Subgroup.zpowers d) Y := x.2.2
    rw [KFacts.mem_barCentralizer_zpowers_iff hdN, ← hα, ← hgα, MulAut.conj_apply,
      mul_inv_eq_iff_eq_mul] at hx
    change eG (Subgroup.inclusion inf_le_left x) * eG gH =
      eG gH * eG (Subgroup.inclusion inf_le_left x)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hx.symm
  set f := f₀.codRestrict _ hf₀mem with hf
  have hfinj : Function.Injective f := by
    intro x y hxy
    have h1 : f₀ x = f₀ y := congrArg Subtype.val hxy
    have h2 := eG.injective h1
    exact Subtype.ext (congrArg
      (fun z : ↥(barCentralizer (Subgroup.zpowers c) Y) => (z : Y ⧸ aschbacherSolvableCore 3 Y))
      h2)
  haveI := hcs
  exact Group.isSolvable_of_isSolvable_injective hfinj

theorem false_of_small (h45 : Sec4.Item4_5) (hF : KF84Field) (hG : G2TwoCentThreeSolvable)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G}
    {X : Subgroup G} {n : ℕ} (h : Sec8Pair G A c L a b X n) (hn2 : 2 ≤ n)
    {Y : Subgroup G} (hIJ : sec8I L a ⊔ sec8J X a ≤ Y)
    (hcN : c ∈ Subgroup.normalizer (Y : Set G))
    (hZ : Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) = ⊥)
    (hH : IsoGTwoEven (barCentralizer (Subgroup.zpowers c) Y) 1 ∨
      IsoPGUThree (barCentralizer (Subgroup.zpowers c) Y) (2 ^ 1))
    {d : G} (hdcl : d ∈ Subgroup.closure ({c, b} : Set G)) (hdA : d ∈ A) (hd3 : d ^ 3 = 1)
    (hdN : d ∈ Subgroup.normalizer (Y : Set G))
    (hin : KFacts.IsInnerAut (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩)))
    (hne : Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩) ≠ 1) : False := by
  obtain ⟨hAc, -⟩ := Hering88C.pair_commute_pow_three h
  have hcd : c * d = d * c := hAc c h.mem_A d hdA
  refine not_isSolvable_inf_barCentralizer h45 hF h hn2 hIJ hcN hdcl hdA hd3 hdN ?_
  rcases hH with hG2 | hP
  · exact isSolvable_inf_barCentralizer_of_isoGTwoEven_one hG hcN hdN hcd hd3 hin hne hZ hG2
  · haveI : Group.IsSolvable ↥(barCentralizer (Subgroup.zpowers c) Y) :=
      isSolvable_of_isoPGUThree_two hP
    exact Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (inf_le_left :
        barCentralizer (Subgroup.zpowers c) Y ⊓ barCentralizer (Subgroup.zpowers d) Y ≤
          barCentralizer (Subgroup.zpowers c) Y))

end Hering88F

end CFSG.RankThree.PartTwo.Sec8
