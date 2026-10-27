module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_3.ExcSz
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_3.ExcInner
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_3.ExcOuter
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallL2
public import CFSG.Quasithin.Background.RonanE42Small
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_3.Statement
public import CFSG.Quasithin.Vol2.Ch11SecOE2D
public import CFSG.Quasithin.Background.SmithB45L2Main
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJModel
public import CFSG.Quasithin.Background.E3MParamAttained
public import CFSG.Timmesfeld.TransvectionActions.InvolutionFixedSpace

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3

open CFSG.Quasithin
open CFSG.RankThree.FFModules
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
open scoped MatrixGroups

theorem finrank_eq_of_mParam_eq_add_two {F : Type} [Field F] [Fintype F] [CharP F 2] {n : ℕ}
    (hn : 3 ≤ n) (hn4 : n ≠ 4) (hF : Fintype.card F = 2 ^ n) {I : Type} [CommGroup I] [Finite I]
    (hI : ∀ w : I, w ^ 2 = 1) {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (θ : I ≃* Multiplicative W) {X L : Subgroup (MulAut I)} (hLX : L ≤ X)
    (hLn : (L.subgroupOf X).Normal) (hirr : IsIrrOn L ⊤ ⊥) (φ : ↥L ≃* SL(2, F))
    (hm : E3.mParam X = n + 2) : Module.finrank (ZMod 2) W = 2 * n + 4 := by
  classical
  haveI : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  obtain ⟨u, hu⟩ := exists_orderOf_eq_two_of_sl2 hLX φ
  have hevX : Even (Nat.card ↥X) :=
    even_iff_two_dvd.2 (hu ▸ orderOf_dvd_natCard u)
  obtain ⟨t₀, ht₀X, ht₀, ht₀m⟩ := E3.exists_involution_rkIdx_fixV_eq_mParam X hevX
  let t : ↥X := ⟨t₀, ht₀X⟩
  have ht : orderOf t = 2 := by rw [Subgroup.orderOf_mk]; exact ht₀
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have htm : Module.finrank (ZMod 2) (W ⧸ fixSub (subRep θ X) (Subgroup.zpowers t)) =
      E3.mParam X := by
    rw [finrank_quotient_fixSub_subRep, MonoidHom.map_zpowers]
    exact ht₀m
  have hle : Module.finrank (ZMod 2) W ≤ 2 * (n + 2) := by
    rcases trichotomy_of_involution hn hF hI θ hLX hLn hirr φ t ht with
      h1 | ⟨s, hns, hms, -, -⟩ | ⟨s, hns, h3s⟩
    · rw [htm, hm] at h1
      exact h1
    · rw [htm, hm] at hms
      omega
    · rw [htm, hm] at h3s
      omega
  have hker : ((subRep θ X t) - LinearMap.id).ker =
      fixSub (subRep θ X) (Subgroup.zpowers t) := by
    ext v
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    constructor
    · intro hv b hb
      rcases UC22.K147L2Fac.eq_one_or_eq_of_mem_zpowers ht2 hb with rfl | rfl
      · simp
      · exact hv
    · intro hv
      exact hv t (Subgroup.mem_zpowers t)
  have hinv : ∀ v, (subRep θ X t) ((subRep θ X t) v) = v := by
    intro v
    have h2 : (subRep θ X t) * (subRep θ X t) = 1 := by rw [← map_mul, ht2, map_one]
    exact congrArg (fun f : Module.End (ZMod 2) W => f v) h2
  have hbound :=
    CFSG.Timmesfeld.TransvectionActions.finrank_le_two_mul_finrank_ker_involution
      (subRep θ X t) hinv
  rw [hker] at hbound
  have hquot := Submodule.finrank_quotient_add_finrank
    (fixSub (subRep θ X) (Subgroup.zpowers t))
  rw [htm] at hquot
  omega

theorem k14_3Exc_holds :
    K14_3Exc := by
  intro I _ _ hI X L n hLX hLn hirr hL2orSz hn hn4 hm
  classical
  rcases hL2orSz with hL2 | hSz
  ·
    obtain ⟨F, _, _, hF, ⟨φ⟩⟩ := CFSG.Quasithin.Vol2.Ch11.OE2.exists_sl2_of_lieModel hL2
    haveI : CharP F 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hF
    haveI : Fintype F := Fintype.ofFinite F
    have hF' : Fintype.card F = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hF]
    obtain ⟨W, _, _, _, ⟨θ⟩⟩ :=
      CFSG.QuasithinUnique.Setup.Layer.Actor.exists_binModel_of_binary (V := I) fun v => by
        rw [← pow_two]; exact hI v
    haveI : Module.Finite (ZMod 2) W := Module.Finite.of_finite
    haveI : Fact (B45L2.repOf θ φ).IsIrreducible :=
      ⟨B45L2.repOf_isIrreducible θ φ (isIrrSec_of_isIrrOn_top hirr)⟩
    have hdim := finrank_eq_of_mParam_eq_add_two hn hn4 hF' hI θ hLX hLn hirr φ hm
    obtain ⟨rfl, hD⟩ := sixtyFourDescent_of_finrank hn hn4 hF' (B45L2.repOf θ φ)
      (B45L2.repOf_nontrivial θ φ) hdim
    refine ⟨rfl, hL2, ?_⟩
    refine RonanE42.aParam_le_of_aSet_empty X 2 (fun A hA => ?_)
    by_cases hAL : A ≤ L
    · exact not_mem_aSet_three_of_le hF' hI θ φ hD X A hAL hA
    · exact not_mem_aSet_two_of_not_le hF' hI θ hLX hLn φ hD A hAL
        (E3.aSet_anti (by norm_num : 2 ≤ 3) X hA)
  ·
    exfalso
    have h2n := two_mul_le_mParam_of_isSz hI hn hLX hLn hSz hirr
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3
