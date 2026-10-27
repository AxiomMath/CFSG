module

public import CFSG.Yardstones.Mf4cdcdf2e013.Definitions
public import CFSG.Adapters.LieModelSimple
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94S3E16b
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGenericCatalog
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSeitz3
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811K1Cover
public import CFSG.Quasithin.Vol2.Ch9Sec3L34Out
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONTwoRank
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TableComplete

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)

theorem three_le_pRank_of_linear_three_center
    {G : Type} [Group G] [Finite G] {X K : Subgroup G}
    (hXK : X ≤ K) (hXq : CFSG.Open.IsQuasisimple X)
    (hX : CFSG.Blueprint.LieModel X .PSL 3 2 2)
    (hZ : 3 ∣ Nat.card (Subgroup.center K)) : 3 ≤ CFSG.Open.pRank 3 K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E₀, hE₀, hE₀c⟩ := CFSG.Quasithin.H13.Ch9.L34.exists_elemAbelian_nine_of_isPSL
    (hX.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags]))
  have hE : IsElemAbelian 3 (E₀.map X.subtype) := hE₀.map X.subtype
  have hEc : Nat.card (E₀.map X.subtype) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective X.subtype_injective, hE₀c]
    norm_num
  have hEX : E₀.map X.subtype ≤ X := Subgroup.map_subtype_le E₀
  have hZX :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzBridgeAux.center_eq_bot_of_simple
      (hX.isSimpleGroup_of_mem_classicalTags (by simp [CFSG.Blueprint.classicalTags]))
      (CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3.exists_noncomm_of_quasisimple hXq)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 hZ
  let zG : G := (z : K)
  have hzorder : orderOf zG = 3 := by
    change orderOf (((z : Subgroup.center K) : K) : G) = 3
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  have hzX : zG ∉ X := by
    intro hzX
    have hxZ : (⟨zG, hzX⟩ : X) ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact congrArg (fun k : K => (k : G))
        (Subgroup.mem_center_iff.mp z.2 (Subgroup.inclusion hXK y))
    rw [hZX, Subgroup.mem_bot] at hxZ
    have hz1 : zG = 1 := congrArg Subtype.val hxZ
    rw [hz1, orderOf_one] at hzorder
    norm_num at hzorder
  have hzC : zG ∈ Subgroup.centralizer ((E₀.map X.subtype : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg (fun k : K => (k : G))
      (Subgroup.mem_center_iff.mp z.2 ⟨y, hXK (hEX hy)⟩)
  exact CFSG.AGLEmbedding.three_le_pRank_of_isElemAbelian_sq_of_mem_centralizer
    Nat.prime_three hE hEc hzorder (fun h => hzX (hEX h)) hzC
    (hEX.trans hXK) (z : K).2

section LinearThreeCenter

theorem rest15_false_of_linear_three_center
    {G : Type} [Group G] [Finite G]
    (hS : Standing4 G) (S : Setup4 G) {X H K P : Subgroup G}
    (hHtop : H ≠ ⊤) (hHr : CFSG.Open.pRank 3 H ≤ 3)
    (hXcomp : CFSG.Open.IsComponentOf X (H ⊓ S.M))
    (hKcomp : CFSG.Open.IsComponentOf K H)
    (hXK : X ≤ K) (_hKM : ¬ K ≤ S.M)
    (hX : CFSG.Blueprint.LieModel X .PSL 3 2 2)
    (_hP : CFSG.ABGLocalTools.IsSylowOf 3 P X)
    (_hGamma : rankThreeGamma 1 3 P ≤ S.M)
    (hZ : 3 ∣ Nat.card (Subgroup.center K)) : False := by
  have hKq : CFSG.Open.IsQuasisimple K := hKcomp.2.2
  have hXq : CFSG.Open.IsQuasisimple X := hXcomp.2.2
  have hKtop : K ≠ ⊤ := fun h => hHtop (top_le_iff.mp (h ▸ hKcomp.1))
  have hcat := CFSG.HardMathSupport.Timmesfeld.ComponentBalance.inCatalog_quotient_center_of_kgroup
    hKq (hS.kProper.isKGroup K hKtop)
  have hKr : CFSG.Open.pRank 3 K ≤ 3 :=
    (CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt hKcomp.1).trans hHr
  have hK3 : CFSG.Open.pRank 3 (⊤ : Subgroup K) = 3 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact Nat.le_antisymm hKr (three_le_pRank_of_linear_three_center hXK hXq hX hZ)
  obtain ⟨-, -, ⟨θ⟩⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.k34odd_threeCover_of_three_dvd
      CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
      CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput
      CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds
      K hKq hcat hZ hK3
  have hZX :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzBridgeAux.center_eq_bot_of_simple
      (hX.isSimpleGroup_of_mem_classicalTags (by simp [CFSG.Blueprint.classicalTags]))
      (CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3.exists_noncomm_of_quasisimple hXq)
  let f : X →* CFSG.Blueprint.NativeSporadic.ON :=
    θ.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center K)).comp (Subgroup.inclusion hXK))
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : (QuotientGroup.mk' (Subgroup.center K)) (Subgroup.inclusion hXK x) = 1 := by
      apply θ.injective
      rw [map_one]
      exact hx
    have hx' : Subgroup.inclusion hXK x ∈ Subgroup.center K := (QuotientGroup.eq_one_iff _).mp h1
    have hxZ : x ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact congrArg (fun k : K => (k : G))
        (Subgroup.mem_center_iff.mp hx' (Subgroup.inclusion hXK y))
    rw [hZX, Subgroup.mem_bot] at hxZ
    exact hxZ
  obtain ⟨F, hF2, hF16⟩ := CFSG.GH74.GLS.IVK.Proofs2.Ivk94.e16_psl3_four hX
  have hFe : CFSG.Assembly.IsElemAbelian 2 (F.map f) := by
    have hsq : ∀ y ∈ F.map f, y ^ 2 = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hF2 x hx, map_one]
    have hinv : ∀ y : ↥(F.map f), y⁻¹ = y := by
      intro y
      apply inv_eq_of_mul_eq_one_right
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_one, ← sq]
      exact hsq y y.2
    show IsMulCommutative ↥(F.map f) ∧ ∀ y ∈ F.map f, y ^ 2 = 1
    refine ⟨⟨⟨fun a b => ?_⟩⟩, hsq⟩
    calc a * b = (a * b)⁻¹ := (hinv _).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [hinv, hinv]
  have h8 := (open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONTwoRank in
    card_le_eight_of_isElemAbelian_ON (F.map f) hFe)
  rw [Subgroup.card_map_of_injective hf, hF16] at h8
  norm_num at h8

end LinearThreeCenter

end CFSG.LocalAnalysis.UniquenessCase.UC22
