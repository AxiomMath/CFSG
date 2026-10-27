module

public import CFSG.Yardstones.Mf4cdcdf2e013.Definitions
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
import CFSG.LocalAnalysis.SectionRank.QTK.J4InspB2
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Nat
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotSetup
import CFSG.LocalAnalysis.StandardType.GGSpNbrKGInj
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Open
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open scoped MatrixGroups


private theorem not_injective_psl_three_four_to_small_statedSp
    {X : Type} [Group X] {n : ℕ} (hn : n ≤ 4)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2)
    (hX : CFSG.Blueprint.LieModel X .PSL 3 2 2)
    (φ : X →* StatedSp n F) (hφ : Function.Injective φ) : False := by
  let V := Multiplicative (Fin n ⊕ Fin n → F)
  let ψ : X →* MulAut V :=
    (PartTwo.s16gNatHom (Fin n ⊕ Fin n) F).comp ((StatedSp n F).subtype.comp φ)
  have hψ : Function.Injective ψ :=
    PartTwo.s16gNatHom_injective.comp ((StatedSp n F).subtype_injective.comp hφ)
  have hPSL : CFSG.Quasithin.IsPSL 3 2 2 ψ.range :=
    CFSG.SectionRank.QTK.isPSL_of_mulEquiv (MonoidHom.ofInjective hψ)
      (hX.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags]))
  have hpow : ∀ v : V, v ^ 2 = 1 := by
    intro v
    rw [pow_two]
    change Multiplicative.ofAdd (v.toAdd + v.toAdd) = Multiplicative.ofAdd 0
    apply congrArg Multiplicative.ofAdd
    ext i
    exact CharTwo.add_self_eq_zero _
  have hcard : Nat.card V = 2 ^ (2 * n) := by
    change Nat.card (Multiplicative (Fin n ⊕ Fin n → F)) = _
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_sum,
      Nat.card_fin, hF]
    congr 1
    omega
  have hdim := CFSG.SectionRank.QTK.faithfulL34ModDim_holds V hpow ψ.range hPSL
  rw [hcard] at hdim
  have hsmall : 2 ^ (2 * n) ≤ 2 ^ 8 :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h := hdim.trans hsmall
  norm_num at h

theorem rest15_false_of_linear_symplectic_two
    {G : Type} [Group G] [Finite G]
    (_hS : Standing4 G) (_hU : uniqueFourUnique G) (S : Setup4 G)
    (_hMS : S.InMSigma) (_hPart : PartIAt S.M)
    {L X H K P : Subgroup G} (_hL : L ∈ calC S.M)
    (_hLN : S.M ≤ normalizer (L : Set G)) (_hthin : ¬ F08.Thin8 L)
    (_hXL : X ≤ L) (_hsupp : X ⊔ pCoreOf 2 L = L)
    (_hHtop : H ≠ ⊤) (_hHr : CFSG.Open.pRank 3 H ≤ 3)
    (_hnotStrong : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 S.M)
    (_hXcomp : CFSG.Open.IsComponentOf X (H ⊓ S.M))
    (_hKcomp : CFSG.Open.IsComponentOf K H) (hXK : X ≤ K) (_hKM : ¬ K ≤ S.M)
    (hX : CFSG.Blueprint.LieModel X .PSL 3 2 2)
    (_hP : CFSG.ABGLocalTools.IsSylowOf 3 P X)
    (_hGamma : rankThreeGamma 1 3 P ≤ S.M)
    (_hNormal : (X.subgroupOf (H ⊓ S.M)).Normal)
    (_hGammaH : rankThreeGamma 1 3 (P.subgroupOf H) ≤
      (normalizer (X : Set G)).subgroupOf H)
    (_hZK : ¬ 3 ∣ Nat.card (center K))
    (_hAlt : ¬ ∃ m : ℕ, 5 ≤ m ∧
      Nonempty (K ⧸ center K ≃* alternatingGroup (Fin m)))
    {n : ℕ} (hn : n = 3 ∨ n = 4)
    (hmodel : CFSG.Blueprint.LieModel (K ⧸ center K) .PSp n 2 1) : False := by
  have hZX : Subgroup.center X = ⊥ := CFSG.Quasithin.H13.A5.center_eq_bot_of_isPSL34
    (hX.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags]))
  obtain ⟨φ, hφ, -⟩ := CFSG.StandardType.exists_inj_hom_centerQuot
    (MulEquiv.refl (K ⧸ center K)) X.subtype X.subtype_injective
    (Subgroup.range_subtype X) hXK hZX
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ :=
    CFSG.SeitzReduction.SymplecticPilot.exists_mulEquiv_statedSp_of_lieModel hmodel
  exact not_injective_psl_three_four_to_small_statedSp
    (by rcases hn with rfl | rfl <;> norm_num) (by simpa using hF) hX
    (e.toMonoidHom.comp φ) (e.injective.comp hφ)

end CFSG.LocalAnalysis.UniquenessCase.UC22
