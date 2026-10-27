module

public import CFSG.RankThree.PartTwo.Sec13.Item137
public import CFSG.RankThree.PartTwo.Sec13.Item13Inputs
public import CFSG.RankThree.PartTwo.Sec17.Item1729
public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic
public import CFSG.RankThree.PartTwo.Toolkit.Statements
import CFSG.RankThree.PartTwo.Sec13.Item137Delta
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item133Mono
import CFSG.RankThree.PartTwo.Sec13.Item136Moreover
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec13.Item132
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec13.Naturality
import CFSG.RankThree.Asc83Table.GL23
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.RankThree.PartTwo.Sec11.Data
import CFSG.RankThree.PartTwo.Sec6.Statements
import Certificates.Certificate43

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section NormLe

variable {G : Type} [Group G] [Finite G] {X L K : Subgroup G} {c : G}

theorem three_dvd_card_of_sec13Data (h131 : Item131) (hspor : SporadicModels131)
    (hD : Sec13Data G X c K) : 3 ∣ Nat.card K := by
  rcases cases131 h131 hspor slTwoCenter hD with ⟨-, h9, -⟩ | ⟨-, h9, -⟩ | ⟨-, hPGL, -⟩ |
      ⟨hcK, -⟩
  · exact (show 3 ∣ 9 by norm_num).trans (h9 ▸ Subgroup.card_dvd_of_le inf_le_right)
  · exact (show 3 ∣ 9 by norm_num).trans (h9 ▸ Subgroup.card_dvd_of_le inf_le_right)
  · obtain ⟨-, -, D, hDK, -, hD9⟩ := facts_of_isZ3PGLThreePi hD hPGL
    exact (show 3 ∣ 9 by norm_num).trans (hD9 ▸ Subgroup.card_dvd_of_le hDK)
  · rw [← hD.orderOf_eq]
    exact Subgroup.orderOf_dvd_natCard K hcK

theorem false_of_autIn_gl (h131 : Item131) (hspor : SporadicModels131)
    (hD : Sec13Data G X c L) (hcL : c ∉ L) (e : Sec4.autIn L X ≃* GL (Fin 2) (ZMod 3)) :
    False := by
  have h48 : Nat.card (Sec4.autIn L X) = 48 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.RankThree.Asc83Table.card_GL23
  rcases cases131 h131 hspor slTwoCenter hD with ⟨-, -, -, hcase⟩ | ⟨-, -, -, ⟨f⟩⟩ |
      ⟨-, -, ⟨f⟩, -⟩ | ⟨hcL', -⟩
  · rcases hcase with ⟨-, hf | hf⟩ | ⟨-, ⟨f⟩⟩ | ⟨-, ⟨f⟩⟩
    · obtain ⟨f⟩ := hf
      rw [Nat.card_congr f.toEquiv, card_quaternion_two] at h48
      norm_num at h48
    · obtain ⟨f⟩ := hf
      rw [Nat.card_congr f.toEquiv, card_SL_two_three] at h48
      norm_num at h48
    · rw [Nat.card_congr f.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
        ZMod.card] at h48
      norm_num at h48
    · rw [Nat.card_congr f.toEquiv, card_quaternion_two] at h48
      norm_num at h48
  · rw [Nat.card_congr f.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      at h48
    norm_num [Nat.factorial] at h48
  · rw [Nat.card_congr f.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      ZMod.card] at h48
    norm_num at h48
  · exact hcL hcL'


omit [Finite G] in
theorem isElemAbelian_inf_right {X : Subgroup G} (hX : CFSG.Assembly.IsElemAbelian 3 X)
    (L : Subgroup G) : CFSG.Assembly.IsElemAbelian 3 (X ⊓ L) :=
  ⟨⟨⟨fun a b => Subtype.ext (show (a : G) * b = b * a from
      congrArg (Subtype.val : X → G) (hX.1.is_comm.comm ⟨a, a.2.1⟩ ⟨b, b.2.1⟩))⟩⟩,
    fun x hx => hX.2 x hx.1⟩

end NormLe

section NormLeMain

theorem item137NormLe_of (h131 : Item131) (h132 : Item132) (h13S : Sec17.Item13Setup)
    (hspor : SporadicModels131) : Item137NormLe := by
  intro G _ _ A c L h hM P E F t hcfg X hX hST
  obtain ⟨hcL, -, -⟩ := facts_of_m12 h131 hspor h hM
  obtain ⟨hXle, hX3, hX27, ⟨eGL⟩⟩ := hcfg.facts hX
  have hXdec : X = Subgroup.zpowers c ⊔ (X ⊓ L) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hEdec, hFdec⟩ := hcfg
    rcases hX with rfl | rfl
    · exact hEdec
    · exact hFdec
  have hc3 : c ^ 3 = 1 := h.isElemAbelian.2 c h.mem_A
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hl)
  have hcX : c ∈ X := hXdec ▸ (le_sup_left : Subgroup.zpowers c ≤ _) (Subgroup.mem_zpowers c)
  have hXE : X ∈ partTwoE G ∧ X ∉ partTwoT G := by
    rcases hST with hS | hT
    · exact ⟨hS.1, hS.2.1⟩
    · exact ⟨hT.1, hT.2.1⟩
  have hFE := (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1
  have hXF : X ∈ partTwoF G := hFE ▸ hXE.1
  obtain ⟨e, K, he, hK⟩ := h13S G h.toPartTwoStanding h.partTwoS_eq X hXF hXE.2
  have hD : Sec13Data G X e K :=
    { h.toPartTwoStanding with
      partTwoS_eq := h.partTwoS_eq
      mem_partTwoF := hXF
      not_mem_partTwoT := hXE.2
      zpowers_mem_omegaA := he
      mem_lA := hK }
  have hYeq : (Subgroup.zpowers c ⊔ (X ⊓ L)) ⊓ L = X ⊓ L :=
    zpowers_sup_inf_eq hc3 hcL inf_le_right (fun y hy => (hLc y hy.2).symm)
  obtain ⟨e₁⟩ := nonempty_autIn_sup_equiv hLc hYeq
  rw [← hXdec] at e₁
  have hT : Sec4.autIn (L ⊓ Subgroup.normalizer (X : Set G)) (X ⊓ L) = Sec4.autIn L (X ⊓ L) := by
    have := autIn_inf_normalizer_eq hLc hYeq
    rw [← hXdec] at this
    exact this
  let f : QuaternionGroup 2 →* MulAut (X ⊓ L : Subgroup G) :=
    (Sec4.autIn L (X ⊓ L)).subtype.comp
      (e₁.toMonoidHom.comp (eGL.symm.toMonoidHom.comp CFSG.RankThree.Asc83Table.quatHom))
  have hf : Function.Injective f :=
    Subtype.val_injective.comp (e₁.injective.comp (eGL.symm.injective.comp
      CFSG.RankThree.Asc83Table.quatHom_injective))
  have h9 : Nat.card (X ⊓ L : Subgroup G) = 9 := by
    have hcomm : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ X ⊓ L, x * y = y * x := by
      intro x hx y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact (Commute.zpow_left (hLc y hy.2).symm k).eq
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
    rw [← hXdec, hX27, eq_bot_iff.mpr ((inf_le_inf_left _ inf_le_right).trans
        (zpowers_inf_eq_bot hc3 hcL).le), Subgroup.card_bot, mul_one,
      card_zpowers_of_pow_three hc3 h.ne_one] at hcard
    omega
  have hirr : Sec21.IsIrreducibleOn
      (Sec4.autIn (L ⊓ Subgroup.normalizer (X : Set G)) (X ⊓ L)) := by
    refine isIrreducibleOn_of_order_four (isElemAbelian_inf_right hX3 L) h9
      (τ := f (QuaternionGroup.a 1)) (by rw [hT]; exact (e₁ _).2) ?_ ?_
    · rw [← map_pow, show (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 4 = 1 by decide, map_one]
    · rw [← map_pow]
      intro h1
      have := hf (h1.trans (map_one f).symm)
      exact absurd this (by decide)
  rcases h132 G X e K hD hST c hcX h.ne_one L h.mem_thetaComponentsAt hXdec
      (fun hc => hcL hc.2) hirr with h1 | h2 | h3
  ·
    exfalso
    obtain ⟨-, -, -, -, hΩe, hΩc, -⟩ := h1
    have hcΩ : Subgroup.zpowers c ∈ omegaA X := by
      rw [hΩc]
      exact ⟨1, Subgroup.one_mem _, by ext; simp⟩
    have hcΩ' := hcΩ
    rw [hΩe] at hcΩ'
    obtain ⟨w, hw, hcw⟩ := hcΩ'
    have hKw : K.map (MulAut.conj w).toMonoidHom ∈ lA X (w * e * w⁻¹) :=
      (map_conj_mem_lA_iff hw).mpr hK
    have hzp : Subgroup.zpowers (w * e * w⁻¹) = Subgroup.zpowers c := by
      rw [hcw, MonoidHom.map_zpowers]
      rfl
    rw [lA_congr hzp] at hKw
    have hD' : Sec13Data G X c (K.map (MulAut.conj w).toMonoidHom) :=
      { h.toPartTwoStanding with
        partTwoS_eq := h.partTwoS_eq
        mem_partTwoF := hXF
        not_mem_partTwoT := hXE.2
        zpowers_mem_omegaA := hcΩ
        mem_lA := hKw }
    have h3K := three_dvd_card_of_sec13Data h131 hspor hD'
    have hspor' := hspor
    obtain ⟨-, ⟨-, hM12z⟩, -⟩ := hspor'
    obtain ⟨φ⟩ := hM
    have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
      center_eq_bot_of_mulEquiv φ hM12z
    have hXcL : X ≤ Subgroup.zpowers c ⊔ L := hXdec ▸ sup_le_sup_left inf_le_right _
    have hKL := eq_of_mem_thetaComponentsAt_of_maximal h.orderOf_eq h.mem_thetaComponentsAt hZ
      hXcL hX3 (fun F' hF' hXF' => (hXF.2.1 F' hF' hXF') ▸ le_rfl)
      hD'.mem_thetaComponentsAt h3K
    rw [hKL] at hD'
    exact false_of_autIn_gl h131 hspor hD' hcL eGL
  · exact h2
  ·
    exfalso
    obtain ⟨-, -, φ, hφ⟩ := h3
    let g : QuaternionGroup 2 →* wStar X :=
      (Subgroup.inclusion (autIn_mono (le_top : L ≤ ⊤))).comp
        (eGL.symm.toMonoidHom.comp CFSG.RankThree.Asc83Table.quatHom)
    have hg : Function.Injective g :=
      (Subgroup.inclusion_injective (autIn_mono (le_top : L ≤ ⊤))).comp (eGL.symm.injective.comp
        CFSG.RankThree.Asc83Table.quatHom_injective)
    have hsq := sq_eq_one_of_q8_rel hφ (x := g (QuaternionGroup.a 1))
      (y := g (QuaternionGroup.xa 0))
      (by rw [← map_pow, show (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 4 = 1 by decide,
        map_one])
      (by rw [← map_pow, ← map_pow,
        show (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 2 = QuaternionGroup.xa 0 ^ 2 by decide])
      (by rw [← map_inv, ← map_mul, ← map_mul, ← map_inv,
        show QuaternionGroup.xa 0 * QuaternionGroup.a 1 * (QuaternionGroup.xa 0)⁻¹ =
          ((QuaternionGroup.a 1)⁻¹ : QuaternionGroup 2) by decide])
    rw [← map_pow] at hsq
    have := hg (hsq.trans (map_one g).symm)
    exact absurd this (by decide)

end NormLeMain

theorem rank3II_13_7_of_inputs (h131 : Item131) (h132 : Item132) (h13S : Sec17.Item13Setup)
    (hspor : SporadicModels131) (h414 : Sec4.Item4_14_local)
    (hM12D : ∀ (X : Type) [Group X], Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M12) →
      Toolkit.M12ThreeLocalData X) (hMove : Item137Move) : Item137 :=
  rank3II_13_7_of_steps (item137Delta_of h131 hspor h414 hM12D)
    (item137NormLe_of h131 h132 h13S hspor) hMove

end CFSG.RankThree.PartTwo.Sec13
