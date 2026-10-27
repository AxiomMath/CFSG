module

public import CFSG.RankThree.PartTwo.Sec13.Item138ProofMain
import CFSG.RankThree.PartTwo.Sec13.Item138ProofExists
import CFSG.RankThree.PartTwo.Sec13.Item138ProofPGL
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
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
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
import CFSG.RankThree.Asc83Table.Automizer
import CFSG.RankThree.PartTwo.Sec11.Data
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartTwo.Sec6.Statements
import Certificates.Certificate43

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Item138SylHN : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E : Subgroup G),
    Hyp138 A c L E → Sec8.IsZ3PGLThreePi (lBarA c L E) →
      (Nat.card (Subgroup.normalizer (Subgroup.zpowers c : Set G))).factorization 3 = 4

namespace Item138Proof

variable {G : Type} [Group G] [Finite G]

theorem card_le_of_isPGroup {p : ℕ} [Fact p.Prime] {P H : Subgroup G} (hPH : P ≤ H)
    (hP : IsPGroup p P) : Nat.card P ≤ p ^ (Nat.card H).factorization p := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  rw [hk]
  apply Nat.pow_le_pow_right (Fact.out : p.Prime).pos
  have hdvd : p ^ k ∣ Nat.card H := hk ▸ Subgroup.card_dvd_of_le hPH
  exact (Nat.Prime.pow_dvd_iff_le_factorization (Fact.out) Nat.card_pos.ne').mp hdvd

end Item138Proof

open Item138Proof in
theorem item138SylowN_of (hH3 : Item138SylHN) : Item138SylowN := by
  intro G _ _ A c L E hH F hF hPGL
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h81 := hH3 G A c L E hH hPGL
  have hout := not_le_of_isZ3PGLThreePi hH hPGL
  obtain ⟨h, -, hcE, hE3, hE27, hEN, -, -, hC⟩ := hH
  obtain ⟨⟨hFEL, -, hF27, -, hFN⟩, hFL9⟩ := hF
  have hL := h.mem_thetaComponentsAt
  have hLN : L ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    le_normalizer_zpowers_of_mem hL
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hl)
  have hc3 : c ^ 3 = 1 := h.isElemAbelian.2 c h.mem_A
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE3.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hEH : E ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := fun x hx =>
    centralizer_le_normalizer_zpowers c
      (Subgroup.mem_centralizer_singleton_iff.mpr (hEc x hx c hcE))
  obtain ⟨π, p, f, K, _, hK, hq, φ, -⟩ := hC
  have hq2 := two_lt_of_mulEquiv (Sec6.isQuasisimple_of_mem_thetaComponentsAt hL) hK hq φ
  have hZ := Sec13.center_eq_bot_of_mulEquiv φ (Sec13.center_projImage_slPi hK hq hq2)
  have hcL : c ∉ L := Sec13.not_mem_of_center_eq_bot h hZ
  have hEL3 : Nat.card (E ⊓ L : Subgroup G) ≤ 3 := by
    have hcomm : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ E ⊓ L, x * y = y * x := by
      intro x hx y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact (Commute.zpow_left (hLc y hy.2).symm k).eq
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
    rw [eq_bot_iff.mpr ((inf_le_inf_left _ inf_le_right).trans
        (zpowers_inf_eq_bot hc3 hcL).le), Subgroup.card_bot, mul_one,
      card_zpowers_of_pow_three hc3 h.ne_one] at hcard
    have hle : Subgroup.zpowers c ⊔ (E ⊓ L) ≤ E :=
      sup_le (Subgroup.zpowers_le.mpr hcE) inf_le_left
    have hdvd : Nat.card (E ⊓ L : Subgroup G) ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hE27]
      exact Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    by_contra hgt
    have hk2 : 2 ≤ k := by
      by_contra hk2
      interval_cases k <;> rw [hk] at hgt <;> norm_num at hgt
    have hcard27 : 27 ≤ Nat.card (Subgroup.zpowers c ⊔ (E ⊓ L) : Subgroup G) := by
      rw [hcard, hk]
      have : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
      omega
    have heq : Subgroup.zpowers c ⊔ (E ⊓ L) = E :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hE27]; exact hcard27)
    exact hout (heq ▸ sup_le_sup_left inf_le_right _)
  have hFLN : F ⊓ L ≤ Subgroup.normalizer (E : Set G) := inf_le_left.trans hFN
  have hlow := Sec6.card_sup_mul_card_inf hFLN
  rw [hFL9, hE27] at hlow
  have hinf : Nat.card ((F ⊓ L) ⊓ E : Subgroup G) ≤ 3 := le_trans
    (Subgroup.card_le_of_le (show (F ⊓ L) ⊓ E ≤ E ⊓ L from
      le_inf inf_le_right (inf_le_left.trans inf_le_right))) hEL3
  have hpos : 0 < Nat.card ((F ⊓ L) ⊓ E : Subgroup G) := Nat.card_pos
  have hge : 81 ≤ Nat.card ((F ⊓ L) ⊔ E : Subgroup G) := by
    by_contra hlt
    push Not at hlt
    have := Nat.mul_le_mul (Nat.le_of_lt_succ (Nat.lt_succ_of_lt hlt)) hinf
    nlinarith
  have hFE : (F ⊓ L) ⊔ E ≤ E ⊔ F := sup_le (inf_le_left.trans le_sup_right) le_sup_left
  have hEF3 : IsPGroup 3 (E ⊔ F : Subgroup G) := by
    have h1 := Sec6.card_sup_mul_card_inf hFN
    rw [hF27, hE27, sup_comm] at h1
    have hdvd : Nat.card (E ⊔ F : Subgroup G) ∣ 3 ^ 6 :=
      ⟨_, by rw [show (3 : ℕ) ^ 6 = 27 * 27 by norm_num, ← h1]⟩
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    exact IsPGroup.of_card hk
  have hEFH : E ⊔ F ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    sup_le hEH (hFEL.trans (sup_le hEH hLN))
  have hup := card_le_of_isPGroup hEFH hEF3
  rw [h81] at hup
  have hEF81 : Nat.card (E ⊔ F : Subgroup G) = 3 ^ 4 := by
    have := Subgroup.card_le_of_le hFE
    norm_num at hup ⊢
    omega
  exact CFSG.ABGLocalTools.isSylowOf_of_card hEFH (by rw [hEF81, h81])

end CFSG.RankThree.PartTwo.Sec13
