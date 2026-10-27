module

public import CFSG.RankThree.PartTwo.Sec13.Item138N
public import CFSG.RankThree.PartTwo.Sec13.Ronan138SNF
import CFSG.RankThree.PartTwo.Sec13.Item138ProofSylow
import CFSG.RankThree.PartTwo.Sec13.Item138ProofPGL
import CFSG.RankThree.PartTwo.Sec13.Item138ProofOmega
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec13.Item138ProofExists
import CFSG.RankThree.PartTwo.Sec13.Item137Delta
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.Sec13.Item137ProofOrbit
import CFSG.RankThree.PartTwo.Sec13.Ronan138SRefl
import CFSG.RankThree.PartTwo.Sec15.HypR
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec6.Item612Basic
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
import CFSG.RankThree.PartTwo.Sec11.Data
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartTwo.Sec6.Statements
import Certificates.Certificate43

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13.Item138Proof
open scoped commutatorElement

section Small

variable {G : Type} [Group G]

theorem mem_zpowers_pow_of_not_dvd {x : G} (hx3 : x ^ 3 = 1) {i : ℕ} (hi : ¬ 3 ∣ i) :
    x ∈ Subgroup.zpowers (x ^ i) := by
  have hmod : i * i % 3 = 1 := by
    have : i % 3 = 1 ∨ i % 3 = 2 := by omega
    rcases this with h | h <;> simp [Nat.mul_mod, h]
  refine Subgroup.mem_zpowers_iff.mpr ⟨(i : ℤ), ?_⟩
  rw [zpow_natCast, ← pow_mul]
  conv_lhs => rw [← Nat.mod_add_div (i * i) 3, hmod]
  rw [pow_add, pow_mul, hx3, one_pow, mul_one, pow_one]

theorem exists_pow_eq_of_mem_zpowers [Finite G] {x w : G} (hw : w ∈ Subgroup.zpowers x) :
    ∃ n : ℕ, x ^ n = w :=
  mem_powers_iff_mem_zpowers.mpr hw

end Small

section Frame

variable {G : Type} [Group G] [Finite G] {A L E F : Subgroup G} {c : G}

theorem card_inf_le_three (hH : Hyp138 A c L E) (hPGL : Sec8.IsZ3PGLThreePi (lBarA c L E)) :
    Nat.card (E ⊓ L : Subgroup G) ≤ 3 := by
  have hout := Item138Proof.not_le_of_isZ3PGLThreePi hH hPGL
  obtain ⟨h, -, hcE, -, hE27, -, -, -, hC⟩ := hH
  have hL := h.mem_thetaComponentsAt
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hl)
  have hc3 : c ^ 3 = 1 := h.isElemAbelian.2 c h.mem_A
  obtain ⟨π, p, f, K, _, hK, hq, φ, -⟩ := hC
  have hq2 := two_lt_of_mulEquiv (Sec6.isQuasisimple_of_mem_thetaComponentsAt hL) hK hq φ
  have hZ := Sec13.center_eq_bot_of_mulEquiv φ (Sec13.center_projImage_slPi hK hq hq2)
  have hcL : c ∉ L := Sec13.not_mem_of_center_eq_bot h hZ
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

theorem factorization_card_three_of_hyp138 (hH : Hyp138 A c L E)
    (hPGL : Sec8.IsZ3PGLThreePi (lBarA c L E)) : (Nat.card L).factorization 3 = 2 := by
  obtain ⟨h, hL3, hcE, hE3, -, hEN, -, -, hC⟩ := hH
  obtain ⟨p, e₀, _, he₀, hiso⟩ := hL3
  have h9 := not_modNine_of_isTypeCOn h hcE hE3 hEN hC hPGL he₀ hiso
  have hbar := factorization_card_three_eq_two he₀ hiso h9
  have hθ : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 L) :=
    (solvable_prime_complement_core_characterization (H := L) Nat.prime_three).2.2.1
  have hθ0 : Nat.card (aschbacherSolvableCore 3 L) ≠ 0 := Nat.card_pos.ne'
  have hq0 : Nat.card (L ⧸ aschbacherSolvableCore 3 L) ≠ 0 := Nat.card_pos.ne'
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 L),
    Nat.factorization_mul hq0 hθ0, Finsupp.add_apply, hbar,
    Nat.factorization_eq_zero_of_not_dvd hθ, add_zero]

theorem exists_frame138 (hH : Hyp138 A c L E) (hF : IsF138N L E F)
    (hPGL : Sec8.IsZ3PGLThreePi (lBarA c L E)) :
    ∃ x y : G, x ∈ E ∧ y ∈ F ∧ HeisFrame (E ⊓ F) x y ∧ ⁅x, y⁆ ≠ 1 ∧ ⁅x, y⁆ ∈ L ∧ c ∈ F ∧
      Nat.card (E ⊔ F : Subgroup G) = 81 ∧ Nat.card (E ⊓ F : Subgroup G) = 9 ∧
      E ⊓ L = Subgroup.zpowers ⁅x, y⁆ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEL3 := card_inf_le_three hH hPGL
  have hL9 := factorization_card_three_of_hyp138 hH hPGL
  obtain ⟨d, -, hdE, hdL, hd1, -⟩ := exists_inverting_of_hyp138 hH
  obtain ⟨h, -, hcE, hE3, hE27, hEN, -, hST, hC⟩ := hH
  obtain ⟨⟨hFEL, hF3, hF27, -, hFN⟩, hFL9⟩ := hF
  have hL := h.mem_thetaComponentsAt
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hl)
  have hc3 : c ^ 3 = 1 := h.isElemAbelian.2 c h.mem_A
  obtain ⟨π, p, f, K, _, hK, hq, φ, -⟩ := hC
  have hq2 := two_lt_of_mulEquiv (Sec6.isQuasisimple_of_mem_thetaComponentsAt hL) hK hq φ
  have hZL := Sec13.center_eq_bot_of_mulEquiv φ (Sec13.center_projImage_slPi hK hq hq2)
  have hcL : c ∉ L := Sec13.not_mem_of_center_eq_bot h hZL
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE3.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hFc : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hF3.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hEE : E ∈ partTwoE G := by
    rcases hST with hS | hT
    · exact hS.1
    · exact hT.1
  have hEF : E ∈ partTwoF G :=
    (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1 ▸ hEE
  have hEmax : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → E ≤ B → B = E := hEF.2.1
  have hEL : Nat.card (E ⊓ L : Subgroup G) = 3 := by
    have hdvd : Nat.card (E ⊓ L : Subgroup G) ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hE27]
      exact Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hk1 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      apply hd1
      have := Subgroup.eq_bot_of_card_eq _ hk
      have hdmem : d ∈ E ⊓ L := ⟨hdE, hdL⟩
      rw [this, Subgroup.mem_bot] at hdmem
      exact hdmem
    have : k ≤ 1 := by
      by_contra hk2
      have : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hk' : k = 1 := by omega
    rw [hk, hk', pow_one]
  have hELsup : (Nat.card (E ⊔ L : Subgroup G)).factorization 3 = 4 := by
    have h1 := Sec6.card_sup_mul_card_inf hEN
    rw [hEL, hE27] at h1
    have h2 : Nat.card (E ⊔ L : Subgroup G) = 9 * Nat.card L := by omega
    rw [h2, Nat.factorization_mul (by norm_num) Nat.card_pos.ne', Finsupp.add_apply, hL9,
      show (9 : ℕ) = 3 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_three]
    simp
  have hEF3 : IsPGroup 3 (E ⊔ F : Subgroup G) := by
    have h1 := Sec6.card_sup_mul_card_inf hFN
    rw [hF27, hE27, sup_comm] at h1
    have hdvd : Nat.card (E ⊔ F : Subgroup G) ∣ 3 ^ 6 :=
      ⟨_, by rw [show (3 : ℕ) ^ 6 = 27 * 27 by norm_num, ← h1]⟩
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    exact IsPGroup.of_card hk
  have hup := card_le_of_isPGroup (sup_le le_sup_left hFEL : E ⊔ F ≤ E ⊔ L) hEF3
  rw [hELsup] at hup
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
  have hFE' : (F ⊓ L) ⊔ E ≤ E ⊔ F := sup_le (inf_le_left.trans le_sup_right) le_sup_left
  have h81 : Nat.card (E ⊔ F : Subgroup G) = 81 := by
    have := Subgroup.card_le_of_le hFE'
    norm_num at hup ⊢
    omega
  have h9 : Nat.card (E ⊓ F : Subgroup G) = 9 := by
    have h1 := Sec6.card_sup_mul_card_inf hFN
    rw [hF27, hE27, sup_comm, h81, inf_comm] at h1
    omega
  have hPNF : E ⊔ F ≤ Subgroup.normalizer (F : Set G) := le_normalizer_of_card le_sup_right hF27 h81
  obtain ⟨y, hyF, hyE⟩ : ∃ y ∈ F, y ∉ E := by
    by_contra hall
    push Not at hall
    have hFE : F ≤ E := fun y hy => hall y hy
    have : F = E := Subgroup.eq_of_le_of_card_ge hFE (by rw [hE27, hF27])
    rw [this, inf_idem, hE27] at h9
    norm_num at h9
  have hy3 : y ^ 3 = 1 := hF3.2 y hyF
  obtain ⟨x, hxE, hxy⟩ : ∃ x ∈ E, x * y ≠ y * x := by
    by_contra hall
    push Not at hall
    have hsup := Sec15.isElemAbelian_sup_zpowers hE3 hy3 hall
    have heq := hEmax _ hsup le_sup_left
    exact hyE (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
  have hx3 : x ^ 3 = 1 := hE3.2 x hxE
  have hd₀1 : ⁅x, y⁆ ≠ 1 := by
    intro h1
    apply hxy
    rw [commutatorElement_def] at h1
    calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = y * x := by rw [h1, one_mul]
  have hd₀E : ⁅x, y⁆ ∈ E := by
    rw [commutatorElement_def]
    have : y * x⁻¹ * y⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp (hFN hyF) _).mp (inv_mem hxE)
    have e1 : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
    rw [e1]
    exact mul_mem hxE this
  have hd₀F : ⁅x, y⁆ ∈ F := by
    rw [commutatorElement_def]
    have : x * y * x⁻¹ ∈ F :=
      (Subgroup.mem_normalizer_iff.mp (hPNF (Subgroup.mem_sup_left hxE)) _).mp hyF
    exact mul_mem this (inv_mem hyF)
  have hd₀L : ⁅x, y⁆ ∈ L := by
    have hy' : y ∈ ((E ⊔ L : Subgroup G) : Set G) := hFEL hyF
    rw [Subgroup.coe_mul_of_left_le_normalizer_right E L hEN] at hy'
    obtain ⟨e', he', l, hl, rfl⟩ := hy'
    have hxe : x * e' = e' * x := hEc x hxE e' he'
    have h1 : x * l * x⁻¹ * l⁻¹ ∈ L :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp (hEN hxE) l).mp hl) (inv_mem hl)
    have h2 := (Subgroup.mem_normalizer_iff.mp (hEN he') _).mp h1
    rw [commutatorElement_def]
    have e2 : x * (e' * l) * x⁻¹ * (e' * l)⁻¹ = e' * (x * l * x⁻¹ * l⁻¹) * e'⁻¹ := by
      calc x * (e' * l) * x⁻¹ * (e' * l)⁻¹ = (x * e') * l * x⁻¹ * l⁻¹ * e'⁻¹ := by group
        _ = (e' * x) * l * x⁻¹ * l⁻¹ * e'⁻¹ := by rw [hxe]
        _ = e' * (x * l * x⁻¹ * l⁻¹) * e'⁻¹ := by group
    rw [e2]
    exact h2
  have hELc : E ⊔ L ≤ Subgroup.centralizer ({c} : Set G) :=
    sup_le (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (hEc a ha c hcE))
      h.le_centralizer
  have hFcc : ∀ a ∈ F, a * c = c * a := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mp (hELc (hFEL ha))
  have hcF : c ∈ F := by
    by_contra hcF
    obtain ⟨hab, hcard⟩ := Sec5.isElemAbelian_sup_zpowers hF3 hcF hc3 hFcc
    have hle : F ⊔ Subgroup.zpowers c ≤ E ⊔ F :=
      sup_le le_sup_right (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left hcE))
    have heq : F ⊔ Subgroup.zpowers c = E ⊔ F :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hF27, h81])
    apply hxy
    have hx' : x ∈ F ⊔ Subgroup.zpowers c := heq ▸ Subgroup.mem_sup_left hxE
    have hy' : y ∈ F ⊔ Subgroup.zpowers c := Subgroup.mem_sup_left hyF
    exact congrArg Subtype.val (hab.1.is_comm.comm ⟨x, hx'⟩ ⟨y, hy'⟩)
  have hframe : HeisFrame (E ⊓ F) x y := by
    refine ⟨hx3, hy3, fun z hz => hEc z hz.1 x hxE, fun z hz => hFc z hz.2 y hyF,
      fun z hz z' hz' => hEc z hz.1 z' hz'.1, Subgroup.mem_inf.mpr ⟨hd₀E, hd₀F⟩,
      fun i j hij => ?_⟩
    have hij' := Subgroup.mem_inf.mp hij
    have hxi : x ^ i ∈ E ⊓ F := by
      refine Subgroup.mem_inf.mpr ⟨pow_mem hxE i, ?_⟩
      have := F.mul_mem hij'.2 (F.inv_mem (F.pow_mem hyF j))
      rwa [mul_inv_cancel_right] at this
    have hyj : y ^ j ∈ E ⊓ F := by
      refine Subgroup.mem_inf.mpr ⟨?_, pow_mem hyF j⟩
      have := E.mul_mem (E.inv_mem (E.pow_mem hxE i)) hij'.1
      rwa [inv_mul_cancel_left] at this
    constructor
    · by_contra hi
      have hxZ : x ∈ E ⊓ F := Subgroup.zpowers_le.mpr hxi (mem_zpowers_pow_of_not_dvd hx3 hi)
      exact hxy (hFc x hxZ.2 y hyF)
    · by_contra hj
      have hyZ : y ∈ E ⊓ F := Subgroup.zpowers_le.mpr hyj (mem_zpowers_pow_of_not_dvd hy3 hj)
      exact hxy (hEc x hxE y hyZ.1)
  have hd₀3 : ⁅x, y⁆ ^ 3 = 1 := hE3.2 _ hd₀E
  have hELeq : E ⊓ L = Subgroup.zpowers ⁅x, y⁆ :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hd₀E, hd₀L⟩))
      (by rw [hEL, card_zpowers_of_pow_three hd₀3 hd₀1])).symm
  exact ⟨x, y, hxE, hyF, hframe, hd₀1, hd₀L, hcF, h81, h9, hELeq⟩

end Frame

section NF

variable {G : Type} [Group G] [Finite G] {E F : Subgroup G} {x y : G}

theorem HeisFrame.x_not_mem {Z : Subgroup G} (h : HeisFrame Z x y) : x ∉ Z := fun hx => by
  have := (h.ind 1 0 (by simpa using hx)).1
  omega

theorem HeisFrame.y_not_mem {Z : Subgroup G} (h : HeisFrame Z x y) : y ∉ Z := fun hy => by
  have := (h.ind 0 1 (by simpa using hy)).2
  omega

theorem HeisFrame.orderOf_comm {Z : Subgroup G} (h : HeisFrame Z x y) (hd1 : ⁅x, y⁆ ≠ 1) :
    orderOf ⁅x, y⁆ = 3 :=
  orderOf_eq_prime h.comm_pow_three hd1

theorem isNF_of_mem_left (hframe : HeisFrame (E ⊓ F) x y) (hxE : x ∈ E)
    (hE27 : Nat.card E = 27) (h9 : Nat.card (E ⊓ F : Subgroup G) = 9) {p : G} (hp : p ∈ E) :
    ∃ i : ℕ, IsNF (E ⊓ F) x y p i 0 := by
  have hxZ := hframe.x_not_mem
  have hx1 : x ≠ 1 := fun h1 => hxZ (h1 ▸ one_mem _)
  have hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ E ⊓ F, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact ((hframe.zx b hb).zpow_right k).eq.symm
  obtain ⟨hcard, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  rw [zpowers_inf_eq_bot hframe.x3 hxZ, Subgroup.card_bot, mul_one,
    card_zpowers_of_pow_three hframe.x3 hx1, h9] at hcard
  have heq : Subgroup.zpowers x ⊔ (E ⊓ F) = E :=
    Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr hxE) inf_le_left)
      (by rw [hE27, hcard])
  have hp' : p ∈ ((Subgroup.zpowers x ⊔ (E ⊓ F) : Subgroup G) : Set G) := by
    rw [heq]
    exact hp
  rw [hset] at hp'
  obtain ⟨a, ha, b, hb, rfl⟩ := hp'
  obtain ⟨n, rfl⟩ := exists_pow_eq_of_mem_zpowers ha
  exact ⟨n, b, hb, by rw [pow_zero, mul_one]⟩

theorem isNF_of_mem_right (hframe : HeisFrame (E ⊓ F) x y) (hyF : y ∈ F)
    (hF27 : Nat.card F = 27) (h9 : Nat.card (E ⊓ F : Subgroup G) = 9) {p : G} (hp : p ∈ F) :
    ∃ j : ℕ, IsNF (E ⊓ F) x y p 0 j := by
  have hyZ := hframe.y_not_mem
  have hy1 : y ≠ 1 := fun h1 => hyZ (h1 ▸ one_mem _)
  have hcomm : ∀ a ∈ Subgroup.zpowers y, ∀ b ∈ E ⊓ F, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact ((hframe.zy b hb).zpow_right k).eq.symm
  obtain ⟨hcard, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  rw [zpowers_inf_eq_bot hframe.y3 hyZ, Subgroup.card_bot, mul_one,
    card_zpowers_of_pow_three hframe.y3 hy1, h9] at hcard
  have heq : Subgroup.zpowers y ⊔ (E ⊓ F) = F :=
    Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr hyF) inf_le_right)
      (by rw [hF27, hcard])
  have hp' : p ∈ ((Subgroup.zpowers y ⊔ (E ⊓ F) : Subgroup G) : Set G) := by
    rw [heq]
    exact hp
  rw [hset] at hp'
  obtain ⟨a, ha, b, hb, rfl⟩ := hp'
  obtain ⟨n, rfl⟩ := exists_pow_eq_of_mem_zpowers ha
  exact ⟨n, b, hb, by rw [pow_zero, one_mul]⟩

theorem isNF_of_mem_sup (hframe : HeisFrame (E ⊓ F) x y) (hxE : x ∈ E) (hyF : y ∈ F)
    (hE27 : Nat.card E = 27) (hF27 : Nat.card F = 27) (h9 : Nat.card (E ⊓ F : Subgroup G) = 9)
    (hFN : F ≤ Subgroup.normalizer (E : Set G)) {p : G} (hp : p ∈ E ⊔ F) :
    ∃ i j : ℕ, IsNF (E ⊓ F) x y p i j := by
  have hp' : p ∈ ((F ⊔ E : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact hp
  rw [Subgroup.coe_mul_of_left_le_normalizer_right F E hFN] at hp'
  obtain ⟨f', hf', e', he', rfl⟩ := hp'
  obtain ⟨j, hj⟩ := isNF_of_mem_right hframe hyF hF27 h9 hf'
  obtain ⟨i, hi⟩ := isNF_of_mem_left hframe hxE hE27 h9 he'
  exact ⟨i, j, by simpa using IsNF.mul hframe hj hi⟩

theorem mem_left_iff (hframe : HeisFrame (E ⊓ F) x y) (hxE : x ∈ E)
    (hE27 : Nat.card E = 27) (h9 : Nat.card (E ⊓ F : Subgroup G) = 9) {p : G} {i j : ℕ}
    (hp : IsNF (E ⊓ F) x y p i j) : p ∈ E ↔ (j : ZMod 3) = 0 := by
  constructor
  · intro hpE
    obtain ⟨i', hi'⟩ := isNF_of_mem_left hframe hxE hE27 h9 hpE
    simpa using (IsNF.unique hframe hp hi').2
  · intro hj
    obtain ⟨z, hz, rfl⟩ := hp
    obtain ⟨m, rfl⟩ := (ZMod.natCast_eq_zero_iff j 3).mp hj
    rw [pow_mul, hframe.y3, one_pow, mul_one]
    exact mul_mem (pow_mem hxE i) (Subgroup.mem_inf.mp hz).1

theorem mem_right_iff (hframe : HeisFrame (E ⊓ F) x y) (hyF : y ∈ F)
    (hF27 : Nat.card F = 27) (h9 : Nat.card (E ⊓ F : Subgroup G) = 9) {p : G} {i j : ℕ}
    (hp : IsNF (E ⊓ F) x y p i j) : p ∈ F ↔ (i : ZMod 3) = 0 := by
  constructor
  · intro hpF
    obtain ⟨j', hj'⟩ := isNF_of_mem_right hframe hyF hF27 h9 hpF
    simpa using (IsNF.unique hframe hp hj').1
  · intro hi
    obtain ⟨z, hz, rfl⟩ := hp
    obtain ⟨m, rfl⟩ := (ZMod.natCast_eq_zero_iff i 3).mp hi
    rw [pow_mul, hframe.x3, one_pow, one_mul]
    exact mul_mem (pow_mem hyF j) (Subgroup.mem_inf.mp hz).2

theorem mem_inf_of_commute (hframe : HeisFrame (E ⊓ F) x y) (hd1 : ⁅x, y⁆ ≠ 1) {p : G}
    {i j : ℕ} (hp : IsNF (E ⊓ F) x y p i j) (hpx : p * x = x * p) (hpy : p * y = y * p) :
    p ∈ E ⊓ F := by
  have hord := hframe.orderOf_comm hd1
  have h1 := IsNF.commutator hframe hp IsNF.gen_y
  have h2 := IsNF.commutator hframe IsNF.gen_x hp
  have hpy' : ⁅p, y⁆ = 1 := by rw [commutatorElement_def, hpy]; group
  have hxp' : ⁅x, p⁆ = 1 := by rw [commutatorElement_def, ← hpx]; group
  rw [hpy'] at h1
  rw [hxp'] at h2
  have hi : 3 ∣ i := by
    have := orderOf_dvd_of_pow_eq_one h1.symm
    rw [hord] at this
    simpa using this
  have hj : 3 ∣ j := by
    have := orderOf_dvd_of_pow_eq_one h2.symm
    rw [hord] at this
    simpa using this
  exact (IsNF.mem_iff hframe hp).mpr ⟨(ZMod.natCast_eq_zero_iff i 3).mpr hi,
    (ZMod.natCast_eq_zero_iff j 3).mpr hj⟩

theorem conj_mem_inf_of_mem_normalizer (hframe : HeisFrame (E ⊓ F) x y) (hd1 : ⁅x, y⁆ ≠ 1)
    (hxE : x ∈ E) (hyF : y ∈ F) (hE27 : Nat.card E = 27) (hF27 : Nat.card F = 27)
    (h9 : Nat.card (E ⊓ F : Subgroup G) = 9) (hFN : F ≤ Subgroup.normalizer (E : Set G))
    (hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hFab : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a)
    {s : G} (hs : s ∈ Subgroup.normalizer ((E ⊔ F : Subgroup G) : Set G)) :
    ∀ z ∈ E ⊓ F, s * z * s⁻¹ ∈ E ⊓ F := by
  intro z hz
  have hzc : E ⊔ F ≤ Subgroup.centralizer ({z} : Set G) := sup_le
    (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr
      (hEab a ha z (Subgroup.mem_inf.mp hz).1))
    (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr
      (hFab a ha z (Subgroup.mem_inf.mp hz).2))
  have hzP : z ∈ E ⊔ F := Subgroup.mem_sup_left (Subgroup.mem_inf.mp hz).1
  have hszP : s * z * s⁻¹ ∈ E ⊔ F := (Subgroup.mem_normalizer_iff.mp hs z).mp hzP
  have hcomm : ∀ q ∈ E ⊔ F, s * z * s⁻¹ * q = q * (s * z * s⁻¹) := by
    intro q hq
    have hq' : s⁻¹ * q * s ∈ E ⊔ F := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hs) q).mp hq
      rwa [inv_inv] at this
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hzc hq')
    calc s * z * s⁻¹ * q = s * (z * (s⁻¹ * q * s)) * s⁻¹ := by group
      _ = s * ((s⁻¹ * q * s) * z) * s⁻¹ := by rw [h1]
      _ = q * (s * z * s⁻¹) := by group
  obtain ⟨i, j, hij⟩ := isNF_of_mem_sup hframe hxE hyF hE27 hF27 h9 hFN hszP
  exact mem_inf_of_commute hframe hd1 hij (hcomm x (Subgroup.mem_sup_left hxE))
    (hcomm y (Subgroup.mem_sup_right hyF))

theorem pow_three_of_mem_sup (hFN : F ≤ Subgroup.normalizer (E : Set G))
    (hEN : E ≤ Subgroup.normalizer (F : Set G)) (hE3 : CFSG.Assembly.IsElemAbelian 3 E)
    (hF3 : CFSG.Assembly.IsElemAbelian 3 F) {p : G} (hp : p ∈ E ⊔ F) : p ^ 3 = 1 := by
  have hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE3.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hFab : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hF3.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hp' : p ∈ ((F ⊔ E : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact hp
  rw [Subgroup.coe_mul_of_left_le_normalizer_right F E hFN] at hp'
  obtain ⟨f', hf', e', he', rfl⟩ := hp'
  have hkE : ⁅e', f'⁆ ∈ E := by
    rw [commutatorElement_def]
    have : f' * e'⁻¹ * f'⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp (hFN hf') _).mp (inv_mem he')
    rw [show e' * f' * e'⁻¹ * f'⁻¹ = e' * (f' * e'⁻¹ * f'⁻¹) by group]
    exact mul_mem he' this
  have hkF : ⁅e', f'⁆ ∈ F := by
    rw [commutatorElement_def]
    exact mul_mem ((Subgroup.mem_normalizer_iff.mp (hEN he') _).mp hf') (inv_mem hf')
  have ha : Commute ⁅e', f'⁆ e' := hEab _ hkE e' he'
  have hb : Commute ⁅e', f'⁆ f' := hFab _ hkF f' hf'
  rw [mul_pow_three_of_commute ha hb, hE3.2 _ hkE, hF3.2 _ hf', hE3.2 _ he']
  group

end NF

end CFSG.RankThree.PartTwo.Sec13.Ronan138S
