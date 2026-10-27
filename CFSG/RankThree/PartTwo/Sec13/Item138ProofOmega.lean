module

public import CFSG.RankThree.PartTwo.Sec13.Item138N
public import CFSG.RankThree.PartTwo.Sec17.Item1729
import CFSG.RankThree.PartTwo.Sec13.Item138ProofTools
import CFSG.RankThree.PartTwo.Sec13.Item138ProofExists
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item133Mono
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec13.Item135SimpleL3ProofModel
import CFSG.RankThree.PartTwo.Sec18.Tools
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseI
import CFSG.RankThree.PartTwo.Sec5.Tools
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
import CFSG.GroupTheory.ABGLocalTools.Constraint
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.RankThree.PartTwo.Late.GammaZero
import CFSG.RankThree.PartTwo.Sec11.Data
import CFSG.RankThree.PartTwo.Sec18.Notation
import CFSG.RankThree.PartTwo.Sec18.Transport
import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
import CFSG.RankThree.PartTwo.Sec4.StatementsGraphField
import CFSG.RankThree.PartTwo.Sec6.Statements
import Certificates.Certificate43

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Item138SN : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E : Subgroup G),
    Hyp138 A c L E → ∀ F : Subgroup G, IsF138N L E F →
      Sec8.IsZ3PGLThreePi (lBarA c L E) →
      CFSG.ABGLocalTools.IsSylowOf 3 (E ⊔ F) (Subgroup.normalizer (Subgroup.zpowers c : Set G)) →
        ∃ s ∈ Subgroup.normalizer (F : Set G),
          s ∉ Subgroup.normalizer (Subgroup.zpowers c : Set G)

end CFSG.RankThree.PartTwo.Sec13

namespace CFSG.RankThree.PartTwo.Sec13.Item138Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.RankThree.PartTwo.Sec4 (slPi PiField ModThree)

section Arith

theorem sl3Order_eq_of_not_modNine {q : ℕ} (hq : q % 3 = 1) (h9 : q % 9 ≠ 1) :
    ∃ m, ¬ 3 ∣ m ∧ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) = 27 * m := by
  obtain ⟨b, rfl⟩ : ∃ b, q = 3 * b + 1 := ⟨q / 3, by omega⟩
  have h2 : (3 * b + 1) ^ 2 - 1 = 3 * b * (3 * b + 2) := Nat.sub_eq_of_eq_add (by ring)
  have h3 : (3 * b + 1) ^ 3 - 1 = 9 * b * (3 * b ^ 2 + 3 * b + 1) :=
    Nat.sub_eq_of_eq_add (by ring)
  refine ⟨b ^ 2 * ((3 * b + 1) ^ 3 * (3 * b + 2) * (3 * b ^ 2 + 3 * b + 1)), ?_, ?_⟩
  · intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
    · have := Nat.prime_three.dvd_of_dvd_pow h
      omega
    · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
      · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
        · have := Nat.prime_three.dvd_of_dvd_pow h
          omega
        · omega
      · omega
  · rw [h2, h3]
    ring

theorem su3Order_eq_of_not_modNine {q : ℕ} (hq : q % 3 = 2) (h9 : q % 9 ≠ 8) :
    ∃ m, ¬ 3 ∣ m ∧ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) = 27 * m := by
  obtain ⟨b, rfl⟩ : ∃ b, q = 3 * b + 2 := ⟨q / 3, by omega⟩
  have h2 : (3 * b + 2) ^ 2 - 1 = 3 * (3 * b + 1) * (b + 1) := Nat.sub_eq_of_eq_add (by ring)
  refine ⟨(b + 1) ^ 2 * ((3 * b + 2) ^ 3 * (3 * b + 1) * (3 * b ^ 2 + 3 * b + 1)), ?_, ?_⟩
  · intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
    · have := Nat.prime_three.dvd_of_dvd_pow h
      omega
    · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
      · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
        · have := Nat.prime_three.dvd_of_dvd_pow h
          omega
        · omega
      · omega
  · rw [h2]
    ring

theorem factorization_card_three_eq_two {X : Type} [Group X] {p e : ℕ} [Fact p.Prime]
    (he : 1 ≤ e) (hiso : Sec4.IsoLThreePi X p e) (h9 : ¬ (p ^ e % 9 = 1 ∨ p ^ e % 9 = 8)) :
    (Nat.card X).factorization 3 = 2 := by
  obtain ⟨π, K, _, hK, hq, ⟨φ⟩⟩ := exists_projImage_model he hiso
  have hc := card_projImage_slPi_mul_three hK hq
  rw [← Nat.card_congr φ.toEquiv] at hc
  obtain ⟨m, hm3, hm⟩ : ∃ m, ¬ 3 ∣ m ∧ Nat.card X = 9 * m := by
    cases π
    · change p ^ e % 3 = 2 at hq
      obtain ⟨m, hm3, hm⟩ := su3Order_eq_of_not_modNine hq (by omega)
      refine ⟨m, hm3, ?_⟩
      change Nat.card X * 3 = (p ^ e) ^ 3 * ((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 + 1) at hc
      rw [hm] at hc
      omega
    · change p ^ e % 3 = 1 at hq
      obtain ⟨m, hm3, hm⟩ := sl3Order_eq_of_not_modNine hq (by omega)
      refine ⟨m, hm3, ?_⟩
      change Nat.card X * 3 = (p ^ e) ^ 3 * ((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 - 1) at hc
      rw [hm] at hc
      omega
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm3 (dvd_zero 3)
  rw [hm, Nat.factorization_mul (by norm_num) hm0, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hm3, add_zero,
    show (9 : ℕ) = 3 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_three]
  simp

end Arith

section Q8

theorem mem_normalizer_sup_zpowers {M : Type*} [Group M] [Finite M] {y₁ y₂ n : M}
    (h₁ : n * y₁ * n⁻¹ ∈ Subgroup.zpowers y₁ ⊔ Subgroup.zpowers y₂)
    (h₂ : n * y₂ * n⁻¹ ∈ Subgroup.zpowers y₁ ⊔ Subgroup.zpowers y₂) :
    n ∈ Subgroup.normalizer
      ((Subgroup.zpowers y₁ ⊔ Subgroup.zpowers y₂ : Subgroup M) : Set M) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_
    (by rw [Subgroup.card_map_of_injective (MulAut.conj n).injective])
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  exact sup_le (Subgroup.zpowers_le.mpr h₁) (Subgroup.zpowers_le.mpr h₂)

theorem not_mem_zpowers_of_card_sup {M : Type*} [Group M] {x₁ x₂ : M} (hx1 : x₁ ^ 3 = 1)
    (hx2 : x₂ ^ 3 = 1)
    (h9 : Nat.card (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup M) = 9) :
    x₂ ∉ Subgroup.zpowers x₁ ∧ x₁ ≠ 1 := by
  have hle : ∀ y : M, y ^ 3 = 1 → Nat.card (Subgroup.zpowers y) ≤ 3 := fun y hy =>
    (Nat.card_zpowers y).symm ▸ Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hy)
  constructor
  · intro hmem
    rw [sup_eq_left.mpr (Subgroup.zpowers_le.mpr hmem)] at h9
    have := hle x₁ hx1
    omega
  · rintro rfl
    rw [Subgroup.zpowers_one_eq_bot, bot_sup_eq] at h9
    have := hle x₂ hx2
    omega

variable {G : Type} [Group G] [Finite G]

theorem exists_q8_lift {L Y : Subgroup G} (hYL : Y ≤ L)
    (hYab : CFSG.Assembly.IsElemAbelian 3 Y) (hY9 : Nat.card Y = 9) {p e : ℕ} [Fact p.Prime]
    (he : 1 ≤ e) (hiso : Sec4.IsoLThreePi (L ⧸ aschbacherSolvableCore 3 L) p e)
    (h9 : ¬ (p ^ e % 9 = 1 ∨ p ^ e % 9 = 8)) :
    ∃ X₁ X₂ M₁ M₂ : G, X₁ ≠ 1 ∧ Y = Subgroup.zpowers X₁ ⊔ Subgroup.zpowers X₂ ∧
      M₁ ∈ L ∧ M₂ ∈ L ∧ M₁ ∈ Subgroup.normalizer (Y : Set G) ∧
      M₂ ∈ Subgroup.normalizer (Y : Set G) ∧
      M₁ * X₁ * M₁⁻¹ = X₂⁻¹ ∧ M₁ * X₂ * M₁⁻¹ = X₁ ∧
      M₂ * X₁ * M₂⁻¹ = X₂⁻¹ * X₁⁻¹ ∧ M₂ * X₂ * M₂⁻¹ = X₁ * X₂ * X₁ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x₁, x₂, n₁, n₂, h12, hx1, hx2, hP9, R1, R2, R3, R4, -⟩ :=
    L3Proof.exists_heis_data_of_isoLThreePi he hiso
  have hfac := factorization_card_three_eq_two he hiso h9
  set YL : Subgroup L := Y.subgroupOf L with hYLdef
  have hYLmap : YL.map L.subtype = Y := by
    rw [hYLdef, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hYL]
  have hYL9 : Nat.card YL = 9 := by
    rw [← hY9, ← hYLmap, Subgroup.card_map_of_injective L.subtype_injective]
  have hYL3 : IsPGroup 3 YL := IsPGroup.of_card (n := 2) (by rw [hYL9]; norm_num)
  have hinj := injOn_mk_of_isPGroup Nat.prime_three hYL3
  have hYbar9 : Nat.card (YL.map (QuotientGroup.mk' (aschbacherSolvableCore 3 L))) = 9 := by
    rw [card_map_eq_of_injOn _ hinj, hYL9]
  have hSyl₁ : CFSG.ABGLocalTools.IsSylowOf 3 (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) ⊤ :=
    CFSG.ABGLocalTools.isSylowOf_of_card le_top (by rw [hP9, Subgroup.card_top, hfac]; norm_num)
  have hSyl₂ : CFSG.ABGLocalTools.IsSylowOf 3
      (YL.map (QuotientGroup.mk' (aschbacherSolvableCore 3 L))) ⊤ :=
    CFSG.ABGLocalTools.isSylowOf_of_card le_top
      (by rw [hYbar9, Subgroup.card_top, hfac]; norm_num)
  obtain ⟨n, -, hn⟩ := Sec18.exists_map_conj_eq_of_isSylowOf hSyl₁ hSyl₂
  have hYbar : YL.map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) =
      Subgroup.zpowers (n * x₁ * n⁻¹) ⊔ Subgroup.zpowers (n * x₂ * n⁻¹) := by
    rw [hn, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rfl
  have S1 : (n * n₁ * n⁻¹) * (n * x₁ * n⁻¹) * (n * n₁ * n⁻¹)⁻¹ = (n * x₂ * n⁻¹)⁻¹ := by
    calc (n * n₁ * n⁻¹) * (n * x₁ * n⁻¹) * (n * n₁ * n⁻¹)⁻¹ =
        n * (n₁ * x₁ * n₁⁻¹) * n⁻¹ := by group
      _ = (n * x₂ * n⁻¹)⁻¹ := by rw [R1]; group
  have S2 : (n * n₁ * n⁻¹) * (n * x₂ * n⁻¹) * (n * n₁ * n⁻¹)⁻¹ = n * x₁ * n⁻¹ := by
    calc (n * n₁ * n⁻¹) * (n * x₂ * n⁻¹) * (n * n₁ * n⁻¹)⁻¹ =
        n * (n₁ * x₂ * n₁⁻¹) * n⁻¹ := by group
      _ = n * x₁ * n⁻¹ := by rw [R2]
  have S3 : (n * n₂ * n⁻¹) * (n * x₁ * n⁻¹) * (n * n₂ * n⁻¹)⁻¹ =
      (n * x₂ * n⁻¹)⁻¹ * (n * x₁ * n⁻¹)⁻¹ := by
    calc (n * n₂ * n⁻¹) * (n * x₁ * n⁻¹) * (n * n₂ * n⁻¹)⁻¹ =
        n * (n₂ * x₁ * n₂⁻¹) * n⁻¹ := by group
      _ = (n * x₂ * n⁻¹)⁻¹ * (n * x₁ * n⁻¹)⁻¹ := by rw [R3]; group
  have S4 : (n * n₂ * n⁻¹) * (n * x₂ * n⁻¹) * (n * n₂ * n⁻¹)⁻¹ =
      (n * x₁ * n⁻¹) * (n * x₂ * n⁻¹) * (n * x₁ * n⁻¹) := by
    calc (n * n₂ * n⁻¹) * (n * x₂ * n⁻¹) * (n * n₂ * n⁻¹)⁻¹ =
        n * (n₂ * x₂ * n₂⁻¹) * n⁻¹ := by group
      _ = (n * x₁ * n⁻¹) * (n * x₂ * n⁻¹) * (n * x₁ * n⁻¹) := by rw [R4]; group
  have hz₁ : n * x₁ * n⁻¹ ∈ YL.map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) := by
    rw [hYbar]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hz₂ : n * x₂ * n⁻¹ ∈ YL.map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) := by
    rw [hYbar]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  obtain ⟨Z₁, hZ₁, hZ₁e⟩ := hz₁
  obtain ⟨Z₂, hZ₂, hZ₂e⟩ := hz₂
  have hm₁ : n * n₁ * n⁻¹ ∈ Subgroup.normalizer
      ((YL.map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) :
        Subgroup (L ⧸ aschbacherSolvableCore 3 L)) : Set (L ⧸ aschbacherSolvableCore 3 L)) := by
    rw [hYbar]
    refine mem_normalizer_sup_zpowers ?_ ?_
    · rw [S1]
      exact inv_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    · rw [S2]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hm₂ : n * n₂ * n⁻¹ ∈ Subgroup.normalizer
      ((YL.map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) :
        Subgroup (L ⧸ aschbacherSolvableCore 3 L)) : Set (L ⧸ aschbacherSolvableCore 3 L)) := by
    rw [hYbar]
    refine mem_normalizer_sup_zpowers ?_ ?_
    · rw [S3]
      exact mul_mem (inv_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))
        (inv_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)))
    · rw [S4]
      exact mul_mem (mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
  rw [normalizer_map_mk_eq hYL3] at hm₁ hm₂
  obtain ⟨N₁, hN₁, hN₁e⟩ := hm₁
  obtain ⟨N₂, hN₂, hN₂e⟩ := hm₂
  have hconjY : ∀ {N : L}, N ∈ Subgroup.normalizer (YL : Set L) → ∀ {Z : L}, Z ∈ YL →
      N * Z * N⁻¹ ∈ YL := fun hN _ hZ => (Subgroup.mem_normalizer_iff.mp hN _).mp hZ
  have T1 : N₁ * Z₁ * N₁⁻¹ = Z₂⁻¹ := hinj (hconjY hN₁ hZ₁) (inv_mem hZ₂) (by
    simp only [map_mul, map_inv]
    rw [hN₁e, hZ₁e, hZ₂e]
    exact S1)
  have T2 : N₁ * Z₂ * N₁⁻¹ = Z₁ := hinj (hconjY hN₁ hZ₂) hZ₁ (by
    simp only [map_mul, map_inv]
    rw [hN₁e, hZ₁e, hZ₂e]
    exact S2)
  have T3 : N₂ * Z₁ * N₂⁻¹ = Z₂⁻¹ * Z₁⁻¹ :=
    hinj (hconjY hN₂ hZ₁) (mul_mem (inv_mem hZ₂) (inv_mem hZ₁)) (by
      simp only [map_mul, map_inv]
      rw [hN₂e, hZ₁e, hZ₂e]
      exact S3)
  have T4 : N₂ * Z₂ * N₂⁻¹ = Z₁ * Z₂ * Z₁ :=
    hinj (hconjY hN₂ hZ₂) (mul_mem (mul_mem hZ₁ hZ₂) hZ₁) (by
      simp only [map_mul, map_inv]
      rw [hN₂e, hZ₁e, hZ₂e]
      exact S4)
  have hZ₁Y : (Z₁ : G) ∈ Y := Subgroup.mem_subgroupOf.mp hZ₁
  have hZ₂Y : (Z₂ : G) ∈ Y := Subgroup.mem_subgroupOf.mp hZ₂
  have hz₁3 : (n * x₁ * n⁻¹) ^ 3 = 1 := by rw [conj_pow, hx1]; group
  have hz₂3 : (n * x₂ * n⁻¹) ^ 3 = 1 := by rw [conj_pow, hx2]; group
  obtain ⟨hz₂₁, hz₁1⟩ := not_mem_zpowers_of_card_sup hz₁3 hz₂3 (by rw [← hYbar, hYbar9])
  have hZ₁1 : (Z₁ : G) ≠ 1 := by
    intro h1
    apply hz₁1
    rw [← hZ₁e, show Z₁ = 1 from Subtype.ext h1, map_one]
  have hZ₂₁ : (Z₂ : G) ∉ Subgroup.zpowers (Z₁ : G) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    apply hz₂₁
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have hk' : Z₁ ^ k = Z₂ := Subtype.ext (by rw [Subgroup.coe_zpow, hk])
    rw [← hZ₁e, ← hZ₂e, ← map_zpow, hk']
  have hZ₁3 : (Z₁ : G) ^ 3 = 1 := hYab.2 _ hZ₁Y
  have hZ₂3 : (Z₂ : G) ^ 3 = 1 := hYab.2 _ hZ₂Y
  have hZ12 : (Z₂ : G) * Z₁ = Z₁ * Z₂ :=
    congrArg Subtype.val (hYab.1.is_comm.comm ⟨_, hZ₂Y⟩ ⟨_, hZ₁Y⟩)
  have hcard := Sec4.card_zpowers_sup_zpowers hZ₂3
    (orderOf_eq_prime hZ₁3 hZ₁1) hZ₂₁ hZ12
  have hYeq : Y = Subgroup.zpowers (Z₁ : G) ⊔ Subgroup.zpowers (Z₂ : G) :=
    (Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr hZ₁Y)
      (Subgroup.zpowers_le.mpr hZ₂Y)) (by rw [hcard, hY9])).symm
  have hNY : ∀ {N : L}, N ∈ Subgroup.normalizer (YL : Set L) →
      (N : G) ∈ Subgroup.normalizer (Y : Set G) := by
    intro N hN
    apply mem_normalizer_of_map_le
    rintro _ ⟨y, hy, rfl⟩
    exact Subgroup.mem_subgroupOf.mp
      (hconjY hN (Z := ⟨y, hYL hy⟩) (Subgroup.mem_subgroupOf.mpr hy))
  refine ⟨Z₁, Z₂, N₁, N₂, hZ₁1, hYeq, N₁.2, N₂.2, hNY hN₁, hNY hN₂, ?_, ?_, ?_, ?_⟩
  · exact congrArg Subtype.val T1
  · exact congrArg Subtype.val T2
  · exact congrArg Subtype.val T3
  · exact congrArg Subtype.val T4

end Q8

section Rel

variable {M : Type*} [Group M]

theorem q8_rel_facts {X₁ X₂ M₁ M₂ : M} (h12 : X₁ * X₂ = X₂ * X₁) (h1 : X₁ ^ 3 = 1)
    (h2 : X₂ ^ 3 = 1) (R1 : M₁ * X₁ * M₁⁻¹ = X₂⁻¹) (R2 : M₁ * X₂ * M₁⁻¹ = X₁)
    (R3 : M₂ * X₁ * M₂⁻¹ = X₂⁻¹ * X₁⁻¹) (R4 : M₂ * X₂ * M₂⁻¹ = X₁ * X₂ * X₁) :
    M₁ ^ 2 * X₁ * (M₁ ^ 2)⁻¹ = X₁⁻¹ ∧ M₁ ^ 2 * X₂ * (M₁ ^ 2)⁻¹ = X₂⁻¹ ∧
    M₂ ^ 2 * X₁ * (M₂ ^ 2)⁻¹ = X₁⁻¹ ∧ M₂ ^ 2 * X₂ * (M₂ ^ 2)⁻¹ = X₂⁻¹ ∧
    (M₂ * M₁) * X₁ * (M₂ * M₁)⁻¹ = (M₁⁻¹ * M₂) * X₁ * (M₁⁻¹ * M₂)⁻¹ ∧
    (M₂ * M₁) * X₂ * (M₂ * M₁)⁻¹ = (M₁⁻¹ * M₂) * X₂ * (M₁⁻¹ * M₂)⁻¹ := by
  have R1' : M₁⁻¹ * X₁ * M₁ = X₂ := by rw [← R2]; group
  have R2' : M₁⁻¹ * X₂ * M₁ = X₁⁻¹ := by
    calc M₁⁻¹ * X₂ * M₁ = (M₁⁻¹ * X₂⁻¹ * M₁)⁻¹ := by group
      _ = (M₁⁻¹ * (M₁ * X₁ * M₁⁻¹) * M₁)⁻¹ := by rw [R1]
      _ = X₁⁻¹ := by group
  have c1 : X₁⁻¹ * X₂ = X₂ * X₁⁻¹ := by
    calc X₁⁻¹ * X₂ = X₁⁻¹ * (X₂ * X₁) * X₁⁻¹ := by group
      _ = X₁⁻¹ * (X₁ * X₂) * X₁⁻¹ := by rw [h12]
      _ = X₂ * X₁⁻¹ := by group
  have c2 : X₁ * X₂⁻¹ = X₂⁻¹ * X₁ := by
    calc X₁ * X₂⁻¹ = X₂⁻¹ * (X₂ * X₁) * X₂⁻¹ := by group
      _ = X₂⁻¹ * (X₁ * X₂) * X₂⁻¹ := by rw [h12]
      _ = X₂⁻¹ * X₁ := by group
  have c3 : X₂⁻¹ * X₁⁻¹ = X₁⁻¹ * X₂⁻¹ := by
    rw [← mul_inv_rev, ← mul_inv_rev, h12]
  have i1 : X₁⁻¹ * X₁⁻¹ = X₁ := by
    calc X₁⁻¹ * X₁⁻¹ = X₁⁻¹ * X₁⁻¹ * X₁ ^ 3 := by rw [h1, mul_one]
      _ = X₁ := by group
  have i2 : X₂ * X₂ = X₂⁻¹ := by
    calc X₂ * X₂ = X₂ * X₂ * (X₂ ^ 3)⁻¹ := by rw [h2, inv_one, mul_one]
      _ = X₂⁻¹ := by group
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc M₁ ^ 2 * X₁ * (M₁ ^ 2)⁻¹ = M₁ * (M₁ * X₁ * M₁⁻¹) * M₁⁻¹ := by rw [sq]; group
      _ = M₁ * X₂⁻¹ * M₁⁻¹ := by rw [R1]
      _ = (M₁ * X₂ * M₁⁻¹)⁻¹ := by group
      _ = X₁⁻¹ := by rw [R2]
  · calc M₁ ^ 2 * X₂ * (M₁ ^ 2)⁻¹ = M₁ * (M₁ * X₂ * M₁⁻¹) * M₁⁻¹ := by rw [sq]; group
      _ = M₁ * X₁ * M₁⁻¹ := by rw [R2]
      _ = X₂⁻¹ := R1
  · calc M₂ ^ 2 * X₁ * (M₂ ^ 2)⁻¹ = M₂ * (M₂ * X₁ * M₂⁻¹) * M₂⁻¹ := by rw [sq]; group
      _ = M₂ * (X₂⁻¹ * X₁⁻¹) * M₂⁻¹ := by rw [R3]
      _ = (M₂ * X₂ * M₂⁻¹)⁻¹ * (M₂ * X₁ * M₂⁻¹)⁻¹ := by group
      _ = (X₁ * X₂ * X₁)⁻¹ * (X₂⁻¹ * X₁⁻¹)⁻¹ := by rw [R4, R3]
      _ = X₁⁻¹ := by group
  · calc M₂ ^ 2 * X₂ * (M₂ ^ 2)⁻¹ = M₂ * (M₂ * X₂ * M₂⁻¹) * M₂⁻¹ := by rw [sq]; group
      _ = M₂ * (X₁ * X₂ * X₁) * M₂⁻¹ := by rw [R4]
      _ = (M₂ * X₁ * M₂⁻¹) * (M₂ * X₂ * M₂⁻¹) * (M₂ * X₁ * M₂⁻¹) := by group
      _ = (X₂⁻¹ * X₁⁻¹) * (X₁ * X₂ * X₁) * (X₂⁻¹ * X₁⁻¹) := by rw [R3, R4]
      _ = X₁ * X₂⁻¹ * X₁⁻¹ := by group
      _ = X₂⁻¹ * X₁ * X₁⁻¹ := by rw [c2]
      _ = X₂⁻¹ := by group
  · calc (M₂ * M₁) * X₁ * (M₂ * M₁)⁻¹ = M₂ * (M₁ * X₁ * M₁⁻¹) * M₂⁻¹ := by group
      _ = M₂ * X₂⁻¹ * M₂⁻¹ := by rw [R1]
      _ = (M₂ * X₂ * M₂⁻¹)⁻¹ := by group
      _ = (X₁ * X₂ * X₁)⁻¹ := by rw [R4]
      _ = X₁⁻¹ * (X₂⁻¹ * X₁⁻¹) := by group
      _ = X₁⁻¹ * (X₁⁻¹ * X₂⁻¹) := by rw [c3]
      _ = (X₁⁻¹ * X₁⁻¹) * X₂⁻¹ := by group
      _ = X₁ * X₂⁻¹ := by rw [i1]
      _ = (X₁⁻¹)⁻¹ * X₂⁻¹ := by rw [inv_inv]
      _ = (M₁⁻¹ * X₂ * M₁)⁻¹ * (M₁⁻¹ * X₁ * M₁)⁻¹ := by rw [R2', R1']
      _ = M₁⁻¹ * (X₂⁻¹ * X₁⁻¹) * M₁ := by group
      _ = M₁⁻¹ * (M₂ * X₁ * M₂⁻¹) * M₁ := by rw [R3]
      _ = (M₁⁻¹ * M₂) * X₁ * (M₁⁻¹ * M₂)⁻¹ := by group
  · calc (M₂ * M₁) * X₂ * (M₂ * M₁)⁻¹ = M₂ * (M₁ * X₂ * M₁⁻¹) * M₂⁻¹ := by group
      _ = M₂ * X₁ * M₂⁻¹ := by rw [R2]
      _ = X₂⁻¹ * X₁⁻¹ := R3
      _ = (X₂ * X₂) * X₁⁻¹ := by rw [i2]
      _ = X₂ * (X₂ * X₁⁻¹) := by group
      _ = X₂ * (X₁⁻¹ * X₂) := by rw [c1]
      _ = (M₁⁻¹ * X₁ * M₁) * (M₁⁻¹ * X₂ * M₁) * (M₁⁻¹ * X₁ * M₁) := by rw [R1', R2']; group
      _ = M₁⁻¹ * (X₁ * X₂ * X₁) * M₁ := by group
      _ = M₁⁻¹ * (M₂ * X₂ * M₂⁻¹) * M₁ := by rw [R4]
      _ = (M₁⁻¹ * M₂) * X₂ * (M₁⁻¹ * M₂)⁻¹ := by group

theorem commute_of_conj_eq {W y : M} (h : W * y * W⁻¹ = y) : W * y = y * W := by
  calc W * y = W * y * W⁻¹ * W := by group
    _ = y * W := by rw [h]

theorem inv_conj_of_conj {W y z : M} (h : W * y * W⁻¹ = z) : W⁻¹ * z * W = y := by
  rw [← h]
  group

end Rel

section Aut

variable {G : Type} [Group G]

theorem normalizerMonoidHom_pow_coe {X : Subgroup G} (w : Subgroup.normalizer (X : Set G))
    (n : ℕ) (x : X) :
    ((((X.normalizerMonoidHom w) ^ n : MulAut X) x : X) : G) =
      (w : G) ^ n * x * ((w : G) ^ n)⁻¹ := by
  rw [← map_pow]
  change ((w ^ n : Subgroup.normalizer (X : Set G)) : G) * x *
    ((w ^ n : Subgroup.normalizer (X : Set G)) : G)⁻¹ = _
  rw [Subgroup.coe_pow]

theorem normalizerMonoidHom_eq_one_of {F : Subgroup G} {c X₁ X₂ : G}
    (hF : F = Subgroup.zpowers c ⊔ (Subgroup.zpowers X₁ ⊔ Subgroup.zpowers X₂))
    (w : Subgroup.normalizer (F : Set G)) (hc : (w : G) * c = c * w)
    (h1 : (w : G) * X₁ = X₁ * w) (h2 : (w : G) * X₂ = X₂ * w) :
    F.normalizerMonoidHom w = 1 := by
  have hle' : Subgroup.zpowers c ⊔ (Subgroup.zpowers X₁ ⊔ Subgroup.zpowers X₂) ≤
      Subgroup.centralizer ({(w : G)} : Set G) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_)
      (sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_))
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hc.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr h1.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr h2.symm
  ext f
  have hfF : (f : G) ∈ Subgroup.zpowers c ⊔ (Subgroup.zpowers X₁ ⊔ Subgroup.zpowers X₂) :=
    hF.le f.2
  have hf := Subgroup.mem_centralizer_singleton_iff.mp (hle' hfF)
  change (w : G) * f * (w : G)⁻¹ = f
  rw [← hf, mul_inv_cancel_right]

end Aut

end CFSG.RankThree.PartTwo.Sec13.Item138Proof

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13.Item138Proof

theorem item138OmegaN_of (h132 : Item132) (hset : Sec17.Item13Setup) (hS : Item138SN) :
    Item138OmegaN := by
  intro G _ _ A c L E hH F hF hPGL hSyl hSTF
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hs, hsN, hsH⟩ := hS G A c L E hH F hF hPGL hSyl
  obtain ⟨h, hL3, hcE, hE3, -, hEN, -, -, hC⟩ := hH
  obtain ⟨⟨hFEL, hF3, hF27, -, -⟩, hFL9⟩ := hF
  obtain ⟨p, e, _, he, hiso⟩ := hL3
  have h9 := not_modNine_of_isTypeCOn h hcE hE3 hEN hC hPGL he hiso
  have hFE : F ∈ partTwoE G ∧ F ∉ partTwoT G := by
    rcases hSTF with hS' | hT'
    · exact ⟨hS'.1, hS'.2.1⟩
    · exact ⟨hT'.1, hT'.2.1⟩
  have hFF : F ∈ partTwoF G :=
    (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1 ▸ hFE.1
  obtain ⟨π, p', f, K, _, hK, hq, φ, -⟩ := hC
  have hq2 := two_lt_of_mulEquiv
    (Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_thetaComponentsAt) hK hq φ
  have hZ := Sec13.center_eq_bot_of_mulEquiv φ (Sec13.center_projImage_slPi hK hq hq2)
  have hcL : c ∉ L := Sec13.not_mem_of_center_eq_bot h hZ
  have hc3 : c ^ 3 = 1 := h.isElemAbelian.2 c h.mem_A
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hl)
  have hEc : ∀ x ∈ E, x * c = c * x := fun x hx =>
    congrArg Subtype.val (hE3.1.is_comm.comm ⟨x, hx⟩ ⟨c, hcE⟩)
  have hELc : E ⊔ L ≤ Subgroup.centralizer ({c} : Set G) :=
    sup_le (fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hEc y hy))
      (fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hLc y hy))
  have hFc : ∀ x ∈ F, x * c = c * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (hELc (hFEL hx))
  have hcF : c ∈ F := by
    by_contra hcF
    obtain ⟨hab, -⟩ := Sec5.isElemAbelian_sup_zpowers hF3 hcF hc3 hFc
    have heq := hFF.2.1 _ hab le_sup_left
    exact hcF (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers c))
  have hcFL : c ∉ F ⊓ L := fun hc => hcL hc.2
  have hFLab : CFSG.Assembly.IsElemAbelian 3 (F ⊓ L) :=
    ⟨⟨⟨fun a b => Subtype.ext (show (a : G) * b = b * a from
      congrArg (Subtype.val : F → G) (hF3.1.is_comm.comm ⟨a, a.2.1⟩ ⟨b, b.2.1⟩))⟩⟩,
      fun x hx => hF3.2 x hx.1⟩
  obtain ⟨-, hc27⟩ := isElemAbelian_zpowers_sup_of_card_nine hc3 hcFL le_rfl hFL9
    (fun s hs => hFLab.2 s hs) (fun y hy => (hLc y hy.2).symm)
  have hFdec : F = Subgroup.zpowers c ⊔ (F ⊓ L) :=
    (Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr hcF) inf_le_left)
      (by rw [hc27, hF27])).symm
  obtain ⟨X₁, X₂, M₁, M₂, hX1, hYeq, hM₁L, hM₂L, hM₁Y, hM₂Y, R1, R2, R3, R4⟩ :=
    exists_q8_lift inf_le_right hFLab hFL9 he hiso h9
  have hX₁F : X₁ ∈ F ⊓ L := hYeq ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers X₁)
  have hX₂F : X₂ ∈ F ⊓ L := hYeq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers X₂)
  have h12 : X₁ * X₂ = X₂ * X₁ :=
    congrArg Subtype.val (hFLab.1.is_comm.comm ⟨X₁, hX₁F⟩ ⟨X₂, hX₂F⟩)
  have hX13 : X₁ ^ 3 = 1 := hFLab.2 X₁ hX₁F
  have hX23 : X₂ ^ 3 = 1 := hFLab.2 X₂ hX₂F
  obtain ⟨Q1, Q2, Q3, Q4, Q5, Q6⟩ := q8_rel_facts h12 hX13 hX23 R1 R2 R3 R4
  have hFgen : F = Subgroup.zpowers c ⊔ (Subgroup.zpowers X₁ ⊔ Subgroup.zpowers X₂) := by
    rw [← hYeq]
    exact hFdec
  have hMF : ∀ {Mx : G}, Mx ∈ L → Mx ∈ Subgroup.normalizer ((F ⊓ L : Subgroup G) : Set G) →
      Mx ∈ Subgroup.normalizer (F : Set G) := by
    intro Mx hMxL hMxY
    apply mem_normalizer_of_map_le
    intro y hy
    obtain ⟨y, hy, rfl⟩ := hy
    have hy' : y ∈ Subgroup.zpowers c ⊔ (F ⊓ L) := hFdec.le hy
    refine hFdec.ge ?_
    change Mx * y * Mx⁻¹ ∈ Subgroup.zpowers c ⊔ (F ⊓ L)
    have hle : Subgroup.zpowers c ⊔ (F ⊓ L) ≤
        (Subgroup.zpowers c ⊔ (F ⊓ L)).comap (MulAut.conj Mx).toMonoidHom := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) ?_
      · change Mx * c * Mx⁻¹ ∈ Subgroup.zpowers c ⊔ (F ⊓ L)
        rw [hLc Mx hMxL, mul_inv_cancel_right]
        exact Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
      · intro z hz
        exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hMxY z).mp hz)
    exact hle hy'
  have hM₁F := hMF hM₁L hM₁Y
  have hM₂F := hMF hM₂L hM₂Y
  obtain ⟨e', K', he', hK'⟩ := hset G h.toPartTwoStanding h.partTwoS_eq F hFF hFE.2
  have hD' : Sec13Data G F e' K' :=
    { h.toPartTwoStanding with
      partTwoS_eq := h.partTwoS_eq
      mem_partTwoF := hFF
      not_mem_partTwoT := hFE.2
      zpowers_mem_omegaA := he'
      mem_lA := hK' }
  set τ : MulAut (F ⊓ L : Subgroup G) := (F ⊓ L).normalizerMonoidHom ⟨M₁, hM₁Y⟩ with hτ
  have hτmem : τ ∈ Sec4.autIn (L ⊓ Subgroup.normalizer (F : Set G)) (F ⊓ L) :=
    Sec4.mem_autIn_iff.mpr ⟨M₁, hM₁Y, ⟨hM₁L, hM₁F⟩, rfl⟩
  have hX1inv : X₁⁻¹ ≠ X₁ := by
    intro h1
    apply hX1
    have hsq : X₁ * X₁ = 1 := by
      calc X₁ * X₁ = X₁ * X₁⁻¹ := by rw [h1]
        _ = 1 := mul_inv_cancel X₁
    calc X₁ = X₁ ^ 3 * (X₁ * X₁)⁻¹ := by group
      _ = 1 := by rw [hX13, hsq]; group
  have hτ2 : τ ^ 2 ≠ 1 := by
    intro h1
    have h2 := congrArg (fun σ : MulAut (F ⊓ L : Subgroup G) =>
      ((σ ⟨X₁, hX₁F⟩ : (F ⊓ L : Subgroup G)) : G)) h1
    simp only [hτ, normalizerMonoidHom_pow_coe, MulAut.one_apply] at h2
    exact hX1inv (Q1.symm.trans h2)
  have hτ4 : τ ^ 4 = 1 := by
    ext y
    rw [hτ, normalizerMonoidHom_pow_coe]
    change M₁ ^ 4 * y * (M₁ ^ 4)⁻¹ = y
    have hW1 : M₁ ^ 4 * X₁ * (M₁ ^ 4)⁻¹ = X₁ := by
      rw [show M₁ ^ 4 = M₁ ^ 2 * M₁ ^ 2 by group]
      calc M₁ ^ 2 * M₁ ^ 2 * X₁ * (M₁ ^ 2 * M₁ ^ 2)⁻¹ =
          M₁ ^ 2 * (M₁ ^ 2 * X₁ * (M₁ ^ 2)⁻¹) * (M₁ ^ 2)⁻¹ := by group
        _ = M₁ ^ 2 * X₁⁻¹ * (M₁ ^ 2)⁻¹ := by rw [Q1]
        _ = (M₁ ^ 2 * X₁ * (M₁ ^ 2)⁻¹)⁻¹ := by group
        _ = X₁ := by rw [Q1, inv_inv]
    have hW2 : M₁ ^ 4 * X₂ * (M₁ ^ 4)⁻¹ = X₂ := by
      rw [show M₁ ^ 4 = M₁ ^ 2 * M₁ ^ 2 by group]
      calc M₁ ^ 2 * M₁ ^ 2 * X₂ * (M₁ ^ 2 * M₁ ^ 2)⁻¹ =
          M₁ ^ 2 * (M₁ ^ 2 * X₂ * (M₁ ^ 2)⁻¹) * (M₁ ^ 2)⁻¹ := by group
        _ = M₁ ^ 2 * X₂⁻¹ * (M₁ ^ 2)⁻¹ := by rw [Q2]
        _ = (M₁ ^ 2 * X₂ * (M₁ ^ 2)⁻¹)⁻¹ := by group
        _ = X₂ := by rw [Q2, inv_inv]
    have hle : Subgroup.zpowers X₁ ⊔ Subgroup.zpowers X₂ ≤
        Subgroup.centralizer ({M₁ ^ 4} : Set G) := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (commute_of_conj_eq hW1).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (commute_of_conj_eq hW2).symm
    have hy := Subgroup.mem_centralizer_singleton_iff.mp (hle (hYeq.le y.2))
    rw [← hy, mul_inv_cancel_right]
  have hirr := Sec13.isIrreducibleOn_of_order_four hFLab hFL9 hτmem hτ4 hτ2
  rcases h132 G F e' K' hD' hSTF c hcF h.ne_one L h.mem_thetaComponentsAt hFdec hcFL hirr with
    h1 | h2 | h3
  · obtain ⟨-, -, -, -, -, hΩa, hcard, -⟩ := h1
    exact ⟨hΩa, hcard⟩
  · exact absurd (h2 hsN) hsH
  ·
    exfalso
    obtain ⟨-, -, ψ, hψ⟩ := h3
    have hmem : ∀ m : Subgroup.normalizer (F : Set G), F.normalizerMonoidHom m ∈ wStar F :=
      fun m => Sec4.mem_autIn_iff.mpr ⟨m, m.2, Subgroup.mem_top _, rfl⟩
    have hcW : ∀ m : Subgroup.normalizer (F : Set G), (m : G) ∈ L → (m : G) * c = c * m :=
      fun m hm => hLc m hm
    have hW : ∀ m : Subgroup.normalizer (F : Set G), (m : G) ∈ L →
        (m : G) * X₁ * (m : G)⁻¹ = X₁ → (m : G) * X₂ * (m : G)⁻¹ = X₂ →
        F.normalizerMonoidHom m = 1 := fun m hm h1 h2 =>
      normalizerMonoidHom_eq_one_of hFgen m (hcW m hm) (commute_of_conj_eq h1)
        (commute_of_conj_eq h2)
    have hM4 : ∀ {Z : G}, M₁ ^ 2 * Z * (M₁ ^ 2)⁻¹ = Z⁻¹ → M₁ ^ 4 * Z * (M₁ ^ 4)⁻¹ = Z := by
      intro Z hZ
      rw [show M₁ ^ 4 = M₁ ^ 2 * M₁ ^ 2 by group]
      calc M₁ ^ 2 * M₁ ^ 2 * Z * (M₁ ^ 2 * M₁ ^ 2)⁻¹ =
          M₁ ^ 2 * (M₁ ^ 2 * Z * (M₁ ^ 2)⁻¹) * (M₁ ^ 2)⁻¹ := by group
        _ = M₁ ^ 2 * Z⁻¹ * (M₁ ^ 2)⁻¹ := by rw [hZ]
        _ = (M₁ ^ 2 * Z * (M₁ ^ 2)⁻¹)⁻¹ := by group
        _ = Z := by rw [hZ, inv_inv]
    have hM22 : ∀ {Z : G}, M₁ ^ 2 * Z * (M₁ ^ 2)⁻¹ = Z⁻¹ → M₂ ^ 2 * Z * (M₂ ^ 2)⁻¹ = Z⁻¹ →
        M₁ ^ 2 * (M₂ ^ 2)⁻¹ * Z * (M₁ ^ 2 * (M₂ ^ 2)⁻¹)⁻¹ = Z := by
      intro Z h1 h2
      have h' := inv_conj_of_conj h2
      calc M₁ ^ 2 * (M₂ ^ 2)⁻¹ * Z * (M₁ ^ 2 * (M₂ ^ 2)⁻¹)⁻¹ =
          M₁ ^ 2 * ((M₂ ^ 2)⁻¹ * Z⁻¹ * M₂ ^ 2)⁻¹ * (M₁ ^ 2)⁻¹ := by group
        _ = M₁ ^ 2 * Z⁻¹ * (M₁ ^ 2)⁻¹ := by rw [h']
        _ = (M₁ ^ 2 * Z * (M₁ ^ 2)⁻¹)⁻¹ := by group
        _ = Z := by rw [h1, inv_inv]
    have hM5 : ∀ {Z : G}, (M₂ * M₁) * Z * (M₂ * M₁)⁻¹ = (M₁⁻¹ * M₂) * Z * (M₁⁻¹ * M₂)⁻¹ →
        (M₂ * M₁)⁻¹ * (M₁⁻¹ * M₂) * Z * ((M₂ * M₁)⁻¹ * (M₁⁻¹ * M₂))⁻¹ = Z := by
      intro Z hZ
      calc (M₂ * M₁)⁻¹ * (M₁⁻¹ * M₂) * Z * ((M₂ * M₁)⁻¹ * (M₁⁻¹ * M₂))⁻¹ =
          (M₂ * M₁)⁻¹ * ((M₁⁻¹ * M₂) * Z * (M₁⁻¹ * M₂)⁻¹) * (M₂ * M₁) := by group
        _ = (M₂ * M₁)⁻¹ * ((M₂ * M₁) * Z * (M₂ * M₁)⁻¹) * (M₂ * M₁) := by rw [hZ]
        _ = Z := by group
    let m₁ : Subgroup.normalizer (F : Set G) := ⟨M₁, hM₁F⟩
    let m₂ : Subgroup.normalizer (F : Set G) := ⟨M₂, hM₂F⟩
    have hx4 : (⟨_, hmem m₁⟩ : wStar F) ^ 4 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← map_pow]
      exact hW _ (pow_mem hM₁L 4) (hM4 Q1) (hM4 Q2)
    have hxy : (⟨_, hmem m₁⟩ : wStar F) ^ 2 = (⟨_, hmem m₂⟩ : wStar F) ^ 2 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_pow, ← map_pow, ← map_pow, ← mul_inv_eq_one,
        ← map_inv, ← map_mul]
      exact hW _ (mul_mem (pow_mem hM₁L 2) (inv_mem (pow_mem hM₂L 2))) (hM22 Q1 Q3)
        (hM22 Q2 Q4)
    have hyx : (⟨_, hmem m₂⟩ : wStar F) * ⟨_, hmem m₁⟩ * (⟨_, hmem m₂⟩ : wStar F)⁻¹ =
        (⟨_, hmem m₁⟩ : wStar F)⁻¹ := by
      rw [mul_inv_eq_iff_eq_mul]
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← map_mul, ← map_inv,
        ← map_mul, ← inv_mul_eq_one, ← map_inv, ← map_mul]
      exact hW _ (mul_mem (inv_mem (mul_mem hM₂L hM₁L)) (mul_mem (inv_mem hM₁L) hM₂L))
        (hM5 Q5) (hM5 Q6)
    have hsq := Sec13.sq_eq_one_of_q8_rel hψ hx4 hxy hyx
    have h2 := congrArg (fun z : wStar F => (((z : MulAut F) ⟨X₁, hX₁F.1⟩ : F) : G)) hsq
    simp only [Subgroup.coe_pow, normalizerMonoidHom_pow_coe, Subgroup.coe_one,
      MulAut.one_apply] at h2
    exact hX1inv (Q1.symm.trans h2)

end CFSG.RankThree.PartTwo.Sec13
