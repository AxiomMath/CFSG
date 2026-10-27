module

public import CFSG.RankThree.PartTwo.Sec19.Step1914MoreProof
public import CFSG.RankThree.PartTwo.Sec13.Item138ProofOmega
public import CFSG.RankThree.PartTwo.Sec13.Item138ProofMain
public import Certificates.Certificate3029
public import Certificates.Certificate3086
public import Certificates.Certificate3139
import CFSG.RankThree.PartTwo.Sec19.Step1914MoreSProofCore
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.Sec19.O2Centralizer
import CFSG.RankThree.PartTwo.Sec13.Item138ProofPGL
import CFSG.RankThree.PartTwo.Sec13.Item138ProofSylow
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item137Delta
import CFSG.RankThree.PartTwo.Sec13.Item137ProofOrbit
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.CentralCover.FourGroupWitness
public import Certificates.Certificate2201
public import Certificates.Certificate8171
public import Certificates.Certificate8172
public import Certificates.Certificate9950
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
import CFSG.RankThree.PartTwo.KFacts.KS12MovesSL
import CFSG.RankThree.PartTwo.Sec11.Data
import CFSG.RankThree.PartTwo.Sec4.Census.Interface
import CFSG.RankThree.PartTwo.Sec4.Census.Interface46
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartTwo.Sec6.Statements
import CFSG.Sporadic.Schreier.J4SProfileNode
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
import Certificates.Certificate43

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def Step1914MoreL34Cartan : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E M : Subgroup G),
    Ctx1912 G A c L E M →
    Nonempty (L ⧸ CFSG.pCore 2 L ≃* projSL 3 (GaloisField 2 2)) →
    E = Subgroup.zpowers c ⊔ (E ⊓ L) → Subgroup.zpowers c ⊓ (E ⊓ L) = ⊥ →
      ∃ F : Subgroup G, F ≤ E ⊔ A ∧ c ∈ F ∧ CFSG.Assembly.IsElemAbelian 3 F ∧
        Nat.card F = 27 ∧ ¬ F ≤ Subgroup.zpowers c ⊔ L ∧
        Late.sectionCentralizer F L ((aschbacherSolvableCore 3 L).map L.subtype) =
          (Subgroup.zpowers c : Set G) ∧
        Sec4.IsTypeCOn F L

namespace Step1914MoreSProof

variable {G : Type} [Group G] [Finite G]

theorem exists_pow_mul_pow {X₁ X₂ y : G} (h12 : X₁ * X₂ = X₂ * X₁) (h1 : X₁ ^ 3 = 1)
    (h2 : X₂ ^ 3 = 1) (hy : y ∈ Subgroup.zpowers X₁ ⊔ Subgroup.zpowers X₂) :
    ∃ a b : ℕ, a < 3 ∧ b < 3 ∧ y = X₁ ^ a * X₂ ^ b := by
  have hc : ∀ x ∈ Subgroup.zpowers X₁, ∀ z ∈ Subgroup.zpowers X₂, x * z = z * x := by
    intro x hx z hz
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (Commute.zpow_zpow (show Commute X₁ X₂ from h12) i j).eq
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hc).2
  have hy' : y ∈ ((Subgroup.zpowers X₁ ⊔ Subgroup.zpowers X₂ : Subgroup G) : Set G) := hy
  rw [hset] at hy'
  obtain ⟨u, hu, v, hv, rfl⟩ := hy'
  have hred : ∀ {x : G}, x ^ 3 = 1 → ∀ i : ℤ, ∃ a : ℕ, a < 3 ∧ x ^ i = x ^ a := by
    intro x hx i
    refine ⟨(i % 3).toNat, by omega, ?_⟩
    rw [Sec13.zpow_eq_zpow_emod_of_pow_three hx i, ← zpow_natCast,
      Int.toNat_of_nonneg (Int.emod_nonneg i (by norm_num))]
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  obtain ⟨a, ha, hai⟩ := hred h1 i
  obtain ⟨b, hb, hbj⟩ := hred h2 j
  exact ⟨a, b, ha, hb, by simp only [hai, hbj]⟩

theorem exists_conj_eq_of_q8 {K : Subgroup G} {X₁ X₂ M₁ M₂ : G} (h12 : X₁ * X₂ = X₂ * X₁)
    (h1 : X₁ ^ 3 = 1) (h2 : X₂ ^ 3 = 1) (hM₁ : M₁ ∈ K) (hM₂ : M₂ ∈ K)
    (R1 : M₁ * X₁ * M₁⁻¹ = X₂⁻¹) (R2 : M₁ * X₂ * M₁⁻¹ = X₁)
    (R3 : M₂ * X₁ * M₂⁻¹ = X₂⁻¹ * X₁⁻¹) {y : G}
    (hy : y ∈ Subgroup.zpowers X₁ ⊔ Subgroup.zpowers X₂) (hy1 : y ≠ 1) :
    ∃ w ∈ K, w * X₁ * w⁻¹ = y := by
  obtain ⟨a, b, ha, hb, rfl⟩ := exists_pow_mul_pow h12 h1 h2 hy
  have C1 : MulAut.conj M₁ X₁ = X₂⁻¹ := R1
  have C2 : MulAut.conj M₁ X₂ = X₁ := R2
  have C3 : MulAut.conj M₂ X₁ = X₂⁻¹ * X₁⁻¹ := R3
  have hcj : ∀ w : G, w * X₁ * w⁻¹ = MulAut.conj w X₁ := fun w => rfl
  have i1 : X₁⁻¹ = X₁ ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ', h1])
  have i2 : X₂⁻¹ = X₂ ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ', h2])
  have hK3 : M₁ * M₁ * M₁ ∈ K := mul_mem (mul_mem hM₁ hM₁) hM₁
  interval_cases a <;> interval_cases b
  · exact absurd (by simp) hy1
  · refine ⟨M₁ * M₁ * M₁, hK3, ?_⟩
    rw [hcj]
    simp only [map_mul, MulAut.mul_apply, map_inv, C1, C2, inv_inv, pow_zero, pow_one, one_mul]
  · refine ⟨M₁, hM₁, ?_⟩
    rw [hcj, C1, i2, pow_zero, one_mul]
  · refine ⟨1, one_mem K, ?_⟩
    simp
  · refine ⟨M₁ * M₁ * M₂, mul_mem (mul_mem hM₁ hM₁) hM₂, ?_⟩
    rw [hcj]
    simp only [map_mul, MulAut.mul_apply, map_inv, C1, C2, C3, inv_inv, pow_one]
    exact h12.symm
  · refine ⟨M₁ * M₁ * M₁ * M₂, mul_mem hK3 hM₂, ?_⟩
    rw [hcj]
    simp only [map_mul, MulAut.mul_apply, map_inv, C1, C2, C3, inv_inv, pow_one]
    rw [i2]
  · refine ⟨M₁ * M₁, mul_mem hM₁ hM₁, ?_⟩
    rw [hcj]
    simp only [map_mul, MulAut.mul_apply, map_inv, C1, C2, pow_zero, mul_one]
    exact i1
  · refine ⟨M₁ * M₂, mul_mem hM₁ hM₂, ?_⟩
    rw [hcj]
    simp only [map_mul, MulAut.mul_apply, map_inv, C1, C2, C3, inv_inv, pow_one]
    rw [i1]
  · refine ⟨M₂, hM₂, ?_⟩
    rw [hcj, C3, i1, i2]
    exact (Commute.pow_pow (show Commute X₂ X₁ from h12.symm) 2 2).eq

theorem fused_of_q8 {K : Subgroup G} {X₁ X₂ M₁ M₂ : G} (h12 : X₁ * X₂ = X₂ * X₁)
    (h1 : X₁ ^ 3 = 1) (h2 : X₂ ^ 3 = 1) (hM₁ : M₁ ∈ K) (hM₂ : M₂ ∈ K)
    (R1 : M₁ * X₁ * M₁⁻¹ = X₂⁻¹) (R2 : M₁ * X₂ * M₁⁻¹ = X₁)
    (R3 : M₂ * X₁ * M₂⁻¹ = X₂⁻¹ * X₁⁻¹) :
    ∀ y ∈ Subgroup.zpowers X₁ ⊔ Subgroup.zpowers X₂, y ≠ 1 →
      ∀ z ∈ Subgroup.zpowers X₁ ⊔ Subgroup.zpowers X₂, z ≠ 1 → ∃ l ∈ K, l * y * l⁻¹ = z := by
  intro y hy hy1 z hz hz1
  obtain ⟨u, hu, rfl⟩ := exists_conj_eq_of_q8 h12 h1 h2 hM₁ hM₂ R1 R2 R3 hy hy1
  obtain ⟨v, hv, rfl⟩ := exists_conj_eq_of_q8 h12 h1 h2 hM₁ hM₂ R1 R2 R3 hz hz1
  exact ⟨v * u⁻¹, mul_mem hv (inv_mem hu), by group⟩

omit [Finite G] in
theorem mem_normalizer_zpowers_sup_of {c g : G} {B : Subgroup G} (hgc : g * c = c * g)
    (hgB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((Subgroup.zpowers c ⊔ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hgB ⊢
  rw [Subgroup.map_sup, hgB, MonoidHom.map_zpowers]
  congr 2
  change g * c * g⁻¹ = c
  rw [hgc, mul_inv_cancel_right]

theorem inf_ne_bot_of_ctx
    (h131 : Item131) {A L : Subgroup G} {c : G}
    (hD : Sec13Data G A c L) (hcL : c ∉ L) (hAN : A ≤ Subgroup.normalizer (L : Set G)) :
    A ⊓ L ≠ ⊥ := by
  intro hbot
  rcases cases131 h131 sporadicModels131 slTwoCenter hD with ⟨-, h9, -⟩ | ⟨-, h9, -⟩ |
      ⟨-, -, ⟨eZ⟩, -⟩ | ⟨hcL', -⟩
  · rw [hbot, Subgroup.card_bot] at h9
    omega
  · rw [hbot, Subgroup.card_bot] at h9
    omega
  · have htriv : Sec4.autIn L A = ⊥ := by
      rw [eq_bot_iff]
      intro σ hσ
      obtain ⟨l, hlN, hlL, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
      rw [Subgroup.mem_bot]
      ext a
      rw [Sec4.normalizerMonoidHom_apply_coe, MulAut.one_apply]
      have hmem : l * (a : G) * l⁻¹ * (a : G)⁻¹ ∈ A ⊓ L := by
        refine ⟨A.mul_mem ((Subgroup.mem_normalizer_iff.mp hlN a).mp a.2) (A.inv_mem a.2), ?_⟩
        have h1 : (a : G) * l⁻¹ * (a : G)⁻¹ ∈ L :=
          (Subgroup.mem_normalizer_iff.mp (hAN a.2) l⁻¹).mp (L.inv_mem hlL)
        have h2 : l * (a : G) * l⁻¹ * (a : G)⁻¹ = l * ((a : G) * l⁻¹ * (a : G)⁻¹) := by group
        rw [h2]
        exact L.mul_mem hlL h1
      rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at hmem
      exact hmem
    have h1 := Nat.card_congr eZ.toEquiv
    rw [htriv, Subgroup.card_bot, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      ZMod.card] at h1
    omega
  · exact hcL hcL'

structure L34Facts {G : Type} [Group G] [Finite G] (A L E : Subgroup G) (c : G) : Prop where
  sec13 : Sec13Data G A c L
  c_not_mem : c ∉ L
  c_mem : c ∈ E
  c_mem_A : c ∈ A
  orderOf_c : orderOf c = 3
  theta_eq : aschbacherSolvableCore 3 L = CFSG.pCore 2 L
  isoLThreePi : Sec4.IsoLThreePi (L ⧸ aschbacherSolvableCore 3 L) 2 2
  perfect : Group.IsPerfect L
  card_inf : Nat.card (E ⊓ L : Subgroup G) = 9
  isPGroup_sup : IsPGroup 3 (E ⊔ A : Subgroup G)
  le_normalizer : E ⊔ A ≤ Subgroup.normalizer (L : Set G)
  le_normalizer_inf : E ⊔ A ≤ Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G)
  le_centralizer : E ⊔ A ≤ Subgroup.centralizer ({c} : Set G)
  le_normalizer_E : A ≤ Subgroup.normalizer (E : Set G)
  card_sup : Nat.card (E ⊔ A : Subgroup G) = 81
  inf_eq : E ⊓ L = (E ⊔ A) ⊓ L

theorem l34Facts_of
    (h131 : Item131) {A L E M : Subgroup G} {c : G}
    (hctx : Ctx1912 G A c L E M)
    (hφ : Nonempty (L ⧸ CFSG.pCore 2 L ≃* projSL 3 (GaloisField 2 2)))
    (hEeq : E = Subgroup.zpowers c ⊔ (E ⊓ L)) (hdisj : Subgroup.zpowers c ⊓ (E ⊓ L) = ⊥) :
    L34Facts A L E c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hst := hctx.toPartTwoStanding
  have hEE : E ∈ partTwoE G := hctx.mem_partTwoT.1
  have hE := isE27_of_mem_partTwoE hEE
  have hAE := isE27_of_mem_partTwoE hctx.mem_partTwoE
  have hA : CFSG.Assembly.IsElemAbelian 3 A := hctx.mem_partTwoE.1
  have hcA : c ∈ A := hctx.zpowers_mem_omegaA.1 (Subgroup.mem_zpowers c)
  have hcE : c ∈ E :=
    mem_of_le_centralizer hst hctx.partTwoS_eq hEE (hA.2 c hcA) hctx.le_centralizer
  have hcL : c ∉ L := hctx.hypS.2.2 c hctx.zpowers_mem_omegaA L hctx.mem_lA
  have hc3 : c ^ 3 = 1 := hA.2 c hcA
  have hc1 : c ≠ 1 := fun h1 => hcL (h1 ▸ L.one_mem)
  have hco : orderOf c = 3 := by
    rw [← Nat.card_zpowers]
    exact hctx.zpowers_mem_omegaA.2.1
  have hFE : partTwoF G = partTwoE G :=
    (hctx.toTheoremFourHyp.partTwoF_eq_partTwoE hctx.partTwoS_eq).1
  have hD : Sec13Data G A c L := ⟨hst, hctx.partTwoS_eq, hFE ▸ hctx.mem_partTwoE,
    hctx.not_mem_partTwoT, hctx.zpowers_mem_omegaA, hctx.mem_lA⟩
  have hiso : Sec4.IsoLThreePi (L ⧸ CFSG.pCore 2 L) 2 2 := Or.inl ⟨by norm_num, hφ⟩
  have hLperf : Group.IsPerfect L := isPerfect_of_mem_thetaComponentsIn hctx.mem_lA.1
  obtain ⟨hXs, -⟩ := Step1914TriProof.isSimpleGroup_of_isoLThreePi (by norm_num) hiso
  have hθeq : aschbacherSolvableCore 3 L = CFSG.pCore 2 L :=
    Step1914TriProof.theta_eq_pCore_two_of_isSimpleGroup
  have hisoθ : Sec4.IsoLThreePi (L ⧸ aschbacherSolvableCore 3 L) 2 2 := by
    obtain ⟨φ⟩ := hφ
    exact Or.inl ⟨by norm_num, ⟨(QuotientGroup.quotientMulEquivOfEq hθeq).trans φ⟩⟩
  have hL3 : IsLThreePi (L ⧸ aschbacherSolvableCore 3 L) :=
    ⟨2, 2, inferInstance, by norm_num, hisoθ⟩
  have h9 : ¬ (2 ^ 2 % 9 = 1 ∨ 2 ^ 2 % 9 = 8) := by norm_num
  have hB9 : Nat.card (E ⊓ L : Subgroup G) = 9 := by
    have hle : E ⊓ L ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
      (inf_le_left.trans (le_centralizer_of_mem hE.1.1 hcE)).trans
        (Sec13.centralizer_le_normalizer_zpowers c)
    have h1 := CFSG.RankThree.CentralCover.card_sup_eq_mul_of_le_normalizer hle hdisj
    rw [← hEeq, hE.2, Nat.card_zpowers, hco] at h1
    omega
  have hBab : CFSG.Assembly.IsElemAbelian 3 (E ⊓ L) :=
    ⟨⟨⟨fun x y => Subtype.ext (congrArg (Subtype.val : E → G)
      (hE.1.1.is_comm.comm ⟨x, x.2.1⟩ ⟨y, y.2.1⟩))⟩⟩, fun x hx => hE.1.2 x hx.1⟩
  have hθ := solvable_prime_complement_core_characterization (H := L) Nat.prime_three
  have hfacL : (Nat.card L).factorization 3 = 2 := by
    rw [(aschbacherSolvableCore 3 L).card_eq_card_quotient_mul_card_subgroup,
      Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
      Item138Proof.factorization_card_three_eq_two (by norm_num) hisoθ h9,
      Nat.factorization_eq_zero_of_not_dvd hθ.2.2.1]
  have hP3 : IsPGroup 3 (E ⊔ A : Subgroup G) := hctx.isPGroup_sup
  have h3L : 3 ∣ Nat.card L :=
    (Step1914TriProof.three_dvd_card_of_isoLThreePi (by norm_num) hiso).trans
      (Subgroup.card_quotient_dvd_card _)
  have hAC : A ≤ Subgroup.centralizer ({c} : Set G) := le_centralizer_of_mem hA.1 hcA
  have hEAC : E ⊔ A ≤ Subgroup.centralizer ({c} : Set G) := sup_le hctx.le_centralizer hAC
  have hPN : E ⊔ A ≤ Subgroup.normalizer (L : Set G) :=
    (hEAC.trans (Sec13.centralizer_le_normalizer_zpowers c)).trans
      (Step1914TriProof.normalizer_zpowers_le_of_three_dvd hctx h3L)
  have hPL9 : Nat.card ((E ⊔ A) ⊓ L : Subgroup G) ≤ 9 := by
    have h1 := Item138Proof.card_le_of_isPGroup (p := 3) (inf_le_right : (E ⊔ A) ⊓ L ≤ L)
      (hP3.to_le inf_le_left)
    rwa [hfacL] at h1
  have hBPL : E ⊓ L = (E ⊔ A) ⊓ L :=
    Subgroup.eq_of_le_of_card_ge (inf_le_inf_right L le_sup_left) (by rw [hB9]; exact hPL9)
  have hPNB : E ⊔ A ≤ Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G) := by
    intro x hx
    rw [hBPL, Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hyP, hyL⟩
      exact ⟨(E ⊔ A).mul_mem ((E ⊔ A).mul_mem hx hyP) ((E ⊔ A).inv_mem hx),
        (Subgroup.mem_normalizer_iff.mp (hPN hx) y).mp hyL⟩
    · rintro ⟨hyP, hyL⟩
      refine ⟨?_, (Subgroup.mem_normalizer_iff.mp (hPN hx) y).mpr hyL⟩
      have h1 : x⁻¹ * (x * y * x⁻¹) * x ∈ E ⊔ A :=
        (E ⊔ A).mul_mem ((E ⊔ A).mul_mem ((E ⊔ A).inv_mem hx) hyP) hx
      simpa [mul_assoc] using h1
  have hAEN : A ≤ Subgroup.normalizer (E : Set G) := by
    intro a ha
    have h1 := mem_normalizer_zpowers_sup_of
      (congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨c, hcA⟩)) (hPNB (le_sup_right (a := E) ha))
    rwa [← hEeq] at h1
  have hALne := inf_ne_bot_of_ctx h131 hD hcL hctx.mem_lA.2.1
  have hALE : A ⊓ L ≤ E := by
    have h1 : A ⊓ L ≤ (E ⊔ A) ⊓ L := inf_le_inf_right L le_sup_right
    rw [← hBPL] at h1
    exact h1.trans inf_le_left
  have hAL3 : 3 ≤ Nat.card (A ⊓ L : Subgroup G) := by
    have hdvd : Nat.card (A ⊓ L : Subgroup G) ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hAE.2]
      exact Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hALne (Subgroup.card_eq_one.mp (by rw [hk, pow_zero]))
    rw [hk]
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hk0)
  have hAE9 : 9 ≤ Nat.card (A ⊓ E : Subgroup G) := by
    have hle : A ⊓ L ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
      (inf_le_left.trans hAC).trans (Sec13.centralizer_le_normalizer_zpowers c)
    have hdisj' : Subgroup.zpowers c ⊓ (A ⊓ L) = ⊥ :=
      eq_bot_iff.mpr ((inf_le_inf_left _ inf_le_right).trans (zpowers_inf_eq_bot hc3 hcL).le)
    have h1 := CFSG.RankThree.CentralCover.card_sup_eq_mul_of_le_normalizer hle hdisj'
    rw [Nat.card_zpowers, hco] at h1
    have h2 : Subgroup.zpowers c ⊔ (A ⊓ L) ≤ A ⊓ E :=
      sup_le (Subgroup.zpowers_le.mpr ⟨hcA, hcE⟩) (le_inf inf_le_left hALE)
    have h3 := Subgroup.card_le_of_le h2
    omega
  have hP81 : Nat.card (E ⊔ A : Subgroup G) = 81 := by
    have hcard := Sec6.card_sup_mul_card_inf hAEN
    rw [hAE.2, hE.2, sup_comm] at hcard
    have hne : Nat.card (A ⊓ E : Subgroup G) ≠ 27 := by
      intro h27
      have hAE' : A ⊓ E = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h27, hAE.2])
      have hle : A ≤ E := hAE' ▸ inf_le_right
      have heq : A = E := Subgroup.eq_of_le_of_card_ge hle (by rw [hE.2, hAE.2])
      exact hctx.not_mem_partTwoT (heq ▸ hctx.mem_partTwoT)
    have hdvd : Nat.card (A ⊓ E : Subgroup G) ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hAE.2]
      exact Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    interval_cases k
    · rw [hk] at hAE9; norm_num at hAE9
    · rw [hk] at hAE9; norm_num at hAE9
    · rw [hk] at hcard; norm_num at hcard; omega
    · exact absurd hk hne
  exact ⟨hD, hcL, hcE, hcA, hco, hθeq, hisoθ, hLperf, hB9, hP3, hPN, hPNB, hEAC, hAEN, hP81,
    hBPL⟩

end Step1914MoreSProof

open Step1914MoreSProof in
theorem step1914MoreSL34_of_cartan
    (h131 : Item131) (htri : Step1914Tri) (h195 : Item195)
    (hSyl : Item138SylowN) (hS : Item138SN) (hcart : Step1914MoreL34Cartan) :
    Step1914MoreSL34 := by
  intro G _ _ A c L E M hctx hLM hφ hEeq hdisj
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEE : E ∈ partTwoE G := hctx.mem_partTwoT.1
  have hE := isE27_of_mem_partTwoE hEE
  obtain ⟨hD, hcL, hcE, -, -, -, hisoθ, -, hB9, hP3, hPN, -, hEAC, -, hP81, -⟩ :=
    l34Facts_of h131 hctx hφ hEeq hdisj
  have hL3 : IsLThreePi (L ⧸ aschbacherSolvableCore 3 L) :=
    ⟨2, 2, inferInstance, by norm_num, hisoθ⟩
  have h9 : ¬ (2 ^ 2 % 9 = 1 ∨ 2 ^ 2 % 9 = 8) := by norm_num
  have hBab : CFSG.Assembly.IsElemAbelian 3 (E ⊓ L) :=
    ⟨⟨⟨fun x y => Subtype.ext (congrArg (Subtype.val : E → G)
      (hE.1.1.is_comm.comm ⟨x, x.2.1⟩ ⟨y, y.2.1⟩))⟩⟩, fun x hx => hE.1.2 x hx.1⟩
  obtain ⟨F, hFP, hcF, hF3, hF27, hFout, hFsec, hFC⟩ := hcart G A c L E M hctx hφ hEeq hdisj
  have hF : IsE27 F := ⟨hF3, hF27⟩
  have hFNE : F ≤ Subgroup.normalizer (E : Set G) :=
    hFP.trans (le_normalizer_of_card le_sup_left hE.2 hP81)
  have hENF : E ≤ Subgroup.normalizer (F : Set G) :=
    le_sup_left.trans (le_normalizer_of_card hFP hF27 hP81)
  have hFE9 : 9 ≤ Nat.card (F ⊓ E : Subgroup G) := by
    have hcard := Sec6.card_sup_mul_card_inf hFNE
    have hle : Nat.card (F ⊔ E : Subgroup G) ≤ 81 :=
      hP81 ▸ Subgroup.card_le_of_le (sup_le hFP le_sup_left)
    rw [hF27, hE.2] at hcard
    by_contra hlt
    push Not at hlt
    have : Nat.card (F ⊔ E : Subgroup G) * Nat.card (F ⊓ E : Subgroup G) ≤ 81 * 8 :=
      Nat.mul_le_mul hle (by omega)
    omega
  have hF𝓔 := mem_partTwoE_of_nine_le hctx hF hFE9
  have hFM := le_M_of_nine_le hctx hF hFE9
  have hFc : F ≤ Subgroup.centralizer ({c} : Set G) := hFP.trans hEAC
  have hFA : IsPGroup 3 (F ⊔ A : Subgroup G) := hP3.to_le (sup_le hFP le_sup_right)
  have hFT : F ∉ partTwoT G := by
    intro hFT
    obtain ⟨-, M', hM'⟩ := mem_partTwoT_iff.mp hFT
    have hM'M := eq_of_mem_scriptM hctx hF hFM hM'
    rcases htri G A c L F M' (ctx1912_of_mem_partTwoT hctx hFT hFc hFA hM') with hLM' |
        ⟨-, hFeq, -⟩ | hM12
    · exact hLM (hM'M ▸ hLM')
    · apply hFout
      rw [hFeq]
      exact sup_le_sup_left inf_le_right _
    · obtain ⟨φ⟩ := hφ
      obtain ⟨ψ⟩ := hM12
      exact KFacts.KS14.not_isoLThreePi_M12 2 2 (Or.inl ⟨by norm_num, ⟨ψ.symm.trans φ⟩⟩)
  have hSF : HypS F := h195 G hctx.toSec19Std F hF𝓔 hFT
  have hH : Hyp138 A c L F := ⟨hD, hL3, hcF, hF3, hF27, hFP.trans hPN, hFsec, Or.inl hSF, hFC⟩
  obtain ⟨X₁, X₂, M₁, M₂, -, hBX, hM₁L, hM₂L, -, -, R1, R2, R3, -⟩ :=
    Item138Proof.exists_q8_lift inf_le_right hBab hB9 (by norm_num : 1 ≤ 2) hisoθ h9
  have hX₁B : X₁ ∈ E ⊓ L := hBX ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers X₁)
  have hX₂B : X₂ ∈ E ⊓ L := hBX ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers X₂)
  have h12 : X₁ * X₂ = X₂ * X₁ :=
    congrArg Subtype.val (hBab.1.is_comm.comm ⟨X₁, hX₁B⟩ ⟨X₂, hX₂B⟩)
  have hfus : ∀ y ∈ E ⊓ L, y ≠ 1 → ∀ z ∈ E ⊓ L, z ≠ 1 → ∃ l ∈ L, l * y * l⁻¹ = z := by
    rw [hBX]
    exact fused_of_q8 h12 (hBab.2 X₁ hX₁B) (hBab.2 X₂ hX₂B) hM₁L hM₂L R1 R2 R3
  have hEFL : E ≤ F ⊔ L := by
    rw [hEeq]
    exact sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left hcF))
      (inf_le_right.trans le_sup_right)
  have hIsF : IsF138N L F E := ⟨⟨hEFL, hE.1, hE.2, hfus, hENF⟩, hB9⟩
  have hPGL := Item138Proof.isZ3PGLThreePi_of_not_le hH hFout
  exact hS G A c L F hH E hIsF hPGL (hSyl G A c L F hH E hIsF hPGL)

end CFSG.RankThree.PartTwo.Sec19
