module

public import CFSG.RankThree.PartTwo.Sec21.Item21Early2ProofModels
public import Certificates.Certificate8018
public import Certificates.Certificate8019
public import Certificates.Certificate8020
public import Certificates.Certificate8021
public import Certificates.Certificate8024
public import Certificates.Certificate8026
public import Certificates.Certificate8029
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate123
import CFSG.RankThree.Asc83Table.M22
import CFSG.RankThree.Asc83Table.M23
import CFSG.RankThree.Asc83Table.Reduction
import CFSG.LocalAnalysis.SectionRank.Sporadic.HSLocal
import CFSG.LocalAnalysis.SectionRank.Sporadic.HeLocal
import CFSG.LocalAnalysis.SectionRank.Sporadic.J2Local
import CFSG.LocalAnalysis.SectionRank.Sporadic.RuLocal
import CFSG.LocalAnalysis.SectionRank.Sporadic.J4Local
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocal
import CFSG.LocalAnalysis.SectionRank.Sporadic.J3
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.RankThree.PartTwo.Late.GammaZero
import CFSG.RankThree.PartTwo.Sec13.Item13ResProofCentral
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec13.Item135SimpleReduce
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134EvenClassical
import CFSG.RankThree.PartOne.S12.ModelTransport
import CFSG.Adapters.RankTwoModelTransports
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVTorus
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherUTools
import CFSG.RankThree.PartTwo.Sec4.Item47CasesEven
import CFSG.Quasithin.Background.A3FactsExceptional
public import CFSG.GroupTheory.BaerSuzuki
public import CFSG.RankThree.PartTwo.Sec4.LThreePiSLOn
public import CFSG.RankThree.PartTwo.Sec7.ThreeTranspositions
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import Certificates.Certificate3084
public import Certificates.Certificate3139
public import Certificates.Certificate3168
public import Certificates.Certificate3169
public import Certificates.Certificate8026Base
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
import CFSG.RankThree.Asc83Table.PermTables
import CFSG.RankThree.PartTwo.Sec11.Data
import CFSG.RankThree.PartTwo.Sec13.Item135Simple
import CFSG.RankThree.PartTwo.Sec13.Item13ResProofA7Z3
import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
import CFSG.RankThree.PartTwo.Sec6.Statements
import CFSG.Sporadic.Schreier.M22
import Certificates.Certificate8035

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedProj StatedSL StatedSp)
open CFSG.Blueprint
open scoped commutatorElement

namespace Item21Early2Proof

theorem exists_e9_of_e9Basis {Y : Type*} [Group Y] (E : Asc83Table.E9Basis Y) :
    ∃ F : Subgroup Y, Monoid.exponent F ∣ 3 ∧ Nat.card F = 9 := by
  have := Asc83Table.E9Basis.isElementaryAbelian E
  exact ⟨E.sub, IsElementaryAbelian.exponent_dvd_p 3 E.sub, E.card⟩

theorem exists_e9_of_square {Y : Type*} [Group Y] {x y : Y} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hxy : x * y = y * x) (hc : Nat.card (Subgroup.closure ({x, y} : Set Y)) = 3 ^ 2) :
    ∃ F : Subgroup Y, Monoid.exponent F ∣ 3 ∧ Nat.card F = 9 :=
  exists_e9_of_e9Basis ⟨x, y, hx, hy, hxy, by rw [hc]; norm_num⟩

theorem exists_e9_of_cubic {Y : Type*} [Group Y] [Finite Y] {x y : Y} (hx : x ^ 3 = 1)
    (hy : y ^ 3 = 1) (hz1 : ⁅x, y⁆ ≠ 1) (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y) :
    ∃ F : Subgroup Y, Monoid.exponent F ∣ 3 ∧ Nat.card F = 9 :=
  exists_e9_of_e9Basis (Asc83Table.ex27Basis hx hy hzx hzy hz1 0)

theorem exists_e9_of_two_le_pRank {Y : Type*} [Group Y] [Finite Y]
    (h : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y)) :
    ∃ F : Subgroup Y, Monoid.exponent F ∣ 3 ∧ Nat.card F = 9 := by
  obtain ⟨E, -, hE, hcard⟩ := Late.exists_elemAbelian_le_of_le_pRank_three h
  refine ⟨E, Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext ?_, ?_⟩
  · rw [Subgroup.coe_pow, hE.2 x x.2, Subgroup.coe_one]
  · rw [hcard]; norm_num

theorem two_le_pRank_of_elemAbelian {Y : Type*} [Group Y] [Finite Y] {E : Subgroup Y}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) {k : ℕ} (hk : 2 ≤ k) (hcard : Nat.card E = 3 ^ k) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) :=
  le_trans hk (CFSG.SectionRank.le_pRank (by norm_num) le_top hE hcard)

theorem three_dvd_two_pow_sub_one {n : ℕ} (hn : Even n) : 3 ∣ 2 ^ n - 1 := by
  have h := two_pow_mod_three_of_even hn
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  omega

theorem exists_e9_M22 : ∃ F : Subgroup NativeSporadic.M22, Monoid.exponent F ∣ 3 ∧
    Nat.card F = 9 :=
  exists_e9_of_e9Basis Asc83Table.M22.E

theorem exists_e9_M23 : ∃ F : Subgroup NativeSporadic.M23, Monoid.exponent F ∣ 3 ∧
    Nat.card F = 9 :=
  exists_e9_of_e9Basis Asc83Table.M23.E

theorem exists_e9_HS :
    ∃ F : Subgroup NativeSporadic.HS, Monoid.exponent F ∣ 3 ∧ Nat.card F = 9 := by
  obtain ⟨x, y, -, hx, hy, hxy, hc, -⟩ := CFSG.SectionRank.HS_sylow3_square_witness
  exact exists_e9_of_square hx hy hxy hc

theorem exists_e9_M24 :
    ∃ F : Subgroup NativeSporadic.M24, Monoid.exponent F ∣ 3 ∧ Nat.card F = 9 := by
  obtain ⟨x, y, -, hx, hy, hz1, hzx, hzy, -⟩ := CFSG.SectionRank.M24_sylow3_cubic_witness
  exact exists_e9_of_cubic hx hy hz1 hzx hzy

theorem exists_e9_He :
    ∃ F : Subgroup NativeSporadic.He, Monoid.exponent F ∣ 3 ∧ Nat.card F = 9 := by
  obtain ⟨x, y, -, hx, hy, hz1, hzx, hzy, -⟩ := CFSG.SectionRank.He_sylow3_cubic_witness
  exact exists_e9_of_cubic hx hy hz1 hzx hzy

theorem exists_e9_J2 :
    ∃ F : Subgroup NativeSporadic.J2, Monoid.exponent F ∣ 3 ∧ Nat.card F = 9 := by
  obtain ⟨x, y, -, hx, hy, hz1, hzx, hzy, -⟩ := CFSG.SectionRank.J2_sylow3_cubic_witness
  exact exists_e9_of_cubic hx hy hz1 hzx hzy

theorem exists_e9_Ru :
    ∃ F : Subgroup NativeSporadic.Ru, Monoid.exponent F ∣ 3 ∧ Nat.card F = 9 := by
  obtain ⟨x, y, -, hx, hy, hz1, hzx, hzy, -⟩ := CFSG.SectionRank.Ru_sylow3_cubic_witness
  exact exists_e9_of_cubic hx hy hz1 hzx hzy

theorem exists_e9_J4 :
    ∃ F : Subgroup NativeSporadic.J4, Monoid.exponent F ∣ 3 ∧ Nat.card F = 9 := by
  obtain ⟨x, y, -, hx, hy, hz1, hzx, hzy, -⟩ := CFSG.SectionRank.J4_sylow3_cubic_witness
  exact exists_e9_of_cubic hx hy hz1 hzx hzy

theorem exists_e9_J3 :
    ∃ F : Subgroup NativeSporadic.J3, Monoid.exponent F ∣ 3 ∧ Nat.card F = 9 := by
  obtain ⟨E, hE, hcard⟩ := CFSG.SectionRank.J3_elementary_three_rank_three
  exact exists_e9_of_two_le_pRank (two_le_pRank_of_elemAbelian hE (by norm_num) hcard)


theorem exists_e9_projSL_three {n : ℕ} (hn : 1 ≤ n) (he : Even n) :
    ∃ F : Subgroup (projSL 3 (GaloisField 2 n)), Monoid.exponent F ∣ 3 ∧ Nat.card F = 9 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨D, hD, hD9⟩ := Sec13.exists_elemAbelian_nine_projImage_slPi
    (Sec13.piField_galoisField 2 n hn) (show Sec4.ModThree true (2 ^ n) from
      two_pow_mod_three_of_even he)
  let ψ : projSL 3 (GaloisField 2 n) ≃*
      CFSG.Assembly.RankThreeEven.projImage (Sec4.slPi true 3 (2 ^ n) (GaloisField 2 n)) :=
    MulEquiv.subgroupCongr (Sec13.projSL_eq 2 n)
  exact ⟨D.map ψ.symm.toMonoidHom,
    Sec13.exponent_dvd_three_of_isElemAbelian (Sec13.isElemAbelian_map hD ψ.symm.toMonoidHom),
    by rw [Subgroup.card_map_of_injective ψ.symm.injective, hD9]⟩

noncomputable def statedProjSLEquiv (m : ℕ) (K : Type) [Field K] :
    StatedProj (StatedSL m K) ≃* projSL m K :=
  (CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk (StatedSL m K)).trans
    (MulEquiv.subgroupCongr (CFSG.RankThree.PartOne.projImage_statedSL_eq_projSL m K))

noncomputable def statedProjSpEquiv (m : ℕ) (K : Type) [Field K] :
    StatedProj (StatedSp m K) ≃* projSp m K :=
  (CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk (StatedSp m K)).trans
    (MulEquiv.subgroupCongr (CFSG.RankThree.PartOne.projImage_statedSp_eq_projSp m K))

theorem two_le_pRank_of_mulEquiv' {Y S : Type*} [Group Y] [Group S] [Finite Y] [Finite S]
    (e : Y ≃* S) (h : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S)) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) := by
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
  exact h

theorem exists_e9_projSp {Y : Type} [Group Y] [Finite Y] {m : ℕ} (hm : 2 ≤ m) {K : Type}
    [Field K] [Finite K] (e : Y ≃* projSp m K) :
    ∃ F : Subgroup Y, Monoid.exponent F ∣ 3 ∧ Nat.card F = 9 :=
  have : Finite (StatedProj (StatedSp m K)) :=
    Finite.of_equiv Y (e.trans (statedProjSpEquiv m K).symm).toEquiv
  exists_e9_of_two_le_pRank (two_le_pRank_of_mulEquiv' (e.trans (statedProjSpEquiv m K).symm)
    (CFSG.QuasithinUnique.Vol2Native.EvenWit.two_le_pRank_three_psp hm))

theorem exists_e9_projSL {Y : Type} [Group Y] [Finite Y] {m : ℕ} (hm : 4 ≤ m) {K : Type}
    [Field K] [Finite K] (e : Y ≃* projSL m K) :
    ∃ F : Subgroup Y, Monoid.exponent F ∣ 3 ∧ Nat.card F = 9 :=
  have : Finite (StatedProj (StatedSL m K)) :=
    Finite.of_equiv Y (e.trans (statedProjSLEquiv m K).symm).toEquiv
  exists_e9_of_two_le_pRank (two_le_pRank_of_mulEquiv' (e.trans (statedProjSLEquiv m K).symm)
    (CFSG.QuasithinUnique.Vol2Native.EvenWit.two_le_pRank_three_psl hm))

theorem exists_e9_projSU_four_odd {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hn : Odd n)
    (e : Y ≃* projSU 4 2 n) : ∃ F : Subgroup Y, Monoid.exponent F ∣ 3 ∧ Nat.card F = 9 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn1 : 1 ≤ n := by obtain ⟨k, rfl⟩ := hn; omega
  have h3 : 3 ∣ 2 ^ n + 1 := by
    obtain ⟨k, rfl⟩ := hn
    have h := Nat.pow_mod 4 k 3
    rw [show (4 : ℕ) % 3 = 1 by norm_num, one_pow] at h
    rw [pow_succ, pow_mul]
    norm_num
    omega
  obtain ⟨E, hE, hcard⟩ := Sec4.Item434SmallTwoIV.exists_elemAbelian_projSU_torus 3 2 n hn1 h3
    (by norm_num)
  have : Finite (projSU 4 2 n) := Finite.of_equiv Y e.toEquiv
  exact exists_e9_of_two_le_pRank (two_le_pRank_of_mulEquiv' e
    (two_le_pRank_of_elemAbelian hE (by norm_num) hcard))

section UnitaryTorus

open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary Matrix
open Sec4.Item434SmallTwoOther.UTools

theorem card_gfq {n : ℕ} (hn : 1 ≤ n) : Nat.card (GaloisField 2 (2 * n)) = (2 ^ n) ^ 2 := by
  rw [GaloisField.card 2 (2 * n) (by omega), ← pow_mul, mul_comm]

theorem two_eq_zero_gfq (n : ℕ) : (2 : GaloisField 2 (2 * n)) = 0 := by
  exact_mod_cast CharP.cast_eq_zero (GaloisField 2 (2 * n)) 2

theorem exists_orderOf_eq_three_gfq {n : ℕ} (hn : 1 ≤ n) :
    ∃ ω : (GaloisField 2 (2 * n))ˣ, orderOf ω = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : Nat.card (GaloisField 2 (2 * n))ˣ = (2 ^ n) ^ 2 - 1 :=
    card_units_of_card (p := 2) (card_gfq hn)
  refine exists_prime_orderOf_dvd_card' 3 ?_
  rw [hc, ← pow_mul, mul_comm, pow_mul]
  have h := Nat.pow_mod 4 n 3
  rw [show (4 : ℕ) % 3 = 1 by norm_num, one_pow] at h
  have h1 : 1 ≤ 4 ^ n := Nat.one_le_pow _ _ (by norm_num)
  norm_num
  omega

theorem exists_e9_projSU_even {m n : ℕ} (hm : 4 ≤ m) (hn : 2 ≤ n) (he : Even n) :
    ∃ F : Subgroup (projSU m 2 n), Monoid.exponent F ∣ 3 ∧ Nat.card F = 9 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn1 : 1 ≤ n := by omega
  set σ := unitaryInvolution (GaloisField 2 (2 * n)) 2 n with hσdef
  have hσ : IsUnitaryInvolution σ := isUnitaryInvolution_unitaryInvolution (card_gfq hn1)
  obtain ⟨ω, hω⟩ := exists_orderOf_eq_three_gfq hn1
  set Z : Subgroup (GaloisField 2 (2 * n))ˣ := Subgroup.zpowers ω with hZdef
  have hZ3 : Nat.card Z = 3 := by rw [hZdef, Nat.card_zpowers, hω]
  have hfix : ∀ a ∈ Z, σ (a : GaloisField 2 (2 * n)) = a := by
    intro a ha
    have h3 : a ^ 3 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, ← hω]
      exact orderOf_dvd_of_mem_zpowers ha
    have h3' : (a : GaloisField 2 (2 * n)) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, h3, Units.val_one]
    rw [hσdef, unitaryInvolution_apply]
    obtain ⟨k, hk⟩ : ∃ k, 2 ^ n = 3 * k + 1 := ⟨2 ^ n / 3, by
      have := two_pow_mod_three_of_even he
      omega⟩
    rw [hk, pow_succ, pow_mul, h3', one_pow, one_mul]
  obtain ⟨W⟩ := hσ.nonempty_wittData
  have hproj : projSU m 2 n =
      (SUid σ m).map (ProjGenLinGroup.mk : GL (Fin m) (GaloisField 2 (2 * n)) →* _) := by
    rw [Sec4.projSU_eq_map_statedSU, SUid_eq_statedSU (card_gfq hn1) m]
  let π : SUid σ m →* projSU m 2 n :=
    (MulEquiv.subgroupCongr hproj.symm).toMonoidHom.comp
      ((ProjGenLinGroup.mk : GL (Fin m) (GaloisField 2 (2 * n)) →* _).subgroupMap (SUid σ m))
  have hπ : ∀ g : SUid σ m, π g = 1 →
      ∃ c : GaloisField 2 (2 * n), ∀ v : Fin m → GaloisField 2 (2 * n), g • v = c • v := by
    intro g hg
    have h0 : ((π g : projSU m 2 n) : ProjGenLinGroup (Fin m) (GaloisField 2 (2 * n))) = 1 := by
      rw [hg]
      rfl
    have h1 : ProjGenLinGroup.mk (g : GL (Fin m) (GaloisField 2 (2 * n))) = 1 := h0
    rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.mem_center_iff_val_mem_range_scalar] at h1
    obtain ⟨c, hc⟩ := h1
    refine ⟨c, fun v => ?_⟩
    rw [smul_def, ← hc]
    funext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  set φ := π.comp (torusHom hσ.invol (stdQuad W hm) Z hfix) with hφ
  have hinj : Function.Injective φ :=
    injective_comp_torusHom hσ (two_eq_zero_gfq n) (stdQuad W hm) hfix π hπ
  refine ⟨φ.range, Monoid.exponent_dvd_of_forall_pow_eq_one fun y => ?_, ?_⟩
  · obtain ⟨p, hp⟩ := y.2
    have hp3 : p ^ 3 = 1 := by
      have h1 : p.1 ^ 3 = 1 := by rw [← hZ3]; exact pow_card_eq_one'
      have h2 : p.2 ^ 3 = 1 := by rw [← hZ3]; exact pow_card_eq_one'
      exact Prod.ext h1 h2
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hp, ← map_pow, hp3, map_one, Subgroup.coe_one]
  · rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top,
      Nat.card_prod, hZ3]

end UnitaryTorus

theorem exists_e9_G2
    {Y : Type} [Group Y] [Finite Y] {n : ℕ} (he : Even n)
    (h : ChevalleyExceptionalModel Y .G2 2 n) :
    ∃ F : Subgroup Y, Monoid.exponent F ∣ 3 ∧ Nat.card F = 9 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, hu⟩ := CFSG.Quasithin.A3Facts.exists_unit_of_prime_dvd_pred (K := K) (r := 3)
    (by rw [hK]; exact three_dvd_two_pow_sub_one he)
  have hT := CFSG.Quasithin.A3Facts.two_le_pRank_adjoint_torus (τ := .G2) hu
    (CFSG.Quasithin.A3Facts.not_dvd_cartan_G2_det Nat.prime_three)
  let eQ : CFSG.Blueprint.AdjointQuotient .G2 K ≃*
      CFSG.Blueprint.Chevalley.adjointGroup .G2 K :=
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K))).trans
      QuotientGroup.quotientBot
  have : Finite (CFSG.Blueprint.Chevalley.adjointGroup .G2 K) :=
    Finite.of_equiv Y (e.trans eQ).toEquiv
  exact exists_e9_of_two_le_pRank (two_le_pRank_of_mulEquiv' (e.trans eQ) hT)

section Triality

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem exists_e9_D4
    {Y : Type} [Group Y] [Finite Y]
    {f : ℕ} (hf : 2 ≤ f) (he : Even f) (hS : ChevalleyExceptionalModel Y .trialityD4 2 f) :
    ∃ F : Subgroup Y, Monoid.exponent F ∣ 3 ∧ Nat.card F = 9 := by
  obtain ⟨hadm, K, _, _, hK, σ, hσq, ⟨e⟩⟩ := hS
  have hq : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hK' : Nat.card K = (2 ^ f) ^ 3 := hK
  have : CharP K 2 :=
    CFSG.SectionRank.charP_two_of_card (f := f * 3) (by rw [hK', ← pow_mul])
  have hσ3 := CFSG.LieType.Steinberg.TwistedD4.sigma_three_of_card hK' hσq
  let eD := CFSG.LieType.Steinberg.TwistedD4.twistedGroupEquivDerived σ hq hK' hσq
  have hZ := CFSG.SectionRank.center_eq_bot_of_mulEquiv' eD
    (CFSG.SectionRank.twistedGroup_center_eq_bot hσ3)
  let eS : DerivedCentralQuotient (twistedFixedGroup .D4 K σ) ≃*
      CFSG.LieType.Steinberg.TwistedD4.twistedGroup σ :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans eD.symm)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hrdvd : 3 ∣ 2 ^ f - 1 := three_dvd_two_pow_sub_one he
  have hdvd3 : 2 ^ f - 1 ∣ (2 ^ f) ^ 3 - 1 := by
    have := Nat.sub_dvd_pow_sub_pow (2 ^ f) 1 3
    rwa [one_pow] at this
  obtain ⟨u, hu⟩ := CFSG.Quasithin.A3Facts.exists_unit_of_prime_dvd_pred (K := K) (r := 3)
    (by rw [hK']; exact hrdvd.trans hdvd3)
  have hu1 : u ^ (2 ^ f - 1) = 1 := by
    have hdvd' : orderOf u ∣ 2 ^ f - 1 := by rw [hu]; exact hrdvd
    exact orderOf_dvd_iff_pow_eq_one.1 hdvd'
  have hσu : σ (u : K) = u := by
    rw [hσq]
    have h1 : u ^ (2 ^ f) = u := by
      rw [← Nat.sub_add_cancel (Nat.one_le_two_pow (n := f)), pow_succ, hu1, one_mul]
    have h2 := congrArg (fun v : Kˣ => (v : K)) h1
    simpa using h2
  have hT := CFSG.Quasithin.A3Facts.two_le_pRank_twistedGroup hσ3 hu hσu
  have : Finite (CFSG.LieType.Steinberg.TwistedD4.twistedGroup σ) :=
    Finite.of_equiv Y (e.trans eS).toEquiv
  exact exists_e9_of_two_le_pRank (two_le_pRank_of_mulEquiv' (e.trans eS) hT)

end Triality

theorem exists_e9_of_bar211Quot
    {Y : Type} [Group Y] [Finite Y] (h : Bar211Quot Y) :
    ∃ F : Subgroup Y, Monoid.exponent F ∣ 3 ∧ Nat.card F = 9 := by
  unfold Bar211Quot at h
  rcases h with h | h | h | h | h | h | h | h | h |
      ⟨n, hn, he, h⟩ | ⟨n, hn, he, hG | hD⟩ | ⟨n, hn, he, h⟩ | ⟨n, hn, h⟩ | h |
      h | h | h
  · obtain ⟨e⟩ := h; exact Sec13.ResProof.exists_e9_of_mulEquiv (Y := NativeSporadic.M22) e
      exists_e9_M22
  · obtain ⟨e⟩ := h; exact Sec13.ResProof.exists_e9_of_mulEquiv (Y := NativeSporadic.M23) e
      exists_e9_M23
  · obtain ⟨e⟩ := h; exact Sec13.ResProof.exists_e9_of_mulEquiv (Y := NativeSporadic.HS) e
      exists_e9_HS
  · obtain ⟨e⟩ := h; exact Sec13.ResProof.exists_e9_of_mulEquiv (Y := NativeSporadic.M24) e
      exists_e9_M24
  · obtain ⟨e⟩ := h; exact Sec13.ResProof.exists_e9_of_mulEquiv (Y := NativeSporadic.He) e
      exists_e9_He
  · obtain ⟨e⟩ := h; exact Sec13.ResProof.exists_e9_of_mulEquiv (Y := NativeSporadic.J2) e
      exists_e9_J2
  · obtain ⟨e⟩ := h; exact Sec13.ResProof.exists_e9_of_mulEquiv (Y := NativeSporadic.Ru) e
      exists_e9_Ru
  · obtain ⟨e⟩ := h; exact Sec13.ResProof.exists_e9_of_mulEquiv (Y := NativeSporadic.J4) e
      exists_e9_J4
  · obtain ⟨e⟩ := h; exact Sec13.ResProof.exists_e9_of_mulEquiv (Y := NativeSporadic.J3) e
      exists_e9_J3
  · obtain ⟨e⟩ := h
    exact Sec13.ResProof.exists_e9_of_mulEquiv e (exists_e9_projSL_three (by omega) he)
  · exact exists_e9_G2 he hG
  · exact exists_e9_D4 hn he hD
  · obtain ⟨e⟩ := h; exact exists_e9_projSp le_rfl e
  · obtain ⟨e⟩ := h
    rcases Nat.even_or_odd n with he | ho
    · exact Sec13.ResProof.exists_e9_of_mulEquiv e (exists_e9_projSU_even le_rfl hn he)
    · exact exists_e9_projSU_four_odd ho e
  · obtain ⟨e⟩ := h
    exact Sec13.ResProof.exists_e9_of_mulEquiv e
      (exists_e9_projSU_even (by norm_num) le_rfl even_two)
  · obtain ⟨e⟩ := h; exact exists_e9_projSL le_rfl e
  · obtain ⟨e⟩ := h; exact exists_e9_projSL (by norm_num) e
  · obtain ⟨e⟩ := h; exact exists_e9_projSp (by norm_num) e

end Item21Early2Proof

open Item21Early2Proof

theorem ks213Nine :
    KS213Nine :=
  fun _ _ _ hX => exists_e9_of_bar211Quot (bar211Quot_of_isBar211 hX)

end CFSG.RankThree.PartTwo.Sec21
