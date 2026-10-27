module

public import CFSG.RankThree.PartTwo.Sec21.Item2119End5Proof2127C
import CFSG.RankThree.PartTwo.KFacts.L34Aut
import CFSG.RankThree.PartTwo.KFacts.L34Sections
import CFSG.RankThree.PartTwo.KFacts.L34Sylow
import CFSG.RankThree.PartTwo.Sec21.Item21Late2ProofFrame
import CFSG.RankThree.PartTwo.Sec21.Item21LateProofGL33
import CFSG.RankThree.PartTwo.Sec21.Item2119End3Proof2125Unique
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.RankThree.GroupTheory.SteinbergBYCentralCoverRank
import CFSG.RankThree.Asc83Table.E27
import CFSG.GroupTheory.SteinbergCBFTFactorization
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
import CFSG.RankThree.PartTwo.Sec19.Step1917EqProofJArith
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec4.LThreePiDiag
import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartOne.S12.ModelTransport
public import CFSG.RankThree.PartOne.S9.Sylow.GlobalRelative
public import CFSG.RankThree.PartTwo.Late.GammaZero
public import CFSG.RankThree.PartTwo.Sec11.Item118
public import CFSG.RankThree.PartTwo.Sec11.Item119
public import CFSG.RankThree.PartTwo.Sec13.Item135
public import CFSG.RankThree.PartTwo.Sec13.Item135Simple
public import CFSG.RankThree.PartTwo.Sec13.Item135SimpleReduce
public import CFSG.RankThree.PartTwo.Sec18.Notation
public import CFSG.RankThree.PartTwo.Sec18.Tools
public import CFSG.RankThree.PartTwo.Sec21.Commute33
public import CFSG.RankThree.PartTwo.Sec21.Item211ProofHeis
public import CFSG.RankThree.PartTwo.Sec21.Item211ProofListOf
public import CFSG.RankThree.PartTwo.Sec21.Item21Late2ProofAssembly
public import CFSG.RankThree.PartTwo.Sec21.Item21Late2ProofChoiceY
public import CFSG.RankThree.PartTwo.Sec21.Item21LateProofChoice
public import CFSG.RankThree.PartTwo.Sec21.Item21Res6ProofNoField
public import CFSG.RankThree.PartTwo.Sec21.Item221Proof228Statements
public import CFSG.RankThree.PartTwo.Sec21.Item221ProofZGen
public import CFSG.RankThree.PartTwo.Sec21.Item223Gaps
public import CFSG.RankThree.PartTwo.Sec21.Item229Diagram
public import CFSG.RankThree.PartTwo.Sec21.Item233
public import CFSG.RankThree.PartTwo.Sec21.Item233OneProof
public import CFSG.RankThree.PartTwo.Sec21.SylowThree
public import CFSG.RankThree.PartTwo.Sec4.Item47
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.Statements423
public import CFSG.RankThree.PartTwo.Sec4.StatementsGraphField
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Schreier.RuPair
public import CFSG.Sporadic.Schreier.RuSylow
public import Certificates.Certificate2195
public import Certificates.Certificate3157
public import Certificates.Certificate3164
public import Certificates.Certificate7233Base

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2119End6Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL projImage)
open Matrix

section Order

variable {G : Type} [Group G] [Finite G]

theorem card_dvd_nine_of_le {L P : Subgroup G} (eL : lBar L ≃* projSL 3 (GaloisField 2 2))
    (hPL : P ≤ L) (hP : IsPGroup 3 P) : Nat.card P ∣ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hL : Nat.card L = Nat.card (lBar L) * Nat.card (aschbacherSolvableCore 3 L) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [Nat.card_congr eL.toEquiv, KFacts.L34.card_projSL] at hL
  have hθ : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 L) :=
    three_not_dvd_card_aschbacherSolvableCore
  have hdvd : 3 ^ k ∣ 9 * (2240 * Nat.card (aschbacherSolvableCore 3 L)) := by
    rw [← hk, ← mul_assoc, show (9 : ℕ) * 2240 = 20160 by norm_num, ← hL]
    exact Subgroup.card_dvd_of_le hPL
  have hcop : Nat.Coprime (3 ^ k) (2240 * Nat.card (aschbacherSolvableCore 3 L)) :=
    Nat.Coprime.pow_left k (Nat.Coprime.mul_right (by norm_num)
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ))
  rw [hk]
  exact hcop.dvd_of_dvd_mul_right hdvd

end Order

section Outer

variable {G : Type} [Group G] [Finite G]

theorem not_inner_of_inducesTypeOn_two {L : Subgroup G}
    (eL : lBar L ≃* projSL 3 (GaloisField 2 2)) {x : G} (hx : Sec4.InducesTypeOn L x 2)
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) (m : lBar L)
    (hm : ∀ z, Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hxN⟩) z = m * z * m⁻¹) :
    False := by
  obtain ⟨hx', π, p, f, K, _, hK, hq, e, y, -, hy2, hact⟩ := hx
  have hcard := Sec13.card_projImage_slPi_mul_three hK hq
  rw [← Nat.card_congr e.toEquiv] at hcard
  obtain ⟨rfl, rfl, hf2⟩ := Sec19.Step1917EqProof.eq_two_of_card hK.prime hK.one_le
    (by norm_num) hq hcard
    (Sec19.Step1917EqProof.card_kStar (by norm_num) (Or.inr ⟨eL⟩))
  subst hf2
  have hq2 : 2 < 2 ^ 2 := by norm_num
  have hem : (e m : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk y := by
    refine Item21Late2Proof.coe_e_eq_mk_of_inner hK hq hq2 e m y fun z => ?_
    rw [← hm z]
    exact hact z
  obtain ⟨s, hs, hsm⟩ := (e m).2
  rw [← hsm] at hem
  have hsy : ProjGenLinGroup.mk (s⁻¹ * y) = 1 := by
    rw [map_mul, map_inv, ← hem, inv_mul_cancel]
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hsy
  obtain ⟨l, hl⟩ := hsy
  have hys : y = s * GeneralLinearGroup.scalar (Fin 3) l := by
    rw [show (GeneralLinearGroup.scalar (Fin 3) l : GL (Fin 3) K) = s⁻¹ * y from hl]
    group
  have hsdet : GeneralLinearGroup.det s = 1 := by
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, Units.val_one]
    exact (Sec4.mem_slPi_true (2 ^ 2)).mp hs
  obtain ⟨τ, hτ3, hτ1, z, hz, g, -, hgz⟩ := hy2
  have hτ3' : (τ : K) ^ 3 = 1 := hτ3
  have hτ1' : (τ : K) ≠ 1 := fun h => hτ1 (Units.ext h)
  obtain ⟨ζ, -, hζ⟩ := Sec4.exists_scalar_of_mem_zPi hK hq hτ3' hτ1' hz
  have hdet := congrArg GeneralLinearGroup.det hgz
  rw [map_mul, map_mul, map_mul, hys, map_mul, hsdet, one_mul, ← hζ,
    GeneralLinearGroup.det_scalar, GeneralLinearGroup.det_scalar] at hdet
  have hdetE : GeneralLinearGroup.det (Sec4.diagE τ) = τ := by
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, Sec4.coe_diagE, det_diagonal, Fin.prod_univ_three]
    simp
  rw [hdetE] at hdet
  have hKc : Nat.card K = 2 ^ 2 := hK.card
  have : Finite K := hK.finite
  let _ := Fintype.ofFinite K
  have hKf : Fintype.card K = 4 := by rw [Fintype.card_eq_nat_card, hKc]; norm_num
  have hu3 : ∀ u : Kˣ, u ^ 3 = 1 := fun u => Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    have h := FiniteField.pow_card_sub_one_eq_one (u : K) u.ne_zero
    rwa [hKf] at h)
  have hfin : τ = (l * ζ) ^ 3 := by
    rw [← hdet, Fintype.card_fin, map_inv, mul_pow,
      mul_comm _ (GeneralLinearGroup.det g), ← mul_assoc, mul_inv_cancel, one_mul]
  exact hτ1 (by rw [hfin, hu3])

end Outer

section Linear

theorem pow_six_eq_one_of_forall_inv_mul_mem {P : Type*} [Group P]
    (h3 : ∀ x : P, x ^ 3 = 1) {M : Subgroup P}
    (hM : Nat.card M ∣ 3) {φ : MulAut P} (hφ : ∀ x, x⁻¹ * φ x ∈ M) : φ ^ 6 = 1 := by
  have hφM : ∀ m ∈ M, φ m ∈ M := fun m hm => by
    have h := M.mul_mem hm (hφ m)
    rwa [mul_inv_cancel_left] at h
  have hfix : ∀ m ∈ M, φ (φ m) = m := by
    intro m hm
    by_cases hm1 : m = 1
    · rw [hm1, map_one, map_one]
    · have hM3 : Nat.card M = 3 := by
        rcases (Nat.dvd_prime Nat.prime_three).mp hM with h | h
        · exfalso
          apply hm1
          have hbot := Subgroup.eq_bot_of_card_eq M h
          rw [hbot] at hm
          exact hm
        · exact h
      have : Finite M := Nat.finite_of_card_ne_zero (by omega)
      have hzM : Subgroup.zpowers m = M := Subgroup.eq_of_le_of_card_ge
        (Subgroup.zpowers_le.mpr hm)
        (by rw [hM3, Nat.card_zpowers, orderOf_eq_prime (h3 m) hm1])
      have hφm : φ m ∈ Subgroup.zpowers m := hzM ▸ hφM m hm
      obtain ⟨k, hk, hφk⟩ := Item21LateProof.exists_pow_lt_three_of_mem_zpowers (h3 m) hφm
      interval_cases k
      · exfalso
        apply hm1
        rw [pow_zero] at hφk
        exact φ.injective (by rw [hφk, map_one])
      · rw [pow_one] at hφk
        rw [hφk, hφk]
      · rw [hφk, map_pow, hφk, ← pow_mul]
        rw [show 2 * 2 = 3 + 1 by norm_num, pow_add, h3, one_mul, pow_one]
  set ψ := φ ^ 2 with hψ
  have hψx : ∀ x, ψ x = φ (φ x) := fun x => by rw [hψ, pow_two, MulAut.mul_apply]
  have hψM : ∀ x, x⁻¹ * ψ x ∈ M := by
    intro x
    rw [hψx]
    have h := M.mul_mem (hφ x) (hφ (φ x))
    rwa [show x⁻¹ * φ x * ((φ x)⁻¹ * φ (φ x)) = x⁻¹ * φ (φ x) by group] at h
  have hψfix : ∀ m ∈ M, ψ m = m := fun m hm => by rw [hψx, hfix m hm]
  have hψ3 : ψ ^ 3 = 1 := by
    ext x
    set m := x⁻¹ * ψ x with hmdef
    have hm : m ∈ M := hψM x
    have h1 : ψ x = x * m := by rw [hmdef]; group
    have h2 : ψ (ψ x) = x * m * m := by rw [h1, map_mul, h1, hψfix m hm]
    have h3' : ψ (ψ (ψ x)) = x * m * m * m := by
      rw [h2, map_mul, map_mul, h1, hψfix m hm]
    rw [MulAut.one_apply, pow_three, MulAut.mul_apply, MulAut.mul_apply, h3',
      show x * m * m * m = x * m ^ 3 by simp only [pow_three, mul_assoc], h3, mul_one]
  rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, ← hψ, hψ3]

variable {G : Type} [Group G] [Finite G]

theorem conj_mul_inv_mem_of_index_three {F M : Subgroup G} (hFe : IsElemAbelian 3 F)
    (hF27 : Nat.card F = 27) (hMF : M ≤ F) (hM9 : Nat.card M = 9) {a : G} (ha3 : a ^ 3 = 1)
    (haF : a ∈ Subgroup.normalizer (F : Set G)) (haM : ∀ m ∈ M, a * m * a⁻¹ = m) {f : G}
    (hf : f ∈ F) : (a * f * a⁻¹) * f⁻¹ ∈ M := by
  have hFc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hFe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  by_cases hfM : f ∈ M
  · rw [haM f hfM, mul_inv_cancel]
    exact M.one_mem
  have hMe : IsElemAbelian 3 M :=
    ⟨⟨⟨fun x y => Subtype.ext (hFc x (hMF x.2) y (hMF y.2))⟩⟩, fun x hx => hFe.2 x (hMF hx)⟩
  have hf3 : f ^ 3 = 1 := hFe.2 f hf
  obtain ⟨-, hcard⟩ := Item2119End3Proof.isElemAbelian_sup_zpowers hMe hf3
    (fun b hb => hFc f hf b (hMF hb))
  have hMf : M ⊔ Subgroup.zpowers f = F := Subgroup.eq_of_le_of_card_ge
    (sup_le hMF (Subgroup.zpowers_le.mpr hf)) (by rw [hcard hfM, hM9, hF27])
  have hx : a * f * a⁻¹ ∈ F := (Subgroup.mem_normalizer_iff.mp haF f).mp hf
  rw [← hMf] at hx
  have hc : ∀ y ∈ M, ∀ z ∈ Subgroup.zpowers f, y * z = z * y := fun y hy z hz =>
    hFc y (hMF hy) z ((Subgroup.zpowers_le.mpr hf) hz)
  obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute M _ hc
  have hx' : a * f * a⁻¹ ∈ ((M ⊔ Subgroup.zpowers f : Subgroup G) : Set G) := hx
  rw [hset] at hx'
  obtain ⟨m, hm, w, hw, hmw⟩ := hx'
  have hmw : m * w = a * f * a⁻¹ := hmw
  obtain ⟨j, hj, rfl⟩ := Item21LateProof.exists_pow_lt_three_of_mem_zpowers hf3 hw
  have haM' : ∀ n ∈ M, a⁻¹ * n * a = n := fun n hn => by
    calc a⁻¹ * n * a = a⁻¹ * (a * n * a⁻¹) * a := by rw [haM n hn]
      _ = n := by group
  interval_cases j
  · exfalso
    apply hfM
    rw [pow_zero, mul_one] at hmw
    have : f = a⁻¹ * m * a := by rw [hmw]; group
    rw [this, haM' m hm]
    exact hm
  · rw [pow_one] at hmw
    rw [← hmw, mul_inv_cancel_right]
    exact hm
  · exfalso
    apply hfM
    simp only [pow_two] at hmw
    have hmf : m * f = f * m := hFc m (hMF hm) f hf
    have hm3 : m ^ 3 = 1 := hMe.2 m hm
    have e2 : a * (a * f * a⁻¹) * a⁻¹ = f := by
      rw [← hmw]
      calc a * (m * (f * f)) * a⁻¹ = (a * m * a⁻¹) * (a * f * a⁻¹) * (a * f * a⁻¹) := by group
        _ = m * (m * (f * f)) * (m * (f * f)) := by rw [haM m hm, ← hmw]
        _ = m * m * m * (f * f * f) * f := by
            calc m * (m * (f * f)) * (m * (f * f)) = m * m * (f * (f * m)) * (f * f) := by group
              _ = m * m * (f * (m * f)) * (f * f) := by rw [hmf]
              _ = m * m * ((f * m) * f) * (f * f) := by group
              _ = m * m * ((m * f) * f) * (f * f) := by rw [hmf]
              _ = m * m * m * (f * f * f) * f := by group
        _ = f := by
            rw [show m * m * m = m ^ 3 by simp only [pow_three, mul_assoc],
              show f * f * f = f ^ 3 by simp only [pow_three, mul_assoc], hm3, hf3, one_mul,
              one_mul]
    have ha3' : a * a * a = 1 := by rw [← pow_three', ha3]
    have e3 : a * (a * (a * f * a⁻¹) * a⁻¹) * a⁻¹ = f := by
      calc a * (a * (a * f * a⁻¹) * a⁻¹) * a⁻¹ = (a * a * a) * f * (a * a * a)⁻¹ := by group
        _ = f := by rw [ha3']; group
    rw [e2] at e3
    rw [← hmw] at e3
    have : f = m⁻¹ := by
      have h1 : m * (f * f) * f⁻¹ = f * f⁻¹ := by rw [e3]
      rw [mul_inv_cancel, show m * (f * f) * f⁻¹ = m * f by group] at h1
      calc f = m⁻¹ * (m * f) := by group
        _ = m⁻¹ := by rw [h1, mul_one]
    rw [this]
    exact M.inv_mem hm

theorem pow_three_mul_eq_one {F M : Subgroup G} (hFe : IsElemAbelian 3 F)
    (hF27 : Nat.card F = 27) (hMF : M ≤ F) (hM9 : Nat.card M = 9) {a : G} (ha3 : a ^ 3 = 1)
    (haF : a ∈ Subgroup.normalizer (F : Set G)) (haM : ∀ m ∈ M, a * m * a⁻¹ = m) {f : G}
    (hf : f ∈ F) : (a * f) ^ 3 = 1 := by
  have hFc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hFe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hm₀ : (a * f * a⁻¹) * f⁻¹ ∈ M :=
    conj_mul_inv_mem_of_index_three hFe hF27 hMF hM9 ha3 haF haM hf
  obtain ⟨m, hm, h1⟩ : ∃ m ∈ M, a * f * a⁻¹ = m * f := ⟨_, hm₀, by group⟩
  have h2 : a * (a * f * a⁻¹) * a⁻¹ = m * m * f := by
    rw [h1]
    calc a * (m * f) * a⁻¹ = (a * m * a⁻¹) * (a * f * a⁻¹) := by group
      _ = m * m * f := by rw [haM m hm, h1, mul_assoc]
  have ha3' : a * a * a = 1 := by rw [← pow_three', ha3]
  have h3 : a * (a * (a * f * a⁻¹) * a⁻¹) * a⁻¹ = f := by
    calc a * (a * (a * f * a⁻¹) * a⁻¹) * a⁻¹ = (a * a * a) * f * (a * a * a)⁻¹ := by group
      _ = f := by rw [ha3']; group
  have key : (a * f) ^ 3 = (a * f * a⁻¹) * (a * (a * f * a⁻¹) * a⁻¹) *
      (a * (a * (a * f * a⁻¹) * a⁻¹) * a⁻¹) * (a * a * a) := by
    rw [pow_three]
    group
  rw [key, h3, h2, h1, ha3', mul_one]
  have hmf : m * f = f * m := hFc m (hMF hm) f hf
  have hm3 : m ^ 3 = 1 := hFe.2 m (hMF hm)
  have hf3 : f ^ 3 = 1 := hFe.2 f hf
  calc m * f * (m * m * f) * f = m * (f * m) * m * f * f := by group
    _ = m * (m * f) * m * f * f := by rw [hmf]
    _ = m * m * (f * m) * f * f := by group
    _ = m * m * (m * f) * f * f := by rw [hmf]
    _ = m ^ 3 * f ^ 3 := by simp only [pow_three, mul_assoc]
    _ = 1 := by rw [hm3, hf3, one_mul]

end Linear

section Fixed

variable {G : Type} [Group G] [Finite G]

theorem exists_ne_one_fixed {A K : Subgroup G} (hA : IsPGroup 3 A) (hK : IsPGroup 3 K)
    (hK1 : K ≠ ⊥) (hAK : A ≤ Subgroup.normalizer (K : Set G)) :
    ∃ y ∈ K, y ≠ 1 ∧ ∀ a ∈ A, a * y * a⁻¹ = y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ : MulDistribMulAction A K := Subgroup.conjMulDistribMulActionOfLeNormalizer A K hAK
  have hdvd : 3 ∣ Nat.card K := by
    obtain ⟨k, hk⟩ := hK.exists_card_eq
    rcases k with _ | k
    · exfalso
      apply hK1
      exact Subgroup.eq_bot_of_card_eq K (by rw [hk, pow_zero])
    · rw [hk]
      exact dvd_pow_self 3 (Nat.succ_ne_zero k)
  have h1 : (1 : K) ∈ MulAction.fixedPoints A K := fun a => smul_one a
  obtain ⟨y, hy, hy1⟩ := hA.exists_fixed_point_of_prime_dvd_card_of_fixed_point K hdvd h1
  refine ⟨y, y.2, fun h => hy1 (Subtype.ext h.symm), fun a ha => ?_⟩
  have h := congrArg Subtype.val (hy ⟨a, ha⟩)
  exact h

end Fixed

section Lift

variable {K Q : Type*} [Group K] [Finite K] [Group Q]

theorem exists_lift_of_isPGroup {φ : K →* Q} (hφ : Function.Surjective φ)
    (hker : ¬ 3 ∣ Nat.card φ.ker) {E : Subgroup Q} (hE : IsPGroup 3 E) :
    ∃ S : Subgroup K, S.map φ = E ∧ ∀ s ∈ S, φ s = 1 → s = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite Q := Finite.of_surjective φ hφ
  set P₀ := E.comap φ with hP₀
  let f : P₀ →* E := (φ.comp P₀.subtype).codRestrict E (fun x => x.2)
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨l, rfl⟩ := hφ y
    exact ⟨⟨l, hy⟩, rfl⟩
  obtain ⟨S⟩ : Nonempty (Sylow 3 P₀) := inferInstance
  have hSE : (S : Subgroup P₀).map f = ⊤ := by
    have h := ((S.mapSurjective hf).is_maximal' (hE.to_subgroup ⊤) le_top).symm
    rwa [Sylow.coe_mapSurjective] at h
  refine ⟨(S : Subgroup P₀).map P₀.subtype, ?_, ?_⟩
  · apply le_antisymm
    · rintro _ ⟨_, ⟨s, -, rfl⟩, rfl⟩
      exact s.2
    · intro y hy
      have hmem : (⟨y, hy⟩ : E) ∈ (S : Subgroup P₀).map f := by rw [hSE]; exact Subgroup.mem_top _
      obtain ⟨s, hs, hsy⟩ := hmem
      refine ⟨(s : K), ⟨s, hs, rfl⟩, ?_⟩
      exact congrArg Subtype.val hsy
  · rintro _ ⟨s, hs, rfl⟩ h1
    have hsk : (s : K) ∈ φ.ker := MonoidHom.mem_ker.mpr h1
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨s, hs⟩
    have hk' : (s : K) ^ 3 ^ k = 1 := by
      have := congrArg (fun z : (S : Subgroup P₀) => ((z : P₀) : K)) hk
      simpa using this
    have hord : orderOf (⟨s, hsk⟩ : φ.ker) ∣ 3 ^ k :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hk'))
    have hord' : orderOf (⟨s, hsk⟩ : φ.ker) ∣ Nat.card φ.ker := orderOf_dvd_natCard _
    have hcop : Nat.Coprime (3 ^ k) (Nat.card φ.ker) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hker)
    have h1' := Nat.eq_one_of_dvd_coprimes hcop hord hord'
    rw [orderOf_eq_one_iff] at h1'
    exact congrArg Subtype.val h1'

theorem exists_normalized_two {φ : K →* Q} (hφ : Function.Surjective φ)
    (hker : ¬ 3 ∣ Nat.card φ.ker) {q : K} (hq3 : q ^ 3 = 1) {R : Subgroup Q} (hR1 : R ≠ ⊥)
    (hR2 : IsPGroup 2 R) (hqR : φ q ∈ Subgroup.normalizer (R : Set Q)) :
    ∃ T : Subgroup K, T ≠ ⊥ ∧ IsPGroup 2 T ∧ q ∈ Subgroup.normalizer (T : Set K) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite Q := Finite.of_surjective φ hφ
  set W := R.comap φ with hW
  have hW3 : ¬ 3 ∣ Nat.card W := by
    intro h3
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := W) 3 h3
    have hw3 : (w : K) ^ 3 = 1 := by
      have := pow_orderOf_eq_one w
      rw [hw] at this
      simpa using congrArg Subtype.val this
    have hφw : φ (w : K) = 1 := by
      have hmem : φ (w : K) ∈ R := w.2
      obtain ⟨k, hk⟩ := hR2 ⟨_, hmem⟩
      have hk' : φ (w : K) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have h3' : φ (w : K) ^ 3 = 1 := by rw [← map_pow, hw3, map_one]
      have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
      have h1 := Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hk')
        (orderOf_dvd_of_pow_eq_one h3')
      rwa [orderOf_eq_one_iff] at h1
    have hwk : (w : K) ∈ φ.ker := hφw
    have hord : orderOf (⟨(w : K), hwk⟩ : φ.ker) = 3 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hw]
    have := orderOf_dvd_natCard (⟨(w : K), hwk⟩ : φ.ker)
    rw [hord] at this
    exact hker this
  have hW2 : 2 ∣ Nat.card W := by
    obtain ⟨r, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hR1
    obtain ⟨k, hk⟩ := hR2 r
    obtain ⟨w, hw⟩ := hφ (r : Q)
    have hwW : w ∈ W := by
      change φ w ∈ R
      rw [hw]
      exact r.2
    have hord : orderOf (r : Q) ∣ orderOf (⟨w, hwW⟩ : W) := by
      rw [← hw, Subgroup.orderOf_mk]
      exact orderOf_map_dvd φ w
    have hr2 : 2 ∣ orderOf (r : Q) := by
      have hk' : (r : Q) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk')
      rcases j with _ | j
      · exfalso
        rw [pow_zero, orderOf_eq_one_iff] at hj
        exact hr1 (Subtype.ext hj)
      · rw [hj]
        exact dvd_pow_self 2 (Nat.succ_ne_zero j)
    exact hr2.trans (hord.trans (orderOf_dvd_natCard _))
  have hqW : Subgroup.zpowers q ≤ Subgroup.normalizer (W : Set K) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_fintype fun w hw => ?_
    change φ (q * w * q⁻¹) ∈ R
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hqR _).mp hw
  have hq : IsPGroup 3 (Subgroup.zpowers q) := by
    rintro ⟨g, n, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one, pow_one]
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hq3,
      _root_.one_zpow]
  obtain ⟨S, hS⟩ := CFSG.GroupTheory.FT63ChII.exists_sylow_normalized hq hqW hW3 2
  refine ⟨(S : Subgroup W).map W.subtype, ?_, (S.isPGroup').map _, hS (Subgroup.mem_zpowers q)⟩
  intro hbot
  apply S.ne_bot_of_dvd_card hW2
  rw [eq_bot_iff]
  intro s hs
  have : (s : K) ∈ (S : Subgroup W).map W.subtype := ⟨s, hs, rfl⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact (Subgroup.mem_bot).mpr (Subtype.ext this)

end Lift

section LocalRank

variable {X : Type*} [Group X] [Finite X]

theorem exists_normalizer_two_of_localRank
    (h : CFSG.Assembly.RankThreeEven.localRank 3 X = 1) :
    ∃ x : X, x ^ 3 = 1 ∧ x ≠ 1 ∧ ∃ R : Subgroup X, R ≠ ⊥ ∧ IsPGroup 2 R ∧
      x ∈ Subgroup.normalizer (R : Set X) := by
  by_contra hne
  have hle : CFSG.Assembly.RankThreeEven.localRank 3 X ≤ 0 := by
    unfold CFSG.Assembly.RankThreeEven.localRank CFSG.Open.twoLocalPrimeRank
    refine csSup_le' ?_
    rintro k ⟨H, ⟨R, hR1, hR2, rfl⟩, rfl⟩
    unfold CFSG.Assembly.pRank
    refine csSup_le' ?_
    rintro j ⟨E, hEH, hEe, hEj⟩
    by_contra hj
    have hE1 : E ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hEj
      have h1 := Nat.pow_eq_one.mp hEj.symm
      omega
    obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE1
    exact hne ⟨(x : X), hEe.2 x x.2, fun h => hx1 (Subtype.ext h), R, hR1, hR2, hEH x.2⟩
  rw [h] at hle
  exact absurd hle (by norm_num)

end LocalRank

end CFSG.RankThree.PartTwo.Sec21.Item2119End6Proof
