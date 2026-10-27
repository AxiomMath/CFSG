module

public import CFSG.RankThree.PartTwo.KFacts.AutSzSemilinear
import CFSG.LocalAnalysis.SectionRank.SuzukiCover
import CFSG.GH74.Uniqueness.Bender.SuzukiAut
import CFSG.GroupActions.SelfCentralizingCoreOuterPrimeBound
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
import CFSG.LocalAnalysis.SectionRank.SporadicCover
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
import CFSG.Sporadic.M23.M23Group
import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.ComponentClassification.AschbacherToolkit.Bender
open CFSG.ComponentClassification.AschbacherToolkit.Bender.AutTransport
open CFSG.ComponentClassification.AschbacherToolkit.Bender.Omega
open CFSG.ComponentClassification.AschbacherToolkit.Bender.SuzukiAut
open CFSG.Open
open CFSG.BenderSuzuki CFSG.BenderSuzuki.External CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.GH74.Uniqueness.Bender
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.SectionRank
open scoped Pointwise

section

variable (m : ℕ)

local notation "F" => BinaryGaloisField (2 * m + 1)

private theorem conj_fixes_root_zero (hm : 0 < m) {r : SuzukiMatrixGroup m}
    (hr : r ∈ rootSub m) (b : F) : MulAut.conj r (root m 0 b) = root m 0 b := by
  have hz : root m 0 b ∈ sylowCenter (rootSub m) :=
    (mem_sylowCenter_rootSub m hm).mpr ⟨b, rfl⟩
  have hcomm := (mem_sylowCenter.mp hz).2 r hr
  rw [MulAut.conj_apply, hcomm, mul_assoc, mul_inv_cancel, mul_one]

private theorem theta_root_zero_eq (hm : 0 < m) {θ : MulAut (SuzukiMatrixGroup m)}
    {r : SuzukiMatrixGroup m} (hr : r ∈ rootSub m) {c : Fˣ} {τ : F ≃+* F}
    (hroot : ∀ b : F, ((MulAut.conj r)⁻¹ * θ) (root m 0 b) = root m 0 (c * τ b)) :
    ∀ b : F, θ (root m 0 b) = root m 0 (c * τ b) := by
  intro b
  have hθ : θ = MulAut.conj r * ((MulAut.conj r)⁻¹ * θ) := by group
  rw [hθ, MulAut.mul_apply, hroot b]
  exact conj_fixes_root_zero m hm hr (c * τ b)

private theorem pow_apply_root_zero {θ : MulAut (SuzukiMatrixGroup m)} {c : Fˣ}
    (hroot : ∀ b : F, θ (root m 0 b) = root m 0 (c * b)) :
    ∀ (k : ℕ) (b : F), (θ ^ k) (root m 0 b) = root m 0 (c ^ k * b) := by
  intro k
  induction k with
  | zero =>
    intro b
    simp
  | succ k ih =>
    intro b
    rw [pow_succ', MulAut.mul_apply, ih, hroot]
    congr 1
    rw [pow_succ', mul_assoc]

private theorem tau_eq_one_of_two_pow (hm : 0 < m) (θ : MulAut (SuzukiMatrixGroup m))
    (τ : F ≃+* F) (hR : ∀ r ∈ rootSub m, θ r ∈ rootSub m)
    (hτ : ∀ x : Fˣ,
      (torus m (Units.map (τ : F →* F) x))⁻¹ * θ (torus m x) ∈ rootSub m)
    (hθ : ∃ n : ℕ, orderOf θ = 2 ^ n) : τ = 1 := by
  obtain ⟨n, hn⟩ := hθ
  have hθpow : θ ^ (2 ^ n) = 1 := by rw [← hn]; exact pow_orderOf_eq_one θ
  have hτpow : τ ^ (2 ^ n) = 1 :=
    pow_eq_one_of_mul_torus_mem m hm θ τ hR hτ hθpow
  have hdvd2 : orderOf τ ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hτpow
  let K := BinaryGaloisField (2 * m + 1)
  have hKcard : Nat.card K = 2 ^ (2 * m + 1) := natCard_binaryGaloisField m
  obtain ⟨-, -, -, -, hAutcard, -⟩ :=
    @finite_field_automorphism_fixed_field_cardinality K _ 2 (2 * m + 1)
      Nat.prime_two (by omega) hKcard
  have hdvd1 : orderOf τ ∣ 2 * m + 1 := by
    have h := orderOf_dvd_natCard τ
    change orderOf τ ∣ Nat.card (K ≃+* K) at h
    rwa [hAutcard] at h
  have hodd : Odd (2 * m + 1) := ⟨m, by ring⟩
  have hcop : Nat.Coprime (2 ^ n) (2 * m + 1) :=
    (Odd.coprime_two_left hodd).pow_left n
  have hord : orderOf τ = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd2 hdvd1
  exact orderOf_eq_one_iff.mp hord

private theorem c_eq_one_of_two_pow (hm : 0 < m) (θ : MulAut (SuzukiMatrixGroup m))
    (c : Fˣ) (hroot : ∀ b : F, θ (root m 0 b) = root m 0 (c * b))
    (hθ : ∃ n : ℕ, orderOf θ = 2 ^ n) : c = 1 := by
  obtain ⟨n, hn⟩ := hθ
  have hθpow : θ ^ (2 ^ n) = 1 := by rw [← hn]; exact pow_orderOf_eq_one θ
  have h := pow_apply_root_zero m hroot (2 ^ n) (1 : F)
  rw [hθpow] at h
  simp only [MulAut.one_apply] at h
  have hval : ((c ^ (2 ^ n) : Fˣ) : F) = 1 := by
    simpa using (root_injective m h).2.symm
  have hc : c ^ (2 ^ n) = 1 := Units.ext hval
  have hdvd2 : orderOf c ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hc
  have hdvd1 : orderOf c ∣ 2 ^ (2 * m + 1) - 1 := by
    have h := orderOf_dvd_natCard c
    rwa [Nat.card_units, natCard_binaryGaloisField] at h
  have hodd : Odd (2 ^ (2 * m + 1) - 1) := by
    have heven : Even (2 ^ (2 * m + 1)) := Nat.even_pow.mpr ⟨even_two, by omega⟩
    exact Nat.Even.sub_odd Nat.one_le_two_pow heven odd_one
  have hcop : Nat.Coprime (2 ^ n) (2 ^ (2 * m + 1) - 1) :=
    (Odd.coprime_two_left hodd).pow_left n
  have hord : orderOf c = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd2 hdvd1
  exact orderOf_eq_one_iff.mp hord

theorem exists_ringEquiv_root_zero_torus (hm : 0 < m) (θ : MulAut (SuzukiMatrixGroup m))
    (hR : ∀ r ∈ rootSub m, θ r ∈ rootSub m) :
    ∃ (τ : F ≃+* F) (c : Fˣ), (∀ b : F, θ (root m 0 b) = root m 0 (c * τ b)) ∧
      ∀ x : Fˣ, (torus m (Units.map (τ : F →* F) x))⁻¹ * θ (torus m x) ∈ rootSub m := by
  obtain ⟨r, hr, hH⟩ := exists_conj_inv_mul_normalizes_torus m hm θ hR
  let α : MulAut (SuzukiMatrixGroup m) := (MulAut.conj r)⁻¹ * θ
  have hRα : ∀ a ∈ rootSub m, α a ∈ rootSub m := by
    intro a ha
    have hαa : α a = r⁻¹ * θ a * r := by
      rw [show α = (MulAut.conj r)⁻¹ * θ from rfl, MulAut.mul_apply,
        MulAut.conj_inv_apply]
    rw [hαa]
    exact (rootSub m).mul_mem
      ((rootSub m).mul_mem ((rootSub m).inv_mem hr) (hR a ha)) hr
  obtain ⟨τ, c, hrootα, htorusα⟩ := exists_ringEquiv_of_normalizes m hm α hRα hH
  refine ⟨τ, c, theta_root_zero_eq m hm hr hrootα, fun x => ?_⟩
  have hθt : θ (torus m x) = r * torus m (Units.map (τ : F →* F) x) * r⁻¹ := by
    have hθ : θ = MulAut.conj r * α := by
      rw [show α = (MulAut.conj r)⁻¹ * θ from rfl]
      group
    rw [hθ, MulAut.mul_apply, htorusα x, MulAut.conj_apply]
  rw [hθt]
  set y : SuzukiMatrixGroup m := torus m (Units.map (τ : F →* F) x) with hy
  have hyN : y⁻¹ ∈ Subgroup.normalizer ((rootSub m : Subgroup _) : Set _) := by
    apply (Subgroup.normalizer _).inv_mem
    rw [hy]
    exact torusSub_le_normalizer m (torus_mem m _)
  have hconj : y⁻¹ * r * y ∈ rootSub m := by
    simpa using (Subgroup.mem_normalizer_iff.mp hyN r).mp hr
  have hgroup : y⁻¹ * (r * y * r⁻¹) = (y⁻¹ * r * y) * r⁻¹ := by group
  rw [hgroup]
  exact (rootSub m).mul_mem hconj ((rootSub m).inv_mem hr)

theorem root_zero_fixed_of_two_pow (hm : 0 < m) (θ : MulAut (SuzukiMatrixGroup m))
    (hR : ∀ r ∈ rootSub m, θ r ∈ rootSub m) (hθ : ∃ n : ℕ, orderOf θ = 2 ^ n)
    (b : F) : θ (root m 0 b) = root m 0 b := by
  obtain ⟨τ, c, hrootθ, hτmem⟩ := exists_ringEquiv_root_zero_torus m hm θ hR
  have hτ1 : τ = 1 := tau_eq_one_of_two_pow m hm θ τ hR hτmem hθ
  have hroot1 : ∀ x : F, θ (root m 0 x) = root m 0 (c * x) := by
    intro x
    simpa [hτ1] using hrootθ x
  have hc1 : c = 1 := c_eq_one_of_two_pow m hm θ c hroot1 hθ
  simpa [hc1] using hroot1 b

theorem exists_eq_conj_of_two_pow (hm : 0 < m) (θ : MulAut (SuzukiMatrixGroup m))
    (hR : ∀ r ∈ rootSub m, θ r ∈ rootSub m) (hθ : ∃ n : ℕ, orderOf θ = 2 ^ n) :
    ∃ s ∈ rootSub m, θ = MulAut.conj s := by
  have hfix : ∀ z ∈ rootCenter (rootSub m), θ z = z := by
    intro z hz
    have hz' : z ∈ sylowCenter (rootSub m) := hz
    obtain ⟨b, rfl⟩ := (mem_sylowCenter_rootSub m hm).mp hz'
    exact root_zero_fixed_of_two_pow m hm θ hR hθ b
  exact centralizingInner_rootSub m hm θ hR hfix

theorem exists_eq_map_conj_rootSub (hm : 0 < m) (T : Sylow 2 (SuzukiMatrixGroup m)) :
    ∃ g : SuzukiMatrixGroup m,
      (T : Subgroup (SuzukiMatrixGroup m)) = (rootSub m).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨R, hR⟩ := exists_sylow_eq_rootSub m hm
  haveI : MulAction.IsPretransitive (SuzukiMatrixGroup m)
      (Sylow 2 (SuzukiMatrixGroup m)) := Sylow.isPretransitive_of_finite
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := SuzukiMatrixGroup m) R T
  refine ⟨g, ?_⟩
  rw [← congrArg (fun P : Sylow 2 (SuzukiMatrixGroup m) =>
    (P : Subgroup (SuzukiMatrixGroup m))) hg, Sylow.coe_subgroup_smul, hR,
    CFSG.GroupActions.mulAut_smul_subgroup_eq_map]

theorem exists_eq_conj_of_two_pow_sylow (hm : 0 < m)
    (T : Sylow 2 (SuzukiMatrixGroup m)) (θ : MulAut (SuzukiMatrixGroup m))
    (hθ : ∃ n : ℕ, orderOf θ = 2 ^ n)
    (hT : ∀ x ∈ (T : Subgroup (SuzukiMatrixGroup m)),
      θ x ∈ (T : Subgroup (SuzukiMatrixGroup m))) :
    ∃ s ∈ (T : Subgroup (SuzukiMatrixGroup m)), θ = MulAut.conj s := by
  obtain ⟨g, hTcoe⟩ := exists_eq_map_conj_rootSub m hm T
  let φ : MulAut (SuzukiMatrixGroup m) := MulAut.congr ((MulAut.conj g)⁻¹) θ
  have hRφ : ∀ r ∈ rootSub m, φ r ∈ rootSub m := by
    intro r hr
    have hgr : (MulAut.conj g) r ∈ (T : Subgroup (SuzukiMatrixGroup m)) := by
      rw [hTcoe]
      exact Subgroup.mem_map.mpr ⟨r, hr, rfl⟩
    have hθgr : θ ((MulAut.conj g) r) ∈ (T : Subgroup (SuzukiMatrixGroup m)) :=
      hT _ hgr
    have hθgr' : θ ((MulAut.conj g) r) ∈
        (rootSub m).map (MulAut.conj g).toMonoidHom := by
      rwa [← hTcoe]
    have hφr : φ r = (MulAut.conj g).symm (θ ((MulAut.conj g) r)) := by
      simp [φ, MulAut.congr_apply]
    rw [hφr]
    exact (Subgroup.mem_map_equiv (f := MulAut.conj g) (K := rootSub m)).mp hθgr'
  have hφord : ∃ n : ℕ, orderOf φ = 2 ^ n := by
    obtain ⟨n, hn⟩ := hθ
    refine ⟨n, ?_⟩
    change orderOf (MulAut.congr ((MulAut.conj g)⁻¹) θ) = 2 ^ n
    rw [MulEquiv.orderOf_eq, hn]
  obtain ⟨s, hs, hφs⟩ := exists_eq_conj_of_two_pow m hm φ hRφ hφord
  refine ⟨MulAut.conj g s, ?_, ?_⟩
  · rw [hTcoe]
    exact Subgroup.mem_map.mpr ⟨s, hs, rfl⟩
  · calc θ = (MulAut.congr ((MulAut.conj g)⁻¹)).symm φ := by
          rw [show φ = MulAut.congr ((MulAut.conj g)⁻¹) θ from rfl]
          exact (MulEquiv.symm_apply_apply _ _).symm
      _ = (MulAut.congr ((MulAut.conj g)⁻¹)).symm (MulAut.conj s) := by rw [hφs]
      _ = MulAut.conj ((MulAut.conj g) s) := by
          ext x
          simp [MulAut.congr_symm_apply, MulAut.conj_apply, map_mul, map_inv]

end

end CFSG.RankThree.PartTwo.KFacts

end
