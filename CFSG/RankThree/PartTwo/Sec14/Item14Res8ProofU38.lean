module

public import CFSG.RankThree.PartTwo.Sec14.Item14Res6ProofGenL3
public import CFSG.RankThree.PartTwo.Sec14.Item14Res8ProofTypeOne
public import CFSG.RankThree.PartTwo.Sec14.Item14Res8ProofHessModel
public import CFSG.RankThree.PartTwo.Sec17.Item17Res7ProofL3AutUni
import CFSG.CharacterTheory.Semidihedral.FixedFieldData
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartOne.S9.Vanishing.Basic
import CFSG.RankThree.PartTwo.Sec17.Item17Res7ProofL3Defs
import CFSG.RankThree.PartTwo.Sec19.Step1915WProofLie3K
import CFSG.RankThree.PartTwo.Sec19.Item19ResProofAutCent
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
  CFSG.RankThree.LocalRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec17.Proof17Res7
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.Assembly.RankThreeEven (projImage)
open Res8Hess

namespace Res8U38

variable {K : Type} [Field K]

theorem pow_three_eq_one_of_fix_tau (hK : Nat.card K = 2 ^ 6) {τ : K} (hτ : τ ^ 3 = 1)
    (hτ1 : τ ≠ 1) (σ : K ≃+* K) (hσ : σ τ = τ) : σ ^ 3 = 1 := by
  obtain ⟨σ₀, hσ₀, hord, htop, -⟩ :=
    CFSG.Semidihedral.FixedFieldData.finite_field_automorphism_fixed_field_cardinality 2 6
      Nat.prime_two (by norm_num) K hK
  have hσ6 : σ₀ ^ 6 = 1 := by rw [← hord, pow_orderOf_eq_one]
  have hpow : ∀ m : ℕ, ∀ x : K, (σ₀ ^ m) x = x ^ (2 ^ m) := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [pow_succ, RingAut.mul_apply, hσ₀, ih, ← pow_mul, ← pow_succ']
  have hσmem : σ ∈ Subgroup.zpowers σ₀ := by
    rw [← htop]
    exact Subgroup.mem_top σ
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hσmem
  set m := (k % 6).toNat with hm
  have hk6 : σ₀ ^ k = σ₀ ^ m := by
    have hmk : ((m : ℕ) : ℤ) = k % 6 := Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))
    have hkdecomp : k = k % 6 + 6 * (k / 6) := (Int.emod_add_mul_ediv k 6).symm
    rw [← zpow_natCast, hmk]
    conv_lhs => rw [hkdecomp]
    rw [_root_.zpow_add, _root_.zpow_mul, show (6 : ℤ) = ((6 : ℕ) : ℤ) by rfl, zpow_natCast, hσ6,
      _root_.one_zpow, mul_one]
  have hm6 : m < 6 := by
    have h1 : k % 6 < 6 := Int.emod_lt_of_pos k (by norm_num)
    omega
  rw [hk6] at hσ ⊢
  rw [hpow] at hσ
  have hτ2 : τ ^ 2 ≠ τ := by
    intro h
    apply hτ1
    have hτ0 : τ ≠ 0 := by
      rintro rfl
      simp at hτ
    have : τ * τ = τ * 1 := by rw [← sq, h, mul_one]
    exact mul_left_cancel₀ hτ0 this
  have hτpow : ∀ j : ℕ, τ ^ (3 * j + 2) = τ ^ 2 := fun j => by
    rw [pow_add, pow_mul, hτ, one_pow, one_mul]
  interval_cases m
  · simp
  · exact absurd hσ (by rw [show (2 : ℕ) ^ 1 = 3 * 0 + 2 by rfl, hτpow]; exact hτ2)
  · rw [← pow_mul, show 2 * 3 = 6 by rfl, hσ6]
  · exact absurd hσ (by rw [show (2 : ℕ) ^ 3 = 3 * 2 + 2 by rfl, hτpow]; exact hτ2)
  · rw [← pow_mul, show 4 * 3 = 6 * 2 by rfl, pow_mul, hσ6, one_pow]
  · exact absurd hσ (by rw [show (2 : ℕ) ^ 5 = 3 * 10 + 2 by rfl, hτpow]; exact hτ2)

theorem eq_or_eq_sq_of_ringEquiv {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (σ : K ≃+* K) :
    σ τ = τ ∨ σ τ = τ ^ 2 := by
  have hs : τ ^ 2 + τ + 1 = 0 := by
    have hne : τ - 1 ≠ 0 := sub_ne_zero.mpr hτ1
    have : (τ - 1) * (τ ^ 2 + τ + 1) = 0 := by linear_combination hτ
    exact (mul_eq_zero.mp this).resolve_left hne
  have hσs : σ τ ^ 2 + σ τ + 1 = 0 := by
    have := congrArg σ hs
    simpa using this
  have key : (σ τ - τ) * (σ τ - τ ^ 2) = 0 := by linear_combination hσs - (σ τ) * hs + hτ
  rcases mul_eq_zero.mp key with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

variable (h : UnitaryFieldData 2 3 K) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)

include hτ1 in
theorem pow_three_eq_one_of_fix_psu {dU cU : unitarySU 2 3 K 3}
    (hdU : (dU : GL (Fin 3) K) = diagTau hτ) (hcU : (cU : GL (Fin 3) K) = cycThree)
    (hdc : (dU : unitaryPSU h 3) * (cU : unitaryPSU h 3) =
      (cU : unitaryPSU h 3) * (dU : unitaryPSU h 3))
    (β : MulAut (unitaryPSU h 3))
    (hd : β (dU : unitaryPSU h 3) = (dU : unitaryPSU h 3))
    (hc : β (cU : unitaryPSU h 3) = (cU : unitaryPSU h 3)) : β ^ 3 = 1 := by
  have hq2 : 2 < 2 ^ 3 := by norm_num
  obtain ⟨A, σ, hβ⟩ := exists_psuConj_mul_psuField hq2 β
  have hcard : Nat.card K = 2 ^ 6 := by rw [h.card]
  have hσc : (glAut σ (cU : GL (Fin 3) K) : GL (Fin 3) K) = cycThree := by
    apply Units.ext
    rw [coe_glAut, hcU, coe_cycThree]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rcases eq_or_eq_sq_of_ringEquiv hτ hτ1 σ with hστ | hστ
  ·
    have hσd : (glAut σ (dU : GL (Fin 3) K) : GL (Fin 3) K) = diagTau hτ := by
      apply Units.ext
      rw [coe_glAut, hdU, coe_diagTau]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hστ]
    have hFd : psuField h σ (dU : unitaryPSU h 3) = (dU : unitaryPSU h 3) := by
      rw [psuField_mk]
      congr 1
      exact Subtype.ext (by rw [coe_suField, hσd, hdU])
    have hFc : psuField h σ (cU : unitaryPSU h 3) = (cU : unitaryPSU h 3) := by
      rw [psuField_mk]
      congr 1
      exact Subtype.ext (by rw [coe_suField, hσc, hcU])
    have hd' := hd
    have hc' := hc
    rw [hβ, MulAut.mul_apply, hFd, psuConj_mk] at hd'
    rw [hβ, MulAut.mul_apply, hFc, psuConj_mk] at hc'
    obtain ⟨u, hu⟩ := exists_scalar_of_unitaryProj_eq hd'
    obtain ⟨v, hv⟩ := exists_scalar_of_unitaryProj_eq hc'
    rw [coe_suConj, hdU] at hu
    rw [coe_suConj, hcU] at hv
    obtain ⟨s, m, j, hA⟩ := exists_eq_of_conj_hessian hτ hτ1 hu hv
    set hb : unitaryPSU h 3 := (dU : unitaryPSU h 3) ^ m * (cU : unitaryPSU h 3) ^ j with hhb
    have hCA : psuConj h A = MulAut.conj hb := by
      ext x
      induction x using QuotientGroup.induction_on with
      | H g =>
        rw [psuConj_mk, MulAut.conj_apply]
        have e : hb = ((dU ^ m * cU ^ j : unitarySU 2 3 K 3) : unitaryPSU h 3) := by
          rw [hhb, QuotientGroup.mk_mul, QuotientGroup.mk_pow, QuotientGroup.mk_pow]
        rw [e, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        apply Subtype.ext
        have hA' : (A : GL (Fin 3) K) =
            GeneralLinearGroup.scalar (Fin 3) s * (diagTau hτ ^ m * cycThree ^ j) := by
          rw [hA, mul_assoc]
        rw [coe_suConj]
        simp only [Subgroup.coe_inv, hA', scalar_mul_conj, Subgroup.coe_mul, Subgroup.coe_pow,
          hdU, hcU]
    have hFh : psuField h σ hb = hb := by
      rw [hhb, map_mul, map_pow, map_pow, hFd, hFc]
    have hFC : psuField h σ * MulAut.conj hb = MulAut.conj hb * psuField h σ := by
      have := conj_apply_eq (psuField h σ) hb
      rw [hFh] at this
      calc psuField h σ * MulAut.conj hb =
          psuField h σ * MulAut.conj hb * (psuField h σ)⁻¹ * psuField h σ := by group
        _ = MulAut.conj hb * psuField h σ := by rw [← this]
    have hd3 : (dU : unitaryPSU h 3) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow]
      have : dU ^ 3 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, hdU, diagTau_pow_three hτ, OneMemClass.coe_one])
      rw [this, QuotientGroup.mk_one]
    have hc3 : (cU : unitaryPSU h 3) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow]
      have : cU ^ 3 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, hcU, cycThree_pow_three, OneMemClass.coe_one])
      rw [this, QuotientGroup.mk_one]
    have hhb3 : hb ^ 3 = 1 := by
      rw [hhb, ((Commute.pow_pow hdc m j)).mul_pow, ← pow_mul, ← pow_mul, mul_comm m,
        mul_comm j, pow_mul, pow_mul, hd3, hc3, one_pow, one_pow, one_mul]
    have hσ3 : σ ^ 3 = 1 := pow_three_eq_one_of_fix_tau hcard hτ hτ1 σ hστ
    rw [hβ, hCA, (Commute.mul_pow (hFC.symm : Commute (MulAut.conj hb) (psuField h σ))),
      ← map_pow, ← map_pow, hhb3, hσ3, map_one, map_one, mul_one]
  ·
    exfalso
    have hσd : (glAut σ (dU : GL (Fin 3) K) : GL (Fin 3) K) = (diagTau hτ)⁻¹ := by
      apply Units.ext
      rw [coe_glAut, hdU, coe_diagTau, coe_diagTau_inv]
      have h2 : σ (τ ^ 2) = τ := by
        rw [map_pow, hστ, ← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_add, hτ, one_mul, pow_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hστ, h2]
    have hd' := hd
    have hc' := hc
    rw [hβ, MulAut.mul_apply, psuField_mk, psuConj_mk] at hd' hc'
    obtain ⟨u, hu⟩ := exists_scalar_of_unitaryProj_eq hd'
    obtain ⟨v, hv⟩ := exists_scalar_of_unitaryProj_eq hc'
    rw [coe_suConj, coe_suField, hσd, hdU] at hu
    rw [coe_suConj, coe_suField, hσc, hcU] at hv
    exact false_of_conj_inv_hessian hτ hτ1 hu hv

noncomputable def dSU : unitarySU 2 3 K 3 :=
  ⟨diagTau hτ, diagTau_mem_slPi (π := false) (fun _ => h) (fun _ => by
    change 2 ^ 3 % 3 = 2
    norm_num) hτ⟩

noncomputable def cSU : unitarySU 2 3 K 3 :=
  ⟨cycThree, cycThree_mem_slPi (π := false) (fun _ => h)⟩

include h hτ1 in
theorem eq_one_of_fix {dM cM : projImage (slPi false 3 (2 ^ 3) K)}
    (hdM : (dM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (diagTau hτ))
    (hcM : (cM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (cycThree : GL (Fin 3) K))
    (hdc : dM * cM = cM * dM) (β : MulAut (projImage (slPi false 3 (2 ^ 3) K)))
    (hd : β dM = dM) (hc : β cM = cM) {n : ℕ} (hn : ¬ 3 ∣ n) (hβn : β ^ n = 1) : β = 1 := by
  set ε := unitaryModelEquiv h with hε
  have hεd : ε (dSU h hτ : unitaryPSU h 3) = dM :=
    Subtype.ext ((coe_unitaryModelEquiv_mk h _).trans hdM.symm)
  have hεc : ε (cSU h : unitaryPSU h 3) = cM :=
    Subtype.ext ((coe_unitaryModelEquiv_mk h _).trans hcM.symm)
  set β' := MulAut.congr ε.symm β with hβ'
  have hβ'app : ∀ x, β' x = ε.symm (β (ε x)) := fun x => rfl
  have hd' : β' (dSU h hτ : unitaryPSU h 3) = (dSU h hτ : unitaryPSU h 3) := by
    rw [hβ'app, hεd, hd, ← hεd, MulEquiv.symm_apply_apply]
  have hc' : β' (cSU h : unitaryPSU h 3) = (cSU h : unitaryPSU h 3) := by
    rw [hβ'app, hεc, hc, ← hεc, MulEquiv.symm_apply_apply]
  have hdc' : (dSU h hτ : unitaryPSU h 3) * (cSU h : unitaryPSU h 3) =
      (cSU h : unitaryPSU h 3) * (dSU h hτ : unitaryPSU h 3) := by
    apply ε.injective
    rw [map_mul, map_mul, hεd, hεc, hdc]
  have h3 := pow_three_eq_one_of_fix_psu h hτ hτ1 (dU := dSU h hτ) (cU := cSU h) rfl rfl hdc' β'
    hd' hc'
  have hn' : β' ^ n = 1 := by rw [hβ', ← map_pow, hβn, map_one]
  have h1 : β' = 1 := by
    have ho3 : orderOf β' ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    have hon : orderOf β' ∣ n := orderOf_dvd_of_pow_eq_one hn'
    have hcop : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hn
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop ho3 hon)
  apply (MulAut.congr ε.symm).injective
  rw [← hβ', h1, map_one]

omit h hτ hτ1 in
theorem eq_one_of_fix_centralizer (h : UnitaryFieldData 2 3 K)
    {x : projImage (slPi false 3 (2 ^ 3) K)} (hx1 : x ≠ 1) (hx : HasCubeOneLift x)
    (β : MulAut (projImage (slPi false 3 (2 ^ 3) K)))
    (hβ : ∀ y ∈ Subgroup.centralizer ({x} : Set (projImage (slPi false 3 (2 ^ 3) K))), β y = y)
    {n : ℕ} (hn : ¬ 3 ∣ n) (hβn : β ^ n = 1) : β = 1 := by
  have hK : PiField false 2 3 K := ⟨Nat.prime_two, by norm_num, by
    rw [h.card]
    change 2 ^ (2 * 3) = (2 ^ 3) ^ 2
    rw [← pow_mul]⟩
  have hq : ModThree false (2 ^ 3) := by
    change 2 ^ 3 % 3 = 2
    norm_num
  have hπ : false = false → UnitaryFieldData 2 3 K := fun _ => h
  have hq' : false = false → ModThree false (2 ^ 3) := fun _ => hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨dM, cM, hdM, hcM, hdc, -, -, -⟩ := Sec19.Step1915WProof.exists_heisPair hK hq hτ hτ1
  obtain ⟨y, hy, hxy, hy3⟩ := hx
  have hyZ : y ∉ zPi false 3 (2 ^ 3) K := by
    intro hz
    apply hx1
    apply Subtype.ext
    rw [← hxy, OneMemClass.coe_one, ProjGenLinGroup.mk_eq_one,
      GeneralLinearGroup.center_eq_range_scalar]
    exact (Subgroup.mem_inf.mp ((zPi_eq hπ hq' hτ hτ1) ▸ hz)).2
  have hyo : orderOf y = 3 := by
    refine orderOf_eq_prime hy3 fun h1 => hyZ ?_
    rw [h1]
    exact one_mem _
  obtain ⟨g, hg, hgy⟩ := rank3II_4_10_three hK hq hτ hτ1 hy hyZ hyo
  set γ := conjM' hπ hg with hγ
  have hγd : γ dM = x := by
    apply Subtype.ext
    rw [coe_conjM', hdM, ← map_inv, ← map_mul, ← map_mul, ← hxy, ← hgy]
    congr 1
    group
  have hγc : γ cM ∈ Subgroup.centralizer ({x} : Set (projImage (slPi false 3 (2 ^ 3) K))) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hγd, ← map_mul, ← map_mul, hdc]
  set β'' := γ⁻¹ * β * γ with hβ''
  have hd'' : β'' dM = dM := by
    rw [hβ'', MulAut.mul_apply, MulAut.mul_apply, hγd,
      hβ x (Subgroup.mem_centralizer_singleton_iff.mpr rfl), ← hγd, MulAut.inv_apply,
      MulEquiv.symm_apply_apply]
  have hc'' : β'' cM = cM := by
    rw [hβ'', MulAut.mul_apply, MulAut.mul_apply, hβ _ hγc, MulAut.inv_apply,
      MulEquiv.symm_apply_apply]
  have hn'' : β'' ^ n = 1 := by
    rw [hβ'', show γ⁻¹ * β * γ = γ⁻¹ * β * γ⁻¹⁻¹ by rw [inv_inv], ← MulAut.conj_apply,
      ← map_pow, hβn, map_one]
  have h1 := eq_one_of_fix h hτ hτ1 hdM hcM hdc β'' hd'' hc'' hn hn''
  calc β = γ * β'' * γ⁻¹ := by rw [hβ'']; group
    _ = 1 := by rw [h1]; group

end Res8U38

open Res8U38 in
theorem ks142U38Alpha : KS142U38Alpha := by
  intro X _ _ hiso E hEe hE9 htr Y hInn
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨π, K, _, hK, hq, ⟨ψ⟩⟩ := Sec13.exists_projImage_model (by norm_num : 1 ≤ 3) hiso
  have hπ : π = false := by
    cases π
    · rfl
    · exfalso
      change 2 ^ 3 % 3 = 1 at hq
      norm_num at hq
  subst hπ
  have h := hK.unitary
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  have hZ : Subgroup.center X = ⊥ := by
    rcases hiso with ⟨hq', -⟩ | ⟨hq', ⟨φ⟩⟩
    · norm_num at hq'
    · exact Sec19.Item19ResProof.center_eq_bot_of_mulEquiv φ
        (Sec13.isPerfect_center_projSU 2 3 (by norm_num) hq' (by norm_num)).2
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) :=
    Sec17.Proof17Res7.conj_injective_of_center hZ
  have hEψ : CFSG.Assembly.IsElemAbelian 3 (E.map ψ.toMonoidHom) :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 ψ.toMonoidHom E hEe
  have hEψ9 : Nat.card (E.map ψ.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective ψ.injective, hE9]
  have htrψ : ∀ y₀ ∈ E.map ψ.toMonoidHom, y₀ ≠ 1 → ∀ y₁ ∈ E.map ψ.toMonoidHom, y₁ ≠ 1 →
      ∃ w ∈ Subgroup.normalizer ((E.map ψ.toMonoidHom : Subgroup _) : Set _),
        w * y₀ * w⁻¹ = y₁ := by
    rintro _ ⟨y₀, hy₀, rfl⟩ hy₀1 _ ⟨y₁, hy₁, rfl⟩ hy₁1
    have hy₀1' : y₀ ≠ 1 := fun h => hy₀1 (by rw [h, map_one])
    have hy₁1' : y₁ ≠ 1 := fun h => hy₁1 (by rw [h, map_one])
    obtain ⟨w, hw, hwy⟩ := htr y₀ hy₀ hy₀1' y₁ hy₁ hy₁1'
    refine ⟨ψ w, ?_, ?_⟩
    · rw [← Subgroup.map_equiv_normalizer_eq]
      exact ⟨w, hw, rfl⟩
    · change ψ w * ψ y₀ * (ψ w)⁻¹ = ψ y₁
      rw [← map_inv, ← map_mul, ← map_mul, hwy]
  have hcube := hasCubeOneLift_of_transitive hK hEψ hEψ9 htrψ
  have hC3 : ∀ e ∈ E, e ≠ 1 → IsPGroup 3 (Subgroup.centralizer ({e} : Set X)) := by
    intro e he he1
    have hψe1 : ψ e ≠ 1 := fun h => he1 (ψ.injective (by rw [h, map_one]))
    have hdvd := card_centralizer_dvd_of_hasCubeOneLift hK hq hψe1 (hcube _ ⟨e, he, rfl⟩ hψe1)
    have hq9 : qSubPi false (2 ^ 3) = 9 := rfl
    rw [hq9] at hdvd
    have hcard : Nat.card (Subgroup.centralizer ({e} : Set X)) =
        Nat.card (Subgroup.centralizer ({ψ e} : Set (projImage (slPi false 3 (2 ^ 3) K)))) := by
      rw [← CFSG.RankThree.PartTwo.map_centralizer_singleton ψ e,
        Subgroup.card_map_of_injective ψ.injective]
    rw [← hcard] at hdvd
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
      (hdvd.trans (by norm_num : 3 * 9 ^ 2 ∣ 3 ^ 5))
    exact IsPGroup.of_card hk
  have hrig : ∀ e ∈ E, e ≠ 1 → ∀ ρ : MulAut X,
      (∀ x ∈ Subgroup.centralizer ({e} : Set X), ρ x = x) → ∀ n : ℕ, ¬ 3 ∣ n → ρ ^ n = 1 →
        ρ = 1 := by
    intro e he he1 ρ hρ n hn hρn
    have hψe1 : ψ e ≠ 1 := fun h => he1 (ψ.injective (by rw [h, map_one]))
    set β := MulAut.congr ψ ρ with hβ
    have hβapp : ∀ m, β m = ψ (ρ (ψ.symm m)) := fun m => rfl
    have hβfix : ∀ y ∈ Subgroup.centralizer
        ({ψ e} : Set (projImage (slPi false 3 (2 ^ 3) K))), β y = y := by
      intro y hy
      rw [hβapp, hρ (ψ.symm y), MulEquiv.apply_symm_apply]
      rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
      apply ψ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hy]
    have hβn : β ^ n = 1 := by rw [hβ, ← map_pow, hρn, map_one]
    have h1 := eq_one_of_fix_centralizer h hψe1 (hcube _ ⟨e, he, rfl⟩ hψe1) β hβfix hn hβn
    apply (MulAut.congr ψ).injective
    rw [← hβ, h1, map_one]
  set B := (E.map (MulAut.conj : X →* MulAut X)).subgroupOf Y with hB
  have hθ : ∀ b ∈ B, b ≠ 1 →
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set Y)) = ⊥ := by
    intro b hb hb1
    obtain ⟨e, he, hbe⟩ := Subgroup.mem_subgroupOf.mp hb
    have he1 : e ≠ 1 := by
      rintro rfl
      apply hb1
      apply Subtype.ext
      rw [← hbe, map_one]
      rfl
    set C := Subgroup.centralizer ({b} : Set Y) with hC
    set R := inSubgroup (aschbacherSolvableCore 3) C with hR
    have hR3 := not_dvd_card_inSubgroup_theta C
    have hRC : R ≤ C := inSubgroup_theta_le C
    have hRN : C ≤ Subgroup.normalizer (R : Set Y) :=
      CFSG.RankThree.PartOne.Vanish.le_normalizer_inSubgroup_aschbacherSolvableCore 3 C
    rw [eq_bot_iff]
    intro r hr
    rw [Subgroup.mem_bot]
    set ρ : MulAut X := (r : MulAut X) with hρ
    have hρe : ρ e = e := by
      have hrb : r * b = b * r := Subgroup.mem_centralizer_singleton_iff.mp (hRC hr)
      have h1 : MulAut.conj (ρ e) = MulAut.conj e := by
        rw [Sec17.Proof17Res7.conj_apply_eq]
        have := congrArg (fun z : Y => (z : MulAut X)) hrb
        simp only [Subgroup.coe_mul] at this
        rw [← hbe, ← hρ] at this
        calc ρ * MulAut.conj e * ρ⁻¹ = MulAut.conj e * ρ * ρ⁻¹ := by rw [this]
          _ = MulAut.conj e := by group
      exact hinj h1
    have hρC : ∀ x ∈ Subgroup.centralizer ({e} : Set X), ρ x = x := by
      intro x hx
      have hxe : x * e = e * x := Subgroup.mem_centralizer_singleton_iff.mp hx
      set cx : Y := ⟨MulAut.conj x, hInn ⟨x, rfl⟩⟩ with hcx
      have hcxC : cx ∈ C := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply Subtype.ext
        simp only [Subgroup.coe_mul, hcx]
        rw [← hbe, ← map_mul, ← map_mul, hxe]
      have hk : r * cx * r⁻¹ * cx⁻¹ ∈ R := by
        have h1 : cx * r⁻¹ * cx⁻¹ ∈ R :=
          (Subgroup.mem_normalizer_iff.mp (hRN hcxC) r⁻¹).mp (inv_mem hr)
        have : r * cx * r⁻¹ * cx⁻¹ = r * (cx * r⁻¹ * cx⁻¹) := by group
        rw [this]
        exact mul_mem hr h1
      have hkval : ((r * cx * r⁻¹ * cx⁻¹ : Y) : MulAut X) = MulAut.conj (ρ x * x⁻¹) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hcx]
        rw [map_mul, map_inv, Sec17.Proof17Res7.conj_apply_eq]
      have hρxC : ρ x * x⁻¹ ∈ Subgroup.centralizer ({e} : Set X) := by
        refine mul_mem ?_ (inv_mem hx)
        rw [Subgroup.mem_centralizer_singleton_iff]
        rw [← hρe, ← map_mul, ← map_mul, hxe]
      obtain ⟨j, hj⟩ := (hC3 e he he1) ⟨_, hρxC⟩
      have hj' : (r * cx * r⁻¹ * cx⁻¹) ^ 3 ^ j = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, hkval, ← map_pow, OneMemClass.coe_one]
        have := congrArg Subtype.val hj
        simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this
        rw [this, map_one]
      have hk1 : r * cx * r⁻¹ * cx⁻¹ = 1 := by
        have h1 : orderOf (r * cx * r⁻¹ * cx⁻¹) ∣ 3 ^ j := orderOf_dvd_of_pow_eq_one hj'
        have h2 := coprime_orderOf_of_mem hR3 hk
        have h3 : Nat.Coprime (3 ^ j) (orderOf (r * cx * r⁻¹ * cx⁻¹)) :=
          Nat.Coprime.pow_left j h2.symm.symm
        exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes h3 h1 dvd_rfl)
      have h2 : MulAut.conj (ρ x * x⁻¹) = 1 := by
        rw [← hkval, hk1]
        rfl
      have h3 : ρ x * x⁻¹ = 1 := hinj (h2.trans (map_one _).symm)
      exact mul_inv_eq_one.mp h3
    have hρn : ρ ^ orderOf r = 1 := by
      rw [hρ, ← Subgroup.coe_pow, pow_orderOf_eq_one]
      rfl
    have hr3 : ¬ 3 ∣ orderOf r := fun h3 =>
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_orderOf_of_mem hR3 hr) h3
    have hρ1 := hrig e he he1 ρ hρC (orderOf r) hr3 hρn
    exact Subtype.ext hρ1
  obtain ⟨⟨e₀, he₀⟩, he₀1⟩ : ∃ x : E, x ≠ 1 := by
    have : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by rw [hE9]; norm_num)
    exact exists_ne 1
  have he₀1' : e₀ ≠ 1 := fun h => he₀1 (Subtype.ext h)
  have hb₀ : (⟨MulAut.conj e₀, hInn ⟨e₀, rfl⟩⟩ : Y) ∈ B :=
    Subgroup.mem_subgroupOf.mpr ⟨e₀, he₀, rfl⟩
  have hb₀1 : (⟨MulAut.conj e₀, hInn ⟨e₀, rfl⟩⟩ : Y) ≠ 1 := by
    intro h
    apply he₀1'
    apply hinj
    rw [map_one]
    exact congrArg Subtype.val h
  rw [thetaAlpha, eq_bot_iff]
  refine sup_le ?_ ?_
  · refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_
    rw [hθ b hb hb1, Subgroup.commutator_bot_left]
  · exact (iInf_le_of_le _ (iInf_le_of_le hb₀ (iInf_le_of_le hb₀1 (hθ _ hb₀ hb₀1).le)))

end CFSG.RankThree.PartTwo.Sec14
