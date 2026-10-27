module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitOrthogonalAction
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate3952
import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410RT
import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410RS
import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinStd
import CFSG.LieType.Universal.Spin.Action
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FundamentalOverModel
import CFSG.GH74.Generic.S1.LinFull
import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Outer
import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma412
import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46d
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAllInvolutionFourGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LieType.Universal.Spin
open scoped MatrixGroups

section Generic

private theorem exists_mulEquiv_map_apply {G X H : Type} [Group G] [Group X] [Group H]
    (ψ : G →* X) {R : Subgroup G} (hinj : R ⊓ ψ.ker = ⊥) (e : ↥R ≃* H) :
    ∃ eR : ↥(R.map ψ) ≃* H, ∀ r : R, eR ⟨ψ r, Subgroup.mem_map_of_mem ψ r.2⟩ = e r := by
  have hinj' : Function.Injective (ψ.comp R.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    apply Subtype.ext
    have hmem : (x : G) ∈ R ⊓ ψ.ker := ⟨x.2, hx⟩
    rw [hinj, Subgroup.mem_bot] at hmem
    exact hmem
  have hrange : (ψ.comp R.subtype).range = R.map ψ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let e1 : ↥R ≃* ↥(ψ.comp R.subtype).range := MonoidHom.ofInjective hinj'
  let e2 : ↥(ψ.comp R.subtype).range ≃* ↥(R.map ψ) := MulEquiv.subgroupCongr hrange
  let eR : ↥(R.map ψ) ≃* H := (e1.trans e2).symm.trans e
  refine ⟨eR, fun r => ?_⟩
  have h5 : (e1.trans e2) r = ⟨ψ r, Subgroup.mem_map_of_mem ψ r.2⟩ := Subtype.ext rfl
  have h4 : (e1.trans e2).symm ⟨ψ r, Subgroup.mem_map_of_mem ψ r.2⟩ = r := by
    rw [← h5, MulEquiv.symm_apply_apply]
  simp only [eR, MulEquiv.trans_apply]
  rw [h4]

theorem nonempty_mulEquiv_map_of_inf_ker_eq_bot {G X H : Type} [Group G] [Group X] [Group H]
    (ψ : G →* X) {R : Subgroup G} (hinj : R ⊓ ψ.ker = ⊥) (e : ↥R ≃* H) :
    Nonempty (↥(R.map ψ) ≃* H) := by
  obtain ⟨eR, -⟩ := exists_mulEquiv_map_apply ψ hinj e
  exact ⟨eR⟩

theorem exists_sylow_of_isSylowOf_map {G X H : Type} [Group G] [Group X] [Group H] [Finite G]
    (ψ : G →* X) {R : Subgroup G} (hinj : R ⊓ ψ.ker = ⊥) (e : ↥R ≃* H) {P : Subgroup X}
    (hP : CFSG.ABGLocalTools.IsSylowOf 2 (P ⊓ R.map ψ) (R.map ψ)) :
    ∃ Q' : Sylow 2 H, ∀ A ∈ (Q' : Subgroup H), ∃ x : R, ψ x ∈ P ∧ e x = A := by
  obtain ⟨eR, heR⟩ := exists_mulEquiv_map_apply ψ hinj e
  obtain ⟨Q, hQ⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_sylow_eq_subgroupOf hP
  have : Finite ↥(R.map ψ) := Finite.of_surjective
    (fun x : R => (⟨ψ x, Subgroup.mem_map_of_mem ψ x.2⟩ : ↥(R.map ψ)))
    (by
      rintro ⟨y, hy⟩
      rw [Subgroup.mem_map] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨⟨x, hx⟩, rfl⟩)
  let Q' : Sylow 2 H := Sylow.mapSurjective (f := eR.toMonoidHom) eR.surjective Q
  refine ⟨Q', ?_⟩
  have hcoe : (Q' : Subgroup H) = (Q : Subgroup ↥(R.map ψ)).map eR.toMonoidHom :=
    Sylow.coe_mapSurjective (f := eR.toMonoidHom) (hf := eR.surjective) Q
  intro A hA
  rw [hcoe] at hA
  obtain ⟨y, hyQ, rfl⟩ := Subgroup.mem_map.mp hA
  have hyP : (y : X) ∈ P := by
    have hy : y ∈ (P ⊓ R.map ψ).subgroupOf (R.map ψ) := hQ ▸ hyQ
    exact (Subgroup.mem_subgroupOf.mp hy).1
  obtain ⟨r, hrR, hry⟩ := Subgroup.mem_map.mp y.2
  refine ⟨⟨r, hrR⟩, ?_, ?_⟩
  · rwa [hry]
  · rw [← heR ⟨r, hrR⟩]
    exact congrArg eR (Subtype.ext hry)

open Matrix

private theorem exists_commutator_eq_neg_one_sl2 {F : Type} [Field F] [Finite F] :
    ∃ x y : SL(2, F), x * y * x⁻¹ * y⁻¹ = -1 := by
  have hne : NeZero (ringChar F) := ⟨CharP.char_ne_zero_of_finite F (ringChar F)⟩
  obtain ⟨a, b, hab⟩ := CharP.sq_add_sq F (ringChar F) (-1)
  have hab' : ((a : F)) ^ 2 + ((b : F)) ^ 2 = -1 := by simpa using hab
  have hA : Matrix.det !![(0 : F), 1; -1, 0] = 1 := by simp [Matrix.det_fin_two]
  have hB : Matrix.det !![(a : F), b; b, -a] = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination -hab'
  let A : SL(2, F) := ⟨_, hA⟩
  let B : SL(2, F) := ⟨_, hB⟩
  have hA' : (A : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := rfl
  have hB' : (B : Matrix (Fin 2) (Fin 2) F) = !![(a : F), b; b, -a] := rfl
  refine ⟨A, B, ?_⟩
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, hA', hB',
    Matrix.adjugate_fin_two_of, Matrix.mul_fin_two, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp <;> first | ring1 | linear_combination hab'

end Generic


variable {t : StatedLieTag} {n r f : ℕ} [hr : Fact r.Prime]

theorem pairedModel_range_le_orthogonalGroup (D : PairedOrthogonalModel t n r f) :
    D.π.range ≤ TauCeti.QuadraticMap.orthogonalGroup D.Q := by
  rintro - ⟨x, rfl⟩
  rw [D.hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction D.Q (D.η x) v

theorem pairedModel_reflection_mul_mem_range (D : PairedOrthogonalModel t n r f)
    (a b : D.V) [Invertible (D.Q a)] [Invertible (D.Q b)] (h : D.Q a * D.Q b = 1) :
    TauCeti.QuadraticMap.reflection D.Q a * TauCeti.QuadraticMap.reflection D.Q b ∈ D.π.range := by
  refine ⟨D.η.symm ⟨CliffordAlgebra.ι D.Q a * CliffordAlgebra.ι D.Q b,
    ι_mul_ι_mem_spinGroup D.Q h⟩, ?_⟩
  rw [D.hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  exact CFSG.ComponentClassification.HarrisLit.T1.spinAction_ι_mul_ι h

theorem pairedModel_pow_four_eq_one_of_mem_center (D : PairedOrthogonalModel t n r f)
    (hr2 : r ≠ 2) {z : (modelUniv t n r f hr.out).K}
    (hz : z ∈ center (modelUniv t n r f hr.out).K) : z ^ 4 = 1 := by
  classical
  let F := GaloisField r f
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hr2
  let : Invertible (2 : F) := invertibleOfNonzero h2
  obtain ⟨c, hc⟩ := CFSG.ClassicalGroups.Orthogonal.mem_scalars.mp (D.hscalar z hz)
  let k : Fin D.m := ⟨0, D.hm⟩
  have hQv : D.Q ((D.A k).e₁ + (D.A k).f₁) = 1 := by
    rw [QuadraticMap.map_add D.Q,
      CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame.Q_e₁,
      CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame.Q_f₁,
      CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame.polar_e₁_f₁]
    ring
  have hQiso : D.Q ((D.π z) ((D.A k).e₁ + (D.A k).f₁)) = D.Q ((D.A k).e₁ + (D.A k).f₁) := by
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
      (pairedModel_range_le_orthogonalGroup D ⟨z, rfl⟩) _
  have hcQ : c ^ 2 = 1 := by
    rw [hc, QuadraticMap.map_smul, hQv, smul_eq_mul, mul_one] at hQiso
    simpa [pow_two] using hQiso
  have hcQ' : c * c = 1 := by rw [← pow_two, hcQ]
  have hsq : D.π z * D.π z = 1 := by
    refine LinearEquiv.ext fun v => ?_
    rw [LinearEquiv.mul_apply]
    change D.π z (D.π z v) = v
    rw [hc, hc, smul_smul, hcQ', one_smul]
  have hz2ker : z ^ 2 ∈ D.π.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    simpa [pow_two] using hsq
  have hηker : D.η (z ^ 2) ∈ (spinAction D.Q).ker := by
    rw [MonoidHom.mem_ker]
    have h := hz2ker
    rw [MonoidHom.mem_ker] at h
    simpa only [D.hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using h
  have : Nontrivial D.V :=
    ⟨⟨(D.A k).e₁, 0,
      CFSG.ClassicalGroups.Orthogonal.HypPair.e_ne_zero (D.A k).P⟩⟩
  have hQne : D.Q ≠ 0 := by
    intro h0
    have h1 : D.Q ((D.A k).e₁ + (D.A k).f₁) = 0 := by
      simpa using congrArg
        (fun Q : QuadraticForm F D.V => Q ((D.A k).e₁ + (D.A k).f₁)) h0
    rw [hQv] at h1
    exact one_ne_zero h1
  have hQnd : D.Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp D.hQ
  rcases (mem_ker_spinAction_iff D.Q hQnd (D.η (z ^ 2))).mp hηker with h1 | h1
  · have h2 : z ^ 2 = 1 := D.η.injective (by rw [h1, map_one])
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, h2, one_pow]
  · have h2 : (z ^ 2) ^ 2 = 1 := by
      apply D.η.injective
      rw [map_pow, h1, pow_two, CliffordAlgebra.spinGroup.negOne_mul_self D.Q hQne, map_one]
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
    exact h2

theorem pairedModel_exists_mulEquiv (D : PairedOrthogonalModel t n r f) (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n r f) (hA1 : ¬ (t = .PSL ∧ n = 2)) (k : Fin D.m × Bool) :
    ∃ e : ↥(D.R k) ≃* SL(2, GaloisField r f), ∀ x : ↥(D.R k),
      D.π x = if k.2 then (D.A k.1).swap.La (e x) else (D.A k.1).La (e x) := by
  classical
  let F := GaloisField r f
  have hinj : D.R k ⊓ D.π.ker = ⊥ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.inf_ker_eq_bot_of_mem_fundamentalSubgroups
      hfund hadm hA1 D.π D.hker (D.hR k).1
  have hinj' : Function.Injective (D.π.comp (D.R k).subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    apply Subtype.ext
    have hmem : (x : (modelUniv t n r f hr.out).K) ∈ D.R k ⊓ D.π.ker := ⟨x.2, hx⟩
    rw [hinj, Subgroup.mem_bot] at hmem
    exact hmem
  have hrange : (D.π.comp (D.R k).subtype).range = (D.R k).map D.π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let e1 : ↥(D.R k) ≃* ↥((D.π.comp (D.R k).subtype).range) :=
    MonoidHom.ofInjective hinj'
  let e2 : ↥((D.π.comp (D.R k).subtype).range) ≃* ↥((D.R k).map D.π) :=
    MulEquiv.subgroupCongr hrange
  let Gk : SL(2, F) →* (D.V ≃ₗ[F] D.V) :=
    if k.2 then (D.A k.1).swap.La else (D.A k.1).La
  have hGk : Function.Injective Gk := by
    rcases hb : k.2 with _ | _
    · simpa [Gk, hb] using
        CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame.La_injective (D.A k.1)
    · simpa [Gk, hb] using
        CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame.La_injective (D.A k.1).swap
  let e4 : SL(2, F) ≃* ↥Gk.range := MonoidHom.ofInjective hGk
  have hGr : Gk.range =
      (if k.2 then (D.A k.1).swap.La.range else (D.A k.1).La.range) := by
    rcases hb : k.2 with _ | _ <;> simp [Gk, hb]
  let eSL : ↥(if k.2 then (D.A k.1).swap.La.range else (D.A k.1).La.range) ≃* SL(2, F) :=
    (MulEquiv.subgroupCongr hGr).symm.trans e4.symm
  let e : ↥(D.R k) ≃* SL(2, F) :=
    (e1.trans e2).trans ((MulEquiv.subgroupCongr (D.hR k).2).trans eSL)
  refine ⟨e, fun x => ?_⟩
  have hGk_e4 : ∀ a : SL(2, F), Gk a = (e4 a : D.V ≃ₗ[F] D.V) := fun a =>
    (MonoidHom.ofInjective_apply hGk).symm
  have hcancel : ∀ z : ↥(if k.2 then (D.A k.1).swap.La.range else (D.A k.1).La.range),
      Gk (eSL z) = (z : D.V ≃ₗ[F] D.V) := by
    intro z
    have h1 : eSL z = e4.symm ((MulEquiv.subgroupCongr hGr).symm z) := rfl
    rw [h1, hGk_e4, MulEquiv.apply_symm_apply]
    rfl
  have hex : Gk (e x) = D.π x := by
    have h2 : e x = eSL ((MulEquiv.subgroupCongr (D.hR k).2) (e2 (e1 x))) := rfl
    rw [h2, hcancel]
    rfl
  rcases hb : k.2 with _ | _
  · simpa [Gk, hb] using hex.symm
  · simpa [Gk, hb] using hex.symm

theorem pairedModel_conj_La_neg_one (D : PairedOrthogonalModel t n r f) (hr2 : r ≠ 2)
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n r f) (hA1 : ¬ (t = .PSL ∧ n = 2))
    {X : Type} [Group X] (ψ : (modelUniv t n r f hr.out).K →* X)
    (hker : ψ.ker ≤ center (modelUniv t n r f hr.out).K) {c : (modelUniv t n r f hr.out).K}
    (hc : ∀ k, ∃ k', ((D.R k).map ψ).map (MulAut.conj (ψ c)).toMonoidHom = (D.R k').map ψ)
    (i : Fin D.m) :
    ∃ i', D.π c * (D.A i).La (-1) * (D.π c)⁻¹ = (D.A i').La (-1) := by
  classical
  let F := GaloisField r f
  let K := (modelUniv t n r f hr.out).K
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hr2
  obtain ⟨x, y, hxy⟩ := exists_commutator_eq_neg_one_sl2 (F := F)
  let k0 : Fin D.m × Bool := (i, false)
  obtain ⟨e0, he0⟩ := pairedModel_exists_mulEquiv D hfund hadm hA1 k0
  have he0' : ∀ a : ↥(D.R k0), D.π a = (D.A i).La (e0 a) := by
    intro a
    simpa [k0] using he0 a
  let z : ↥(D.R k0) := e0.symm (-1)
  have hzπ : D.π z = (D.A i).La (-1) := by
    rw [he0', MulEquiv.apply_symm_apply]
  have hz2 : z * z = 1 := by
    apply e0.injective
    rw [map_mul, MulEquiv.apply_symm_apply]
    simp
  have hzne : z ≠ 1 := by
    intro hz1
    have h1 : D.π z = 1 := by rw [hz1]; simp
    have h2' : (-1 : SL(2, F)) = 1 := by
      apply CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame.La_injective (D.A i)
      rw [← hzπ, h1, map_one]
    exact CFSG.Semidihedral.OddFieldSL2.minusIdentity_ne_one F h2 h2'
  let xs : ↥(D.R k0) := e0.symm x
  let ys : ↥(D.R k0) := e0.symm y
  have hcomm_z : xs * ys * xs⁻¹ * ys⁻¹ = z := by
    apply e0.injective
    have hxs : e0 xs = x := by simp [xs]
    have hys : e0 ys = y := by simp [ys]
    have hz0 : e0 z = -1 := by simp [z]
    calc e0 (xs * ys * xs⁻¹ * ys⁻¹) = e0 xs * e0 ys * (e0 xs)⁻¹ * (e0 ys)⁻¹ := by
          simp only [map_mul, map_inv]
      _ = x * y * x⁻¹ * y⁻¹ := by rw [hxs, hys]
      _ = -1 := hxy
      _ = e0 z := hz0.symm
  obtain ⟨k', hk'⟩ := hc k0
  have hfactor : ∀ w : ↥(D.R k0), ∃ (w' : ↥(D.R k')) (u : K),
      u ∈ center K ∧ c * (w : K) * c⁻¹ = u * (w' : K) := by
    intro w
    have hmem : ψ (c * (w : K) * c⁻¹) ∈ (D.R k').map ψ := by
      have hconjeq : ψ (c * (w : K) * c⁻¹) = MulAut.conj (ψ c) (ψ (w : K)) := by
        simp [map_mul, MulAut.conj_apply]
      rw [hconjeq, ← hk']
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem ψ w.2)
    obtain ⟨w', hw'mem, hw'eq⟩ := Subgroup.mem_map.mp hmem
    refine ⟨⟨w', hw'mem⟩, (c * (w : K) * c⁻¹) * (w' : K)⁻¹, ?_, ?_⟩
    · apply hker
      exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, ← hw'eq, mul_inv_cancel])
    · group
  obtain ⟨w1, u1, hu1, h1⟩ := hfactor xs
  obtain ⟨w2, u2, hu2, h2'⟩ := hfactor ys
  have hinj' : D.R k' ⊓ D.π.ker = ⊥ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.inf_ker_eq_bot_of_mem_fundamentalSubgroups
      hfund hadm hA1 D.π D.hker (D.hR k').1
  have hcen1 : ∀ p : K, u1 * p = p * u1 := fun p =>
    (Subgroup.mem_center_iff.mp hu1 p).symm
  have hcen2 : ∀ p : K, u2 * p = p * u2 := fun p =>
    (Subgroup.mem_center_iff.mp hu2 p).symm
  have hcz : c * (z : K) * c⁻¹ = (w1 : K) * (w2 : K) * (w1 : K)⁻¹ * (w2 : K)⁻¹ := by
    have hzcomm : (z : K) = (xs : K) * (ys : K) * (xs : K)⁻¹ * (ys : K)⁻¹ :=
      (congrArg Subtype.val hcomm_z).symm
    calc c * (z : K) * c⁻¹
        = (c * (xs : K) * c⁻¹) * (c * (ys : K) * c⁻¹) *
            (c * (xs : K) * c⁻¹)⁻¹ * (c * (ys : K) * c⁻¹)⁻¹ := by
          rw [hzcomm]
          group
      _ = (u1 * (w1 : K)) * (u2 * (w2 : K)) * (u1 * (w1 : K))⁻¹ *
            (u2 * (w2 : K))⁻¹ := by rw [h1, h2']
      _ = (w1 : K) * (w2 : K) * (w1 : K)⁻¹ * (w2 : K)⁻¹ := by
          rw [← commutatorElement_def, ← commutatorElement_def]
          rw [CFSG.GroupTheory.commutatorElement_central_mul_left hcen1]
          rw [CFSG.GroupTheory.commutatorElement_mul_central_right hcen2]
  have hcz_mem : c * (z : K) * c⁻¹ ∈ D.R k' := by
    rw [hcz]
    exact (D.R k').mul_mem ((D.R k').mul_mem ((D.R k').mul_mem w1.2 w2.2)
      ((D.R k').inv_mem w1.2)) ((D.R k').inv_mem w2.2)
  have hcz2 : (c * (z : K) * c⁻¹) * (c * (z : K) * c⁻¹) = 1 := by
    have hz2K : (z : K) * (z : K) = 1 := congrArg Subtype.val hz2
    calc (c * (z : K) * c⁻¹) * (c * (z : K) * c⁻¹) = c * ((z : K) * (z : K)) * c⁻¹ := by
          group
      _ = 1 := by rw [hz2K]; group
  have hczne : c * (z : K) * c⁻¹ ≠ 1 := by
    intro h
    apply hzne
    apply Subtype.ext
    calc (z : K) = c⁻¹ * (c * (z : K) * c⁻¹) * c := by group
      _ = 1 := by rw [h]; group
  have hπinj : Function.Injective (fun a : ↥(D.R k') => D.π (a : K)) := by
    intro a b hab
    have hab' : D.π (a : K) = D.π (b : K) := hab
    apply Subtype.ext
    have hmem : (a : K) * (b : K)⁻¹ ∈ D.R k' ⊓ D.π.ker := by
      refine ⟨(D.R k').mul_mem a.2 ((D.R k').inv_mem b.2), ?_⟩
      exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hab', mul_inv_cancel])
    rw [hinj', Subgroup.mem_bot] at hmem
    calc (a : K) = (a : K) * (b : K)⁻¹ * (b : K) := by group
      _ = (b : K) := by rw [hmem, one_mul]
  have hcπne : D.π (c * (z : K) * c⁻¹) ≠ 1 := by
    intro h
    apply hczne
    have h1 : D.π (⟨c * (z : K) * c⁻¹, hcz_mem⟩ : ↥(D.R k')) =
        D.π (1 : ↥(D.R k')) := by
      simpa using h
    exact congrArg Subtype.val (hπinj h1)
  have hsqπ : D.π (c * (z : K) * c⁻¹) * D.π (c * (z : K) * c⁻¹) = 1 := by
    rw [← map_mul, hcz2, map_one]
  have hmemrange : D.π (c * (z : K) * c⁻¹) ∈
      (if k'.2 then (D.A k'.1).swap.La.range else (D.A k'.1).La.range) := by
    have h := Subgroup.mem_map_of_mem D.π hcz_mem
    rwa [(D.hR k').2] at h
  rcases hb : k'.2 with _ | _
  · have hrange : D.π (c * (z : K) * c⁻¹) ∈ (D.A k'.1).La.range := by
      simpa [hb] using hmemrange
    obtain ⟨A, hA⟩ := hrange
    have hA2 : A * A = 1 := by
      apply CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame.La_injective (D.A k'.1)
      rw [map_mul, hA, hsqπ, map_one]
    have hA1' : A ≠ 1 := by
      intro h
      exact hcπne (by rw [← hA, h, map_one])
    have hAinv : A⁻¹ = A := by
      calc A⁻¹ = A⁻¹ * 1 := (mul_one _).symm
        _ = A⁻¹ * (A * A) := by rw [hA2]
        _ = (A⁻¹ * A) * A := by group
        _ = 1 * A := by rw [inv_mul_cancel]
        _ = A := one_mul A
    have hAneg : A = -1 := by
      rcases CFSG.Semidihedral.OddFieldSL2.eq_one_or_minusIdentity_of_inv_eq_self F h2 A hAinv
        with h | h
      · exact absurd h hA1'
      · simpa [CFSG.Semidihedral.OddFieldSL2.minusIdentity] using h
    refine ⟨k'.1, ?_⟩
    have hconjπ : D.π (c * (z : K) * c⁻¹) = (D.A k'.1).La (-1) := by
      rw [hAneg] at hA
      exact hA.symm
    have hfin : D.π (c * (z : K) * c⁻¹) =
        D.π c * (D.A i).La (-1) * (D.π c)⁻¹ := by
      rw [map_mul, map_mul, map_inv, hzπ]
    rw [← hfin, hconjπ]
  · have hrange : D.π (c * (z : K) * c⁻¹) ∈ (D.A k'.1).swap.La.range := by
      simpa [hb] using hmemrange
    obtain ⟨A, hA⟩ := hrange
    have hA2 : A * A = 1 := by
      apply CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame.La_injective (D.A k'.1).swap
      rw [map_mul, hA, hsqπ, map_one]
    have hA1' : A ≠ 1 := by
      intro h
      exact hcπne (by rw [← hA, h, map_one])
    have hAinv : A⁻¹ = A := by
      calc A⁻¹ = A⁻¹ * 1 := (mul_one _).symm
        _ = A⁻¹ * (A * A) := by rw [hA2]
        _ = (A⁻¹ * A) * A := by group
        _ = 1 * A := by rw [inv_mul_cancel]
        _ = A := one_mul A
    have hAneg : A = -1 := by
      rcases CFSG.Semidihedral.OddFieldSL2.eq_one_or_minusIdentity_of_inv_eq_self F h2 A hAinv
        with h | h
      · exact absurd h hA1'
      · simpa [CFSG.Semidihedral.OddFieldSL2.minusIdentity] using h
    refine ⟨k'.1, ?_⟩
    have hconjπ : D.π (c * (z : K) * c⁻¹) = (D.A k'.1).La (-1) := by
      rw [hAneg] at hA
      rw [← hA, CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame.La_swap_neg_one (D.A k'.1)]
    have hfin : D.π (c * (z : K) * c⁻¹) =
        D.π c * (D.A i).La (-1) * (D.π c)⁻¹ := by
      rw [map_mul, map_mul, map_inv, hzπ]
    rw [← hfin, hconjπ]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
