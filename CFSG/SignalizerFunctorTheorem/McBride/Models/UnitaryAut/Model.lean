module

public import CFSG.SignalizerFunctorTheorem.NearModels.Unitary.AutBound
public import CFSG.SignalizerFunctorTheorem.McBride.Models.UnitaryHeisenberg.Assembly
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryAutomorphismHermitian

public section

open CFSG.SignalizerFunctorTheorem.NearModels.UnitaryAut
open CFSG.ClassicalGroups.UnitaryFlag CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.BenderSuzuki.MatrixGroups
open CFSG.Open Matrix

namespace CFSG.SignalizerFunctorTheorem.McBride.UnitaryAut

open UnitaryHeisenberg (SU3 mk_mem_psu3)

variable {p : ℕ}

@[expose] noncomputable def proj (hp : 1 ≤ p) : SU3 hp →* PSU3 2 p :=
  (ProjGenLinGroup.mk.comp (SU3 hp).subtype).codRestrict (PSU3 2 p) (mk_mem_psu3 hp)

theorem coe_proj (hp : 1 ≤ p) (g : SU3 hp) :
    ((proj hp g : PSU3 2 p) : ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * p))) =
      ProjGenLinGroup.mk (g : GL (Fin 3) (GaloisField 2 (2 * p))) := rfl

theorem proj_surjective (hp : 1 ≤ p) : Function.Surjective (proj hp) := by
  intro y
  have hy := (SetLike.ext_iff.mp (psu3_eq_map_gramSU hp)
    (y : ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * p)))).mp y.2
  obtain ⟨g, hg, hgy⟩ := Subgroup.mem_map.mp hy
  exact ⟨⟨g, hg⟩, Subtype.ext hgy⟩

private noncomputable def psuForm (hp : 1 ≤ p) :
    HermitianForm 3 (GaloisField 2 (2 * p)) where
  conj := RingEquiv.ofBijective (unitaryFieldData_galoisField hp).bar
    ⟨(unitaryFieldData_galoisField hp).bar.injective,
      fun c => ⟨_, (unitaryFieldData_galoisField hp).bar_bar c⟩⟩
  conj_involutive := (unitaryFieldData_galoisField hp).bar_bar
  form := antidiagGram _
  form_hermitian i j := by
    fin_cases i <;> fin_cases j <;> simp [antidiagGram]
  form_nondegenerate := by
    simp [antidiagGram, Matrix.det_fin_three]

private theorem psuForm_specialSubgroup (hp : 1 ≤ p) :
    (psuForm hp).specialSubgroup =
      gramSU (unitaryFieldData_galoisField hp) (antidiagGram (GaloisField 2 (2 * p))) := by
  ext A
  rw [HermitianForm.mem_specialSubgroup_iff, mem_gramSU,
    conjTranspose_eq_transpose_map (psuForm hp) (unitaryFieldData_galoisField hp)
      (fun _ => rfl), Units.ext_iff, GeneralLinearGroup.val_det_apply, Units.val_one]
  rfl

private noncomputable def thetaEquiv (hp : 1 ≤ p) :
    hypPSU (unitaryFieldData_galoisField hp) 1 1 ≃* PSU3 2 p :=
  (hypPSUEquivPSU (unitaryFieldData_galoisField hp) (J := psuForm hp) (fun _ => rfl) rfl).trans
    (MulEquiv.subgroupCongr (by
      rw [psu3_eq_map_gramSU hp, ← psuForm_specialSubgroup hp]))

private theorem coe_thetaEquiv (hp : 1 ≤ p) (g : hypSU (unitaryFieldData_galoisField hp) 1 1) :
    ((thetaEquiv hp (hypProj (unitaryFieldData_galoisField hp) 1 1 g) : PSU3 2 p) :
      ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * p))) =
    ProjGenLinGroup.mk (hypReindexGL (g : GL (HypIndex 1 1) (GaloisField 2 (2 * p)))) := rfl

theorem exists_rep (hp : p.Prime) (g : MulAut (PSU3 2 p)) (hg : Nat.Coprime p (orderOf g)) :
    ∃ (σ : GaloisField 2 (2 * p) ≃+* GaloisField 2 (2 * p))
      (B : GL (Fin 3) (GaloisField 2 (2 * p))), σ * σ = 1 ∧ ∀ y : SU3 hp.one_le,
      ((g (proj hp.one_le y) : PSU3 2 p) : ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * p))) =
        ProjGenLinGroup.mk (B * glAut σ (y : GL (Fin 3) (GaloisField 2 (2 * p))) * B⁻¹) := by
  have hf := hp.one_le
  have hq : 2 < 2 ^ p :=
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp.two_le
  set h := unitaryFieldData_galoisField hf with hh
  let Θ := thetaEquiv hf
  let α : MulAut (hypPSU h 1 1) := MulAut.congr Θ.symm g
  obtain ⟨x, hx⟩ := isometryAut_surjective h hq α
  refine ⟨(x : SemiGL (HypIndex 1 1) (GaloisField 2 (2 * p))).right,
    hypReindexGL (x : SemiGL (HypIndex 1 1) (GaloisField 2 (2 * p))).left, ?_, ?_⟩
  · have hxm : isometryAut h 1 1 le_rfl le_rfl (x ^ orderOf g) = 1 := by
      rw [map_pow, hx]
      change (MulAut.congr Θ.symm g) ^ orderOf g = 1
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    have h1 := (semilinearAutHom_eq_one_iff h le_rfl le_rfl (by norm_num) _).mp hxm
    have hσm : (x : SemiGL (HypIndex 1 1) (GaloisField 2 (2 * p))).right ^ orderOf g = 1 := by
      have := h1.1
      change ((x ^ orderOf g : semilinearIsometries h 1 1) : SemiGL (HypIndex 1 1)
        (GaloisField 2 (2 * p))).right = RingEquiv.refl _ at this
      rw [Subgroup.coe_pow] at this
      have h2 := map_pow (SemidirectProduct.rightHom :
        SemiGL (HypIndex 1 1) (GaloisField 2 (2 * p)) →* _) (x : SemiGL (HypIndex 1 1)
          (GaloisField 2 (2 * p))) (orderOf g)
      exact h2.symm.trans this
    have hord : orderOf (x : SemiGL (HypIndex 1 1) (GaloisField 2 (2 * p))).right ∣ 2 := by
      have hd1 := orderOf_dvd_of_pow_eq_one hσm
      have hd2 : orderOf (x : SemiGL (HypIndex 1 1) (GaloisField 2 (2 * p))).right ∣ 2 * p := by
        have := orderOf_dvd_natCard (x : SemiGL (HypIndex 1 1) (GaloisField 2 (2 * p))).right
        rwa [card_ringEquiv_unitary h] at this
      exact (Nat.Coprime.coprime_dvd_right hd1 hg).symm.dvd_of_dvd_mul_right hd2
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp hord
  · intro y
    have hyS : hypReindexGL.symm (y : GL (Fin 3) (GaloisField 2 (2 * p))) ∈ hypSU h 1 1 := by
      rw [← hypReindexGL_mem_iff h (J := psuForm hf) (fun _ => rfl) rfl,
        MulEquiv.apply_symm_apply, psuForm_specialSubgroup]
      exact y.2
    set s : hypSU h 1 1 := ⟨_, hyS⟩ with hs_def
    have hs : hypReindexGL (s : GL (HypIndex 1 1) (GaloisField 2 (2 * p))) = y :=
      MulEquiv.apply_symm_apply _ _
    have h1 : proj hf y = Θ (hypProj h 1 1 s) := by
      apply Subtype.ext
      rw [coe_proj, coe_thetaEquiv, hs]
    have h2 : g (Θ (hypProj h 1 1 s)) = Θ (α (hypProj h 1 1 s)) := by
      change g (Θ (hypProj h 1 1 s)) = Θ (Θ.symm (g (Θ (hypProj h 1 1 s))))
      rw [MulEquiv.apply_symm_apply]
    rw [h1, h2, ← hx]
    change ((Θ (semilinearAutHom h le_rfl le_rfl (Subgroup.inclusion semilinearIsometries_le x)
      (hypProj h 1 1 s)) : PSU3 2 p) : ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * p))) = _
    rw [semilinearAutHom_apply, coe_thetaEquiv]
    refine congrArg ProjGenLinGroup.mk ?_
    change hypReindexGL ((x : SemiGL (HypIndex 1 1) (GaloisField 2 (2 * p))).left *
      glAut (x : SemiGL (HypIndex 1 1) (GaloisField 2 (2 * p))).right
        (s : GL (HypIndex 1 1) (GaloisField 2 (2 * p))) *
      (x : SemiGL (HypIndex 1 1) (GaloisField 2 (2 * p))).left⁻¹) = _
    rw [map_mul, map_mul, map_inv, ← glAut_hypReindexGL, hs]

end CFSG.SignalizerFunctorTheorem.McBride.UnitaryAut
