module

public import CFSG.LocalAnalysis.StandardType.PhanEMatchSeam
public import CFSG.LocalAnalysis.StandardType.PhanEResSeamProd
public import CFSG.ClassicalInvolution.WeakCT.Sides
import CFSG.ClassicalInvolution.WeakCT.SimplyLaced

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Match

open Matrix CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.CentralExt.SLClosed
  CFSG.LieType.Chevalley.CosetBuilding CFSG.ClassicalInvolution.Phan.PhanE
  CFSG.ClassicalInvolution.Phan.PhanE.Res

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {Fld : Type} [Field Fld]

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group

variable (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
  (weylAction D.isFiniteType) D.roots D.rootGroup n H) {w₀ : W} (F : FrobData D n H w₀)
  {M : ChevModel2 D n H Fld} {θ : Fld →+* Fld} (PC : M.PhiCompat F θ)

theorem kapMat_one_tv {m : ℕ} (p q : Fin (m + 1)) (c : Fld) :
    kapMat θ false (1 : SpecialLinearGroup (Fin (m + 1)) Fld) (tv Fld p q c) =
      tv Fld p q (θ c) := by
  simp only [kapMat, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    if_neg (Bool.false_ne_true), inv_one, one_mul, mul_one]
  by_cases h : p = q
  · subst h
    simp [tv]
  · rw [tv_of_ne h, tv_of_ne h, Matrix.SpecialLinearGroup.map_transvection]

include PC in
theorem hX_of_swap {m₁ : ℕ} (L₁ : SLPath M m₁) (L₂ : SLPath M 1) {v : W} {k₁ : Fin m₁}
    (hπ₁ : weylAction D.isFiniteType v (Pi.single (F.op (L₁.e k₁)) 1) = Pi.single (L₂.e 0) 1)
    (hπ₂ : weylAction D.isFiniteType v (Pi.single (F.op (L₂.e 0)) 1) = Pi.single (L₁.e k₁) 1)
    (β : SpecialLinearGroup (Fin 2) Fld →* SpecialLinearGroup (Fin (m₁ + 1)) Fld)
    (hβu : ∀ c : Fld, β (tv Fld 0 1 c) = tv Fld k₁.castSucc k₁.succ c)
    (hβl : ∀ c : Fld, β (tv Fld 1 0 c) = tv Fld k₁.succ k₁.castSucc c) :
    (∀ c : Fld, nrep hct v * F.φ (L₁.ε (β (tv Fld 0 1 c))) * (nrep hct v)⁻¹ =
      L₂.ε (kapMat θ false (1 : SpecialLinearGroup (Fin 2) Fld) (tv Fld 0 1 c))) ∧
    (∀ c : Fld, nrep hct v * F.φ (L₁.ε (β (tv Fld 1 0 c))) * (nrep hct v)⁻¹ =
      L₂.ε (kapMat θ false (1 : SpecialLinearGroup (Fin 2) Fld) (tv Fld 1 0 c))) ∧
    (∀ c : Fld, nrep hct v * F.φ (L₂.ε (tv Fld 0 1 c)) * (nrep hct v)⁻¹ =
      L₁.ε (β (kapMat θ false (1 : SpecialLinearGroup (Fin 2) Fld) (tv Fld 0 1 c)))) ∧
    (∀ c : Fld, nrep hct v * F.φ (L₂.ε (tv Fld 1 0 c)) * (nrep hct v)⁻¹ =
      L₁.ε (β (kapMat θ false (1 : SpecialLinearGroup (Fin 2) Fld) (tv Fld 1 0 c)))) := by
  refine ⟨fun c => ?_, fun c => ?_, fun c => ?_, fun c => ?_⟩
  · rw [hβu c, L₁.tv_eq k₁.castSucc k₁.succ k₁.castSucc_lt_succ.ne c,
      pathRoot_up L₁.e k₁, Res.kappa_single hct F M PC hπ₁ c]
    rw [kapMat_one_tv, L₂.tv_eq 0 1 (by decide) (θ c),
      show pathRoot L₂.e 0 1 = Pi.single (L₂.e 0) 1 from pathRoot_up L₂.e 0]
  · rw [hβl c, L₁.tv_eq k₁.succ k₁.castSucc k₁.castSucc_lt_succ.ne.symm c,
      pathRoot_down L₁.e k₁, Res.kappa_neg_single hct F M PC hπ₁ c]
    rw [kapMat_one_tv, L₂.tv_eq 1 0 (by decide) (θ c),
      show pathRoot L₂.e 1 0 = -Pi.single (L₂.e 0) 1 from pathRoot_down L₂.e 0]
  · rw [L₂.tv_eq 0 1 (by decide) c,
      show pathRoot L₂.e 0 1 = Pi.single (L₂.e 0) 1 from pathRoot_up L₂.e 0,
      Res.kappa_single hct F M PC hπ₂ c]
    rw [kapMat_one_tv, hβu (θ c),
      L₁.tv_eq k₁.castSucc k₁.succ k₁.castSucc_lt_succ.ne (θ c), pathRoot_up L₁.e k₁]
  · rw [L₂.tv_eq 1 0 (by decide) c,
      show pathRoot L₂.e 1 0 = -Pi.single (L₂.e 0) 1 from pathRoot_down L₂.e 0,
      Res.kappa_neg_single hct F M PC hπ₂ c]
    rw [kapMat_one_tv, hβl (θ c),
      L₁.tv_eq k₁.succ k₁.castSucc k₁.castSucc_lt_succ.ne.symm (θ c), pathRoot_down L₁.e k₁]

private theorem plh_tv_eq_timmesfeld {m : ℕ} (i j : Fin (m + 1)) (c : Fld) :
    tv Fld i j c = CFSG.Timmesfeld.tv i j c := by
  by_cases h : i = j
  · subst h
    simp [tv, CFSG.Timmesfeld.tv]
  · rw [tv_of_ne h, CFSG.Timmesfeld.tv_of_ne h]

theorem blk_one_tv01' (c : Fld) :
    WeakCT.blk Fld 1 (tv Fld 0 1 c) = tv Fld (1 : Fin 2).castSucc (1 : Fin 2).succ c := by
  change WeakCT.blk Fld 1 (tv Fld 0 1 c) = tv Fld (1 : Fin 3) (2 : Fin 3) c
  rw [plh_tv_eq_timmesfeld (0 : Fin 2) 1 c, WeakCT.blk_one_tv01,
    ← plh_tv_eq_timmesfeld (1 : Fin 3) 2 c]

theorem blk_one_tv10' (c : Fld) :
    WeakCT.blk Fld 1 (tv Fld 1 0 c) = tv Fld (1 : Fin 2).succ (1 : Fin 2).castSucc c := by
  change WeakCT.blk Fld 1 (tv Fld 1 0 c) = tv Fld (2 : Fin 3) (1 : Fin 3) c
  rw [plh_tv_eq_timmesfeld (1 : Fin 2) 0 c, WeakCT.blk_one_tv10,
    ← plh_tv_eq_timmesfeld (2 : Fin 3) 1 c]

end CFSG.ClassicalInvolution.Phan.PhanE.Match

end
