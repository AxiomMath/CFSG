module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Ctx
public import CFSG.Quasithin.Background.SmithB42Disp

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Quasithin.B42Disp
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)} {t : MulAut W}

theorem w135c2_modelAct_sq (hctx : Is135Context Y L) {M : Type*} [Group M]
    (e : ↥L ⧸ Subgroup.center ↥L ≃* M) (htY : t ∈ Y) (ht2 : orderOf t = 2)
    (hN : t ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    modelAct L e ⟨t, hN⟩ * modelAct L e ⟨t, hN⟩ = 1 := by
  have htt : t * t = 1 := by
    rw [← sq, ← ht2]
    exact pow_orderOf_eq_one t
  have hsq : (⟨t, hN⟩ : Subgroup.normalizer (L : Set (MulAut W))) * ⟨t, hN⟩ = 1 :=
    Subtype.ext htt
  calc modelAct L e ⟨t, hN⟩ * modelAct L e ⟨t, hN⟩
      = modelAct L e (⟨t, hN⟩ * ⟨t, hN⟩) :=
        (map_mul (modelAct L e) ⟨t, hN⟩ ⟨t, hN⟩).symm
    _ = modelAct L e 1 := by rw [hsq]
    _ = 1 := map_one (modelAct L e)

theorem w135c2_modelAct_not_inner (hctx : Is135Context Y L) (hZL : Subgroup.center ↥L = ⊥)
    {M : Type*} [Group M] (e : ↥L ⧸ Subgroup.center ↥L ≃* M) (htY : t ∈ Y)
    (ht2 : orderOf t = 2) (htL : t ∉ L) (hN : t ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (c : M) : modelAct L e ⟨t, hN⟩ ≠ MulAut.conj c := by
  intro h
  obtain ⟨l, rfl⟩ := modelProj_surjective L e c
  have hinj : Function.Injective (modelProj L e) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' := mem_center_of_modelProj_eq_one L e hx
    rwa [hZL, Subgroup.mem_bot] at hx'
  have hmodel : ∀ l' : ↥L,
      modelProj L e (CFSG.QuasithinUnique.Setup.X5.conjOn L ⟨t, hN⟩ l') =
        modelProj L e (l * l' * l⁻¹) := by
    intro l'
    have h1 : modelProj L e (CFSG.QuasithinUnique.Setup.X5.conjOn L ⟨t, hN⟩ l') =
        MulAut.conj (modelProj L e l) (modelProj L e l') := by
      rw [modelProj_apply, ← modelAct_apply_mk L e ⟨t, hN⟩ l']
      exact congrArg (fun f : MulAut M => f (modelProj L e l')) h
    calc modelProj L e (CFSG.QuasithinUnique.Setup.X5.conjOn L ⟨t, hN⟩ l')
        = MulAut.conj (modelProj L e l) (modelProj L e l') := h1
      _ = modelProj L e l * modelProj L e l' * (modelProj L e l)⁻¹ := by
            rw [MulAut.conj_apply]
      _ = modelProj L e (l * l' * l⁻¹) := by simp only [map_mul, map_inv]
  have hconj : ∀ l' : ↥L,
      CFSG.QuasithinUnique.Setup.X5.conjOn L ⟨t, hN⟩ l' = l * l' * l⁻¹ :=
    fun l' => hinj (hmodel l')
  have hconjW : ∀ l' : ↥L,
      t * (l' : MulAut W) * t⁻¹ = (l : MulAut W) * l' * (l : MulAut W)⁻¹ := by
    intro l'
    have h1 := CFSG.QuasithinUnique.Setup.X5.coe_conjOn L ⟨t, hN⟩ l'
    have h2 := congrArg (fun z : ↥L => (z : MulAut W)) (hconj l')
    rw [h1] at h2
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h2
  have hcomm : ∀ l'' : ↥L,
      ((l : MulAut W)⁻¹ * t) * (l'' : MulAut W) =
        (l'' : MulAut W) * ((l : MulAut W)⁻¹ * t) := by
    intro l''
    have ht : t * (l'' : MulAut W) =
        (l : MulAut W) * (l'' : MulAut W) * (l : MulAut W)⁻¹ * t := by
      calc t * (l'' : MulAut W) = (t * (l'' : MulAut W) * t⁻¹) * t := by group
        _ = ((l : MulAut W) * (l'' : MulAut W) * (l : MulAut W)⁻¹) * t := by
              rw [hconjW l'']
        _ = (l : MulAut W) * (l'' : MulAut W) * (l : MulAut W)⁻¹ * t := rfl
    calc ((l : MulAut W)⁻¹ * t) * (l'' : MulAut W)
        = (l : MulAut W)⁻¹ * (t * (l'' : MulAut W)) := by group
      _ = (l : MulAut W)⁻¹ *
            ((l : MulAut W) * (l'' : MulAut W) * (l : MulAut W)⁻¹ * t) := by rw [ht]
      _ = (l'' : MulAut W) * ((l : MulAut W)⁻¹ * t) := by group
  have hyY : (l : MulAut W)⁻¹ * t ∈ Y :=
    Y.mul_mem (Y.inv_mem (hctx.2.2.1 l.2)) htY
  have hyZ : (l : MulAut W)⁻¹ * t ∈ Zc L := by
    refine w135c2_mem_Zc_of_comm hctx hyY ?_
    intro l'' hl''
    have h1 : ⁅(l : MulAut W)⁻¹ * t, l''⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact hcomm ⟨l'', hl''⟩
    rw [h1]
    exact (Zc L).one_mem
  have hyL : (l : MulAut W)⁻¹ * t ∈ L := w135c2_Zc_le L hyZ
  apply htL
  have hmul : (l : MulAut W) * ((l : MulAut W)⁻¹ * t) ∈ L := L.mul_mem l.2 hyL
  rwa [show (l : MulAut W) * ((l : MulAut W)⁻¹ * t) = t by group] at hmul

end CFSG.LocalAnalysis.WeakClosure81
