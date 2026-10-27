module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJModuleOrbits
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJModel
public import CFSG.Quasithin.Background.D2Transport
public import CFSG.Quasithin.Background.F918Z4bDef

@[expose] public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

def gammaComm {V : Type} [CommGroup V] (A : Subgroup (MulAut V)) : Subgroup V :=
  commSub (⨆ (a : MulAut V) (_ : a ∈ A) (_ : a ≠ 1), fixV (Subgroup.zpowers a)) A

theorem gamma_map_congr {V V' : Type} [CommGroup V] [CommGroup V'] (e : V ≃* V')
    (A : Subgroup (MulAut V)) :
    gammaComm (A.map (MulAut.congr e).toMonoidHom) = (gammaComm A).map e.toMonoidHom := by
  have hΓ : (⨆ (a : MulAut V') (_ : a ∈ A.map (MulAut.congr e).toMonoidHom) (_ : a ≠ 1),
        fixV (Subgroup.zpowers a)) =
      (⨆ (a : MulAut V) (_ : a ∈ A) (_ : a ≠ 1), fixV (Subgroup.zpowers a)).map
        e.toMonoidHom := by
    apply le_antisymm
    · refine iSup_le fun a' => iSup_le fun ha' => iSup_le fun hne => ?_
      obtain ⟨a, ha, rfl⟩ := ha'
      have hne' : a ≠ 1 := fun h => hne (by rw [h, map_one])
      rw [← MonoidHom.map_zpowers, fixV_map_congr_equiv]
      exact Subgroup.map_mono (le_iSup_of_le a (le_iSup_of_le ha (le_iSup_of_le hne' le_rfl)))
    · simp only [Subgroup.map_iSup]
      refine iSup_le fun a => iSup_le fun ha => iSup_le fun hne => ?_
      have hne' : (MulAut.congr e).toMonoidHom a ≠ 1 := fun h =>
        hne ((MulAut.congr e).injective (h.trans (map_one (MulAut.congr e)).symm))
      rw [← fixV_map_congr_equiv, MonoidHom.map_zpowers]
      exact le_iSup_of_le _ (le_iSup_of_le ⟨a, ha, rfl⟩ (le_iSup_of_le hne' le_rfl))
  unfold gammaComm
  rw [hΓ, commSub_map_mulAutCongr]

theorem conj_toMonoidHom_eq_congr {V : Type} [CommGroup V] (g : MulAut V) :
    (MulAut.conj g).toMonoidHom = (MulAut.congr g).toMonoidHom := by
  ext x v
  rfl

theorem stab_inf_map_congr {V V' : Type} [CommGroup V] [CommGroup V'] (e : V ≃* V') (v : V)
    (L : Subgroup (MulAut V)) :
    (MulAction.stabilizer (MulAut V) v ⊓ L).map (MulAut.congr e).toMonoidHom =
      MulAction.stabilizer (MulAut V') (e v) ⊓ L.map (MulAut.congr e).toMonoidHom := by
  ext y
  constructor
  · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
    refine ⟨?_, x, hx2, rfl⟩
    have h1 : x v = v := hx1
    show e (x (e.symm (e v))) = e v
    rw [e.symm_apply_apply, h1]
  · rintro ⟨hy1, x, hx2, rfl⟩
    refine ⟨x, ⟨?_, hx2⟩, rfl⟩
    have h : e (x (e.symm (e v))) = e v := hy1
    rw [e.symm_apply_apply] at h
    exact e.injective h

theorem rk_commSub_congr {V V' : Type} [CommGroup V] [CommGroup V'] (e : V ≃* V')
    (x : MulAut V) :
    rk ↥(commSub (⊤ : Subgroup V') (Subgroup.zpowers (MulAut.congr e x))) =
      rk ↥(commSub (⊤ : Subgroup V) (Subgroup.zpowers x)) := by
  have h := commSub_map_mulAutCongr e (⊤ : Subgroup V) (Subgroup.zpowers x)
  rw [Subgroup.map_top_of_surjective _ e.surjective, MonoidHom.map_zpowers] at h
  calc rk ↥(commSub (⊤ : Subgroup V') (Subgroup.zpowers (MulAut.congr e x)))
      = rk ↥((commSub (⊤ : Subgroup V) (Subgroup.zpowers x)).map e.toMonoidHom) :=
        congrArg (fun H : Subgroup V' => rk ↥H) h
    _ = rk ↥(commSub (⊤ : Subgroup V) (Subgroup.zpowers x)) :=
        rk_map_eq_of_injective _ e.injective

theorem fixV_zpowers_congr {V V' : Type} [CommGroup V] [CommGroup V'] (e : V ≃* V')
    (x : MulAut V) :
    fixV (Subgroup.zpowers (MulAut.congr e x)) =
      (fixV (Subgroup.zpowers x)).map e.toMonoidHom := by
  have h := fixV_map_congr_equiv e (Subgroup.zpowers x)
  rwa [MonoidHom.map_zpowers] at h


section Model


theorem exists_model {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (hrk : rk W = 12) {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y) (hN : (L.subgroupOf Y).Normal)
    (hspor : IsSpor ↥L .J2) (hirr : IsIrrOn L ⊤ ⊥) :
    ∃ ψ : W ≃* W12, L.map (MulAut.congr ψ).toMonoidHom = hjL0 ∧
      hjL0 ≤ Y.map (MulAut.congr ψ).toMonoidHom ∧
      (hjL0.subgroupOf (Y.map (MulAut.congr ψ).toMonoidHom)).Normal := by
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_map_eq_hjL0 hW hrk hspor hirr
  have hLY' : hjL0 ≤ Y.map (MulAut.congr ψ).toMonoidHom := hψ ▸ Subgroup.map_mono hLY
  refine ⟨ψ, hψ, hLY', ?_⟩
  rw [Subgroup.normal_subgroupOf_iff hLY']
  rintro _ _ hh ⟨k, hk, rfl⟩
  rw [← hψ] at hh ⊢
  obtain ⟨h, hh, rfl⟩ := hh
  refine ⟨k * h * k⁻¹, ?_, by simp only [map_mul, map_inv]⟩
  exact (Subgroup.normal_subgroupOf_iff hLY).1 hN h k hh hk

theorem exists_model_of_setup {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L : Subgroup (MulAut W)} (hset : HJSetup W Y L) :
    ∃ ψ : W ≃* W12, L.map (MulAut.congr ψ).toMonoidHom = hjL0 ∧
      hjL0 ≤ Y.map (MulAut.congr ψ).toMonoidHom ∧
      (hjL0.subgroupOf (Y.map (MulAut.congr ψ).toMonoidHom)).Normal :=
  exists_model hW hset.2.2.2.2.1 hset.1 hset.2.1 hset.2.2.1 hset.2.2.2.1

end Model

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
