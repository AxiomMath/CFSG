module

public import CFSG.Quasithin.Background.C126A5Lift6

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C126.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B6 Equiv
  CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

namespace Lift

variable {H T M V Y : Subgroup G} {hV : IsElemAbelian 2 V} {s : Setting H T M V Y hV}
  {d : Data H T V Y hV}

namespace XData

variable {x : G} (hx : XData s d x) (hY : IsShort2 Y) (hA3 : IsAltType Y 3)

include hx hY hA3

@[expose] noncomputable def betaEquiv :
    ↥(blockU (Khat s d x)) ≃* Multiplicative (evenWeight 5) :=
  (MulEquiv.subgroupCongr (hx.blockU_eq_Vc hY hA3)).trans
    ((Subgroup.equivMapOfInjective (commV d.L) (valHom hV) IntMod.val_injective).symm.trans d.β)

theorem betaEquiv_apply (u : ↥(blockU (Khat s d x))) (w : ↥(commV d.L))
    (hw : (w : IntMod V hV).val = (u : G)) : hx.betaEquiv hY hA3 u = d.β w := by
  have h : (Subgroup.equivMapOfInjective (commV d.L) (valHom hV) IntMod.val_injective) w =
      MulEquiv.subgroupCongr (hx.blockU_eq_Vc hY hA3) u :=
    Subtype.ext (by show (w : IntMod V hV).val = (u : G); exact hw)
  show d.β ((Subgroup.equivMapOfInjective (commV d.L) (valHom hV) IntMod.val_injective).symm
    (MulEquiv.subgroupCongr (hx.blockU_eq_Vc hY hA3) u)) = d.β w
  rw [← h]
  simp

theorem exists_betaPre (u : ↥(blockU (Khat s d x))) :
    ∃ w : ↥(commV d.L), (w : IntMod V hV).val = (u : G) := by
  have hu : (u : G) ∈ Vc d := hx.blockU_eq_Vc hY hA3 ▸ u.2
  obtain ⟨w, hw, hwu⟩ := mem_Vc.1 hu
  exact ⟨⟨w, hw⟩, hwu⟩

theorem isAltType_five (hRad : twoResidual H ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 H) :
    IsAltType (Khat s d x) 5 := by
  refine ⟨hx.alpha, hx.alpha_surj, hx.alpha_ker hRad, (hx.betaEquiv hY hA3).toMonoidHom,
    (hx.betaEquiv hY hA3).surjective, ?_, ?_⟩
  · rw [hx.blockZ_eq_bot hY hA3, Subgroup.bot_subgroupOf]
    exact (MonoidHom.ker_eq_bot_iff _).2 (hx.betaEquiv hY hA3).injective
  · intro ℓ u v huv i
    obtain ⟨u', hu'⟩ := hx.exists_betaPre hY hA3 u
    have hℓ : cv hV (ℓ : G) ∈ d.L := hx.cv_mem_L ℓ.2
    set ℓ' : ↥d.L := ⟨cv hV (ℓ : G), hℓ⟩ with hℓ'
    have hu'' : ((ℓ' : MulAut (IntMod V hV)) (u' : IntMod V hV)) ∈ commV d.L :=
      act_mem_commV hℓ u'.2
    have hℓN : (ℓ : G) ∈ Subgroup.normalizer (V : Set G) := s.H_le_N (hx.Khat_le_H ℓ.2)
    have hv' : ((⟨(ℓ' : MulAut (IntMod V hV)) (u' : IntMod V hV), hu''⟩ : ↥(commV d.L)) :
        IntMod V hV).val = (v : G) := by
      show ((cv hV (ℓ : G)) (u' : IntMod V hV)).val = _
      rw [cv_val hV hℓN, hu', huv]
      rfl
    have h1 := hx.betaEquiv_apply hY hA3 v _ hv'
    have h2 := hx.betaEquiv_apply hY hA3 u u' hu'
    have h3 := d.hβ ℓ' u' hu'' i
    have h4 : ((hx.alpha ℓ : ↥(alternatingGroup (Fin 5))) : Perm (Fin 5)) = d.θ ℓ' := by
      rw [alpha_apply, d.th_of_mem hℓ]
    show ((Multiplicative.toAdd ((hx.betaEquiv hY hA3) v) : evenWeight 5) : Fin 5 → ZMod 2) i = _
    rw [h1, h4]
    show _ = ((Multiplicative.toAdd ((hx.betaEquiv hY hA3) u) : evenWeight 5) :
      Fin 5 → ZMod 2) _
    rw [h2]
    exact h3

end XData

end Lift

end CFSG.Quasithin.C126.A5
