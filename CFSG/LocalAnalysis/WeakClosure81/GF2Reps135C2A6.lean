module

import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3E
import CFSG.Quasithin.Background.SmithB42Alt6Norm
import CFSG.Quasithin.Background.InternalSecB56
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJModel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.QuasithinUnique.Setup.X3 CFSG.QuasithinUnique.Setup.Offender
open CFSG.QuasithinUnique.Setup.X3E
open CFSG.Blueprint (LieModel)

theorem a6SmallModules_holds :
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
      ∀ L : Subgroup (MulAut W), IsQuasisimple ↥L → IsIrrOn L ⊤ ⊥ → IsAlt ↥L 6 →
      rk W ≤ 15 → AlternatingNatural L ⊤ ⊥ 6 := by
  intro W _ _ hW L hQ hIrr hAlt hrk
  classical
  have : Finite (Additive W) := inferInstanceAs (Finite W)
  obtain ⟨ι⟩ := hAlt
  let _ : Module (ZMod 2) (Additive W) :=
    AddCommGroup.zmodModule (n := 2) fun x => by
      have h3 : Additive.toMul (2 • x) = 1 := by
        rw [toMul_nsmul]
        simpa only [pow_two] using hW (Additive.toMul x)
      exact toMul_eq_one.1 h3
  have : Module.Finite (ZMod 2) (Additive W) := Module.Finite.of_finite
  let θ : W ≃* Multiplicative (Additive W) := (MulEquiv.multiplicativeAdditive W).symm
  let σ : alternatingGroup (Fin 6) →* (Additive W ≃ₗ[ZMod 2] Additive W) :=
    (CFSG.QuasithinUnique.Setup.Layer.binPsi θ).toMonoidHom.comp
      (L.subtype.comp ι.symm.toMonoidHom)
  have hσ : ∀ (γ : alternatingGroup (Fin 6)) (w : Additive W),
      σ γ w = Additive.ofMul ((ι.symm γ : MulAut W) (Additive.toMul w)) := fun γ w => rfl
  have hsimple : IsLSimple σ ⊤ ⊤ := by
    refine ⟨fun _ _ _ _ => trivial, ?_, fun U hU _ => ?_⟩
    · intro htop
      have hbot : (⊤ : Subgroup W) = ⊥ := by
        rw [eq_bot_iff]
        intro w _
        have h1 : Additive.ofMul w ∈ (⊤ : Submodule (ZMod 2) (Additive W)) :=
          Submodule.mem_top
        rw [htop] at h1
        rw [Submodule.mem_bot] at h1
        exact Subgroup.mem_bot.2 (by simpa using h1)
      exact (ne_of_gt hIrr.1) hbot
    · let J : Subgroup W :=
        { carrier := {s | Additive.ofMul s ∈ U}
          one_mem' := by simp
          mul_mem' := fun {a b} ha hb => by
            change Additive.ofMul (a * b) ∈ U
            rw [ofMul_mul]
            exact U.add_mem ha hb
          inv_mem' := fun {a} ha => by
            change Additive.ofMul a⁻¹ ∈ U
            rw [ofMul_inv]
            exact U.neg_mem ha }
      have hstable : StableUnder L J := by
        intro x hx s hs
        have hsU : Additive.ofMul s ∈ U := hs
        have h := hU (ι ⟨x, hx⟩) trivial (Additive.ofMul s) hsU
        rw [hσ] at h
        have hι : (ι.symm (ι ⟨x, hx⟩) : MulAut W) = x := by
          rw [MulEquiv.symm_apply_apply]
        rw [hι] at h
        exact h
      rcases hIrr.2.2.2 J hstable bot_le le_top with hJ | hJ
      · left
        rw [eq_bot_iff]
        intro w hw
        have h1 : Additive.toMul w ∈ J := hw
        rw [hJ, Subgroup.mem_bot] at h1
        rw [Submodule.mem_bot]
        exact h1
      · right
        rw [eq_top_iff]
        intro w _
        have h1 : Additive.toMul w ∈ J := by rw [hJ]; trivial
        exact h1
  have hdim := (a6SimpleModules (Additive W) σ hsimple).1
  have hcardW : Nat.card W = 2 ^ Module.finrank (ZMod 2) (Additive W) := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
    rw [Nat.card_zmod] at h1
    rwa [show Nat.card (Additive W) = Nat.card W from rfl] at h1
  have hrkfin : CFSG.Quasithin.rk W = Module.finrank (ZMod 2) (Additive W) := by
    unfold CFSG.Quasithin.rk
    rw [hcardW]
    exact padicValNat.prime_pow _
  have hle15 : Module.finrank (ZMod 2) (Additive W) ≤ 15 := by
    rw [← hrkfin]
    exact hrk
  have hcard_le : Nat.card W ≤ 2 ^ 6 := by
    rcases hdim with h | h | h
    · rw [hcardW, h]
      norm_num
    · rw [hcardW, h]
      norm_num
    · exfalso
      rw [h] at hle15
      omega
  have hcenter : Subgroup.center ↥L = ⊥ := by
    have hc : (Subgroup.center ↥L).map ι.toMonoidHom = ⊥ := by
      have hmap : (Subgroup.center ↥L).map ι.toMonoidHom =
          Subgroup.center (alternatingGroup (Fin 6)) := by
        simp
      rw [hmap, alternatingGroup.center_eq_bot (α := Fin 6) (by norm_num)]
    exact (Subgroup.map_eq_bot_iff_of_injective _ ι.injective).mp hc
  have hF : L = quasithinGenFitting L := by
    refine le_antisymm ?_ (CFSG.Quasithin.quasithinGenFitting_le L)
    exact CFSG.Quasithin.InternalSec.le_quasithinGenFitting_of_normal le_rfl
      (fun x hx k hk => L.mul_mem (L.mul_mem hx hk) (L.inv_mem hx)) hQ
  have hCtx : CFSG.Quasithin.B42Alt6.Ctx (S := W) L L :=
    { hF := hF, center := hcenter, perfect := hQ.1, iso := ⟨ι⟩ }
  have hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup W) ⊤ :=
    isIrrSec_of_isIrrOn_top hIrr
  obtain ⟨M⟩ := CFSG.Quasithin.B42Alt6.exists_n6Model (S := W) (G := L)
    (fun s => by simpa [pow_two] using hW s) hCtx hirr hcard_le
  exact M.alternatingNatural

end CFSG.LocalAnalysis.WeakClosure81
