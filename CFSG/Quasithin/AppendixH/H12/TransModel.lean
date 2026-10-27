module

public import CFSG.Quasithin.AppendixH.H12.Trans
public import CFSG.Quasithin.AppendixH.H12.ModelCore
public import CFSG.Quasithin.Background.HM22TwelveModel
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Background.HM22Link
public import CFSG.Quasithin.Vol2.Ch9L34Gam

public section

namespace CFSG.Quasithin.AppendixH.H12

open CFSG.Quasithin CFSG.Open CFSG.ASVolI.ChH
open CFSG.Quasithin.H.Mathieu
open CFSG.Quasithin.H.Mathieu.H12Cert
open CFSG.Quasithin.H.Mathieu.M22Link
open CFSG.Quasithin.AppendixH.H12.Model (Vec12 glHom toAdd_glHom G0)

theorem exists_trans
    {G : Type} [Group G]
    {L : Subgroup G} (hL : IsHat ↥L ↥CFSG.Blueprint.NativeSporadic.M22) {V : Type} [CommGroup V]
    {ρ : G →* MulAut V} (hρ : IsFaithIrr12 (ρ.comp L.subtype)) :
    Nonempty (Trans G0 L glHom ρ) := by
  haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hρ.2.1]; norm_num)
  have hinj : Function.Injective (ρ.comp L.subtype) := hρ.2.2.1
  have hW : Nat.card V = 4096 := by rw [hρ.2.1]; norm_num
  let e : ↥L ≃* ↥(L.map ρ) :=
    (MonoidHom.ofInjective (f := ρ.comp L.subtype) hinj).trans
      (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, Subgroup.range_subtype]))
  have he : ∀ x : ↥L, ((e x : ↥(L.map ρ)) : MulAut V) = ρ (x : G) := fun x => rfl
  have hL' : IsHat ↥(L.map ρ) ↥CFSG.Blueprint.NativeSporadic.M22 :=
    isHat_of_mulEquiv' e hL
  obtain ⟨ψ, θ, hθ⟩ := exists_model_of_isHat (W := V) hρ.1 hW hL'
  refine ⟨⟨ψ.trans e.symm, θ.symm, ?_⟩⟩
  intro g v
  let θ' : Vec12 ≃* V := θ.symm
  have hx : ρ (((ψ.trans e.symm) g : ↥L) : G) = ((ψ g : ↥(L.map ρ)) : MulAut V) := by
    rw [MulEquiv.trans_apply, ← he (e.symm (ψ g)), MulEquiv.apply_symm_apply]
  change ρ (((ψ.trans e.symm) g : ↥L) : G) (θ' v) = θ' (glHom (g : GL (Fin 12) (ZMod 2)) v)
  have hm : Multiplicative.toAdd (θ (((ψ g : ↥(L.map ρ)) : MulAut V) (θ' v))) =
      (((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
        (Multiplicative.toAdd (θ (θ' v)))) := hθ g (θ' v)
  apply θ.injective
  apply Multiplicative.toAdd.injective
  rw [hx, hm, show θ (θ' v) = v from θ.apply_symm_apply v,
    show θ (θ' (glHom (g : GL (Fin 12) (ZMod 2)) v)) =
        glHom (g : GL (Fin 12) (ZMod 2)) v from θ.apply_symm_apply _, toAdd_glHom]

end CFSG.Quasithin.AppendixH.H12
