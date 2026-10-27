module

public import CFSG.Quasithin.Background.H12OneHatM22PfIrr
public import CFSG.Quasithin.Background.H12OneHatM22PfReal
public import CFSG.Quasithin.Background.H12OneHatM22PfModelBase

public section

namespace CFSG.Quasithin.H.Mathieu.H12Pf

open CFSG.Quasithin CFSG.Quasithin.HatM22 CFSG.CharacterTheory.SteinbergBY

@[expose] def realAddHom : (Fin 6 → FieldFour) →+ (Fin 12 → ZMod 2) where
  toFun := realV
  map_zero' := funext fun _ => cf_zero _
  map_add' := realV_add

@[expose] noncomputable def realAddEquiv : (Fin 6 → FieldFour) ≃+ (Fin 12 → ZMod 2) :=
  AddEquiv.ofBijective realAddHom ⟨realV_injective, realV_surjective⟩

@[expose] noncomputable def hatEquivG : ↥hatM22Γ₀ ≃* ↥H12Cert.G :=
  (hatM22Γ₀.equivMapOfInjective realGL realGL_injective).trans
    (MulEquiv.subgroupCongr map_realGL_hatM22Γ₀)

theorem hatEquivG_val (γ : ↥hatM22Γ₀) :
    ((hatEquivG γ : ↥H12Cert.G) : GL (Fin 12) (ZMod 2)) = realGL (γ : GL (Fin 6) FieldFour) :=
  rfl

variable {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}

theorem exists_model_of_mhat22Twelve
    [Finite W] (hV : ∀ w : W, w ^ 2 = 1)
    (h : Mhat22Twelve L ⊤ ⊥) :
    ∃ (ψ : ↥H12Cert.G ≃* ↥L) (θ : W ≃* Multiplicative (Fin 12 → ZMod 2)),
      ∀ (g : ↥H12Cert.G) (w : W),
        Multiplicative.toAdd (θ (((ψ g : ↥L) : MulAut W) w)) =
          ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec
            (Multiplicative.toAdd (θ w)) := by
  have hirr := isIrrSec_of_mhat22Twelve hV h
  have hL := isHat_of_mhat22Twelve h
  have hW := card_eq_of_mhat22Twelve h
  obtain ⟨π, hπ⟩ := hatM22SmallModules_holds W hV L hL hirr (by rw [hW]; norm_num)
  have hπinj := hπ.injective_of_faithful (FFModel.nat_faithful hatM22Γ₀)
  obtain ⟨E, hE⟩ := exists_coord_of_realizesVia hπ
  let ψ : ↥H12Cert.G ≃* ↥L := hatEquivG.symm.trans (MulEquiv.ofBijective π ⟨hπinj, hπ.1⟩)
  let θ : W ≃* Multiplicative (Fin 12 → ZMod 2) := E.trans realAddEquiv.toMultiplicative
  refine ⟨ψ, θ, fun g w => ?_⟩
  obtain ⟨γ, rfl⟩ := hatEquivG.surjective g
  have hψ : ψ (hatEquivG γ) = π γ := by
    simp only [ψ, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rfl
  have hθ : ∀ x, Multiplicative.toAdd (θ x) = realV (Multiplicative.toAdd (E x)) := fun _ => rfl
  rw [hψ, hatEquivG_val, hθ, hθ]
  exact (congrArg realV (hE γ w)).trans (realV_mulVec_GL _ _)

end CFSG.Quasithin.H.Mathieu.H12Pf
