module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8H1Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8CuUnique
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8SpinHolds

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.SmithCurtis
open CFSG.Quasithin.JonesParshall
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.SpCurtis

private noncomputable def sixteenC8H1EightFrameEquiv :
    (Fin (2 * 4) → ZMod 2) ≃+ (Fin 8 → ZMod 2) where
  toFun := fcoord
  invFun := fvec
  left_inv := fvec_fcoord
  right_inv := fcoord_fvec
  map_add' := fcoord_add

theorem finrank_H1_irreducible_eight (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) G6 V) (hρ : IsSimpleRep ρ)
    (hdim : Module.finrank (ZMod 2) V = 8) :
    Module.finrank (ZMod 2) (CFSG.Quasithin.JonesParshall.H1 ρ) = 0 := by
  obtain ⟨e⟩ := cu_nonempty_equiv_of_isSpn isSpn_spinH
  obtain ⟨V₀, _, _, _, ρ₀, θ, hs₀, hθ⟩ :=
    cu_binModel spinW_exp_rk.1 spinH_irr e
  have hd₀ : Module.finrank (ZMod 2) V₀ = 8 :=
    cu_finrank_eq spinW_exp_rk.1 spinW_exp_rk.2 θ
  obtain ⟨β, hβ⟩ := classify_eight hρ hs₀ hdim hd₀
  let γ : V₀ ≃+ (Fin 8 → ZMod 2) :=
    (AddEquiv.toMultiplicative.symm θ.symm).trans sixteenC8H1EightFrameEquiv
  let β' : V ≃+ (Fin 8 → ZMod 2) := β.toAddEquiv.trans γ
  have hβ' : ∀ g w, β' (ρ g w) = spinMu (e g) (β' w) := by
    intro g w
    let v : V₀ := β w
    have hkey : ((e g : MulAut SpinW)) (θ.symm (Multiplicative.ofAdd v)) =
        θ.symm (Multiplicative.ofAdd (ρ₀ g v)) := by
      have h1 := hθ g (θ.symm (Multiplicative.ofAdd v))
      rw [MulEquiv.apply_symm_apply] at h1
      have h2 := congrArg θ.symm h1
      rw [MulEquiv.symm_apply_apply] at h2
      simpa using h2
    have hx : β' (ρ g w) =
        fcoord (Multiplicative.toAdd (θ.symm (Multiplicative.ofAdd (ρ₀ g v)))) := by
      have h0 : β' (ρ g w) =
          fcoord (Multiplicative.toAdd (θ.symm (Multiplicative.ofAdd (β (ρ g w))))) := rfl
      rw [h0, hβ g w]
    have hw : β' w = fcoord (Multiplicative.toAdd
        (θ.symm (Multiplicative.ofAdd v))) := by
      have h0 : β' w = fcoord (Multiplicative.toAdd
          (θ.symm (Multiplicative.ofAdd (β w)))) := rfl
      rw [h0]
    rw [hx, spinMu_apply, hw, fvec_fcoord, ofAdd_toAdd, hkey]
  have hcard : Nat.card (CFSG.Quasithin.JonesParshall.H1 ρ) = 1 := by
    rw [card_H1_eq_of_card ρ hβ' (k := 1) (by
      rw [one_mul]
      exact congrArg (fun S : AddSubgroup (↥spinH → Fin 8 → ZMod 2) =>
        Nat.card ↥S) spinMu_Z1A_eq_B1A)]
  exact finrank_H1_of_card ρ (d := 0) (by rw [hcard, pow_zero])

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
