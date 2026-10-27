module

public import CFSG.Quasithin.Background.F918T0
public import CFSG.Quasithin.Background.F918H3
import CFSG.Quasithin.Background.G64Realize

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open CFSG.Quasithin.B5.Ln (mat dmat)
open scoped Matrix

theorem exists_modelData
    (hbridge : ∃ Ψ : Multiplicative ↥(⋀[ZMod 2]^2 (Fin 5 → ZMod 2)) ≃* Multiplicative ↥(altMat 5),
      ∀ (γ : ↥(StatedSL 5 (ZMod 2))) (x : Multiplicative ↥(⋀[ZMod 2]^2 (Fin 5 → ZMod 2))),
        Ψ (extSqAct (ZMod 2) 5 γ x) = altMulAct γ (Ψ x))
    (hfaith : ∀ γ : ↥(StatedSL 5 (ZMod 2)), (∀ B, altMulAct γ B = B) → γ = 1)
    {X : Type} [CommGroup X] {Lb : Subgroup (MulAut X)} {V₁ : Subgroup X} (hLV : Lb ≤ stabSub V₁)
    (π : ↥(StatedSL 5 (ZMod 2)) →* ↥(autSub Lb V₁))
    (hπ : (FFModel.extSq (ZMod 2) 5).RealizesVia (autSub Lb V₁) ⊤ ⊥ π) :
    ∃ (θ : ↥Lb →* ↥(StatedSL 5 (ZMod 2))) (Θ : ↥V₁ ≃* Multiplicative ↥(altMat 5)),
      Function.Surjective θ ∧
        ∀ (l : ↥Lb) (v : ↥V₁), Θ ((resHomOn V₁ hLV l : MulAut ↥V₁) v) = altMulAct (θ l) (Θ v) := by
  obtain ⟨Ψ, hΨ⟩ := hbridge
  obtain ⟨E, hE⟩ := G64.RealizesVia.exists_secEquiv (D := FFModel.extSq (ZMod 2) 5) rfl hπ
  let Θ : ↥V₁ ≃* Multiplicative ↥(altMat 5) := (E.trans Subgroup.topEquiv).trans Ψ
  have hΘ : ∀ (γ : ↥(StatedSL 5 (ZMod 2))) (v : ↥V₁),
      Θ (((π γ : ↥(autSub Lb V₁)) : MulAut ↥V₁) v) = altMulAct γ (Θ v) := fun γ v =>
    (congrArg Ψ (hE γ v)).trans (hΨ γ _)
  have hinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    refine hfaith γ fun B => ?_
    obtain ⟨v, rfl⟩ := Θ.surjective B
    rw [← hΘ γ v, hγ]
    rfl
  let e : ↥(StatedSL 5 (ZMod 2)) ≃* ↥(autSub Lb V₁) := MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
  have hmem : ∀ l : ↥Lb, resHomOn V₁ hLV l ∈ autSub Lb V₁ := fun l => by
    rw [autSub_eq_range_resHomOn hLV]
    exact ⟨l, rfl⟩
  let ρ : ↥Lb →* ↥(autSub Lb V₁) := (resHomOn V₁ hLV).codRestrict (autSub Lb V₁) hmem
  have hρ : Function.Surjective ρ := by
    rintro ⟨φ, hφ⟩
    rw [autSub_eq_range_resHomOn hLV] at hφ
    obtain ⟨l, rfl⟩ := hφ
    exact ⟨l, rfl⟩
  refine ⟨e.symm.toMonoidHom.comp ρ, Θ, e.symm.surjective.comp hρ, fun l v => ?_⟩
  have hπl : π (e.symm (ρ l)) = ρ l := e.apply_symm_apply (ρ l)
  have h := hΘ (e.symm (ρ l)) v
  rw [hπl] at h
  exact h

end CFSG.Quasithin
