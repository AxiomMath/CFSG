module

public import CFSG.Quasithin.EmptyFaithful.SzN32Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin.SzN32

namespace SylowTransfer

def conjEquiv {K V W : Type*} [Semiring K] [AddCommMonoid V] [Module K V] [AddCommMonoid W]
    [Module K W] (e : V ≃ₗ[K] W) : (V ≃ₗ[K] V) ≃* (W ≃ₗ[K] W) where
  toFun f := e.symm.trans (f.trans e)
  invFun g := e.trans (g.trans e.symm)
  left_inv f := by ext; simp
  right_inv g := by ext; simp
  map_mul' f g := by ext; simp

theorem card_aut_fin_six :
    Nat.card ((Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)) = 20158709760 := by
  have h := Matrix.card_GL_field (𝔽 := ZMod 2) 6
  rw [← Nat.card_congr (Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 6 → ZMod 2))).toEquiv, h]
  simp [ZMod.card, Fin.prod_univ_six]

theorem not_dvd_index {G : Type*} [Group G] (hG : Nat.card G = 20158709760) {S : Subgroup G}
    (hS : Nat.card S = 81) : ¬ 3 ∣ S.index := by
  have h := S.card_mul_index
  rw [hG, hS] at h
  have h2 : S.index = 248872960 := by omega
  rw [h2]
  decide

theorem nonempty_mulEquiv {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 20158709760)
    {S T : Subgroup G} (hS : IsPGroup 3 S) (hS81 : Nat.card S = 81) (hT : Nat.card T = 81) :
    Nonempty (T ≃* S) := by
  have hTp : IsPGroup 3 T := IsPGroup.of_card (n := 4) (by rw [hT]; norm_num)
  let P : Sylow 3 G := hS.toSylow (not_dvd_index hG hS81)
  let Q : Sylow 3 G := hTp.toSylow (not_dvd_index hG hT)
  have : Finite (Sylow 3 G) := Sylow.finite_of_finiteIndex P
  exact ⟨Sylow.equiv Q P⟩

end SylowTransfer

theorem sylow_tdata
    (hmodel : ∃ T₀ : Subgroup ((Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)),
      Nat.card T₀ = 81 ∧ ∃ a σ : T₀, TData a σ)
    (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (hV : Module.finrank (ZMod 2) V = 6) (S : Subgroup (V ≃ₗ[ZMod 2] V)) (hS : IsPGroup 3 S)
    (hS81 : Nat.card S = 81) : ∃ a σ : S, TData a σ := by
  obtain ⟨T₀, hT₀, a, σ, hT⟩ := hmodel
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  let e : V ≃ₗ[ZMod 2] (Fin 6 → ZMod 2) :=
    LinearEquiv.ofFinrankEq V (Fin 6 → ZMod 2) (by rw [hV, Module.finrank_fin_fun])
  let Φ := SylowTransfer.conjEquiv e
  have : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun f : V ≃ₗ[ZMod 2] V => (f : V → V)) DFunLike.coe_injective
  have hcard : Nat.card (V ≃ₗ[ZMod 2] V) = 20158709760 := by
    rw [Nat.card_congr Φ.toEquiv, SylowTransfer.card_aut_fin_six]
  let T₁ : Subgroup (V ≃ₗ[ZMod 2] V) := T₀.map Φ.symm.toMonoidHom
  have hT₁ : Nat.card T₁ = 81 := by
    rw [Subgroup.card_map_of_injective Φ.symm.injective]
    exact hT₀
  let f₁ : T₀ ≃* T₁ := T₀.equivMapOfInjective Φ.symm.toMonoidHom Φ.symm.injective
  obtain ⟨f₂⟩ := SylowTransfer.nonempty_mulEquiv hcard hS hS81 hT₁
  exact ⟨f₂ (f₁ a), f₂ (f₁ σ), TData.of_mulEquiv (f₁.trans f₂) hT⟩

end CFSG.Quasithin.SzN32
