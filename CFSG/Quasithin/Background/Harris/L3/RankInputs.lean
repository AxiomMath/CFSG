module

public import CFSG.Quasithin.Background.Harris.L3.Main
public import CFSG.Quasithin.Background.Harris.L3.RankCrude

public section

namespace CFSG.Quasithin.G11.Harris.L3

open CFSG.Open
open scoped MatrixGroups

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem selfDual_of_equiv_dual [Finite V] {G : Type*} [Group G] {L : Subgroup (GLV V)}
    (π : G →* ↥L) (hπ : Function.Surjective π)
    (Φ : (repOfHom L π).Equiv (repOfHom L π).dual) : SelfDual L ⊤ := by
  classical
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  let e : ↥(⊤ : Submodule (ZMod 2) V) ≃ₗ[ZMod 2] V := Submodule.topEquiv
  let Ψ : V ≃ₗ[ZMod 2] Module.Dual (ZMod 2) V := Φ.toLinearEquiv
  have hΨ : ∀ g v, Ψ (repOfHom L π g v) = (repOfHom L π).dual g (Ψ v) := fun g v =>
    CFSG.QuasithinUnique.Setup.SL2Modules.equiv_apply Φ g v
  let B : LinearMap.BilinForm (ZMod 2) ↥(⊤ : Submodule (ZMod 2) V) :=
    LinearMap.mk₂ (ZMod 2) (fun i j => Ψ (e i) (e j))
      (fun i i' j => by simp) (fun c i j => by simp)
      (fun i j j' => by simp) (fun c i j => by simp)
  refine ⟨B, ⟨fun i hi => ?_, fun j hj => ?_⟩, fun k hk i j i' j' hi hj => ?_⟩
  ·
    have h0 : Ψ (e i) = 0 := by
      ext v
      have := hi (e.symm v)
      simpa [B] using this
    have : e i = 0 := Ψ.injective (by rw [h0, map_zero])
    exact e.injective (by rw [this, map_zero])
  ·
    have h0 : ∀ φ : Module.Dual (ZMod 2) V, φ (e j) = 0 := fun φ => by
      obtain ⟨v, rfl⟩ := Ψ.surjective φ
      have := hj (e.symm v)
      simpa [B] using this
    have : e j = 0 := (Module.forall_dual_apply_eq_zero_iff (ZMod 2) (e j)).mp h0
    exact e.injective (by rw [this, map_zero])
  · obtain ⟨g, hg⟩ := hπ ⟨k, hk⟩
    have hi' : e i' = repOfHom L π g (e i) := by
      rw [repOfHom_apply, hg]
      exact hi.symm
    have hj' : e j' = repOfHom L π g (e j) := by
      rw [repOfHom_apply, hg]
      exact hj.symm
    show Ψ (e i') (e j') = Ψ (e i) (e j)
    rw [hi', hj', hΨ, Representation.dual_apply]
    simp [Module.Dual.transpose_apply, ← Module.End.mul_apply, ← map_mul]

theorem rankSharp_holds : RankSharpInput := by
  intro V _ _ _ Γ A L m f hs hf π hπ hker hnsd
  let _inst : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  have hFcard : Fintype.card (GaloisField 2 f) = 2 ^ f := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 f (by omega)]
  exact m_le_of_sl3 hs hf hFcard π hπ hker fun ⟨Φ⟩ => hnsd (selfDual_of_equiv_dual π hπ Φ)

theorem rankCrude_holds : RankCrudeInput := by
  intro V _ _ _ Γ A L m f hs hf π hπ hker
  let _inst : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  have hFcard : Fintype.card (GaloisField 2 f) = 2 ^ f := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 f (by omega)]
  exact m_le_of_sl3_crude hs hf hFcard π hπ hker

theorem rankTwo_holds : RankTwoInput := by
  intro V _ _ _ Γ A L m hs π hπ hker
  let _inst : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have hFcard : Fintype.card (GaloisField 2 1) = 2 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 1 (by omega), pow_one]
  exact m_le_of_sl3_two hs hFcard π hπ hker

end CFSG.Quasithin.G11.Harris.L3
