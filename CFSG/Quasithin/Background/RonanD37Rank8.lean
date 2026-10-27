module

public import CFSG.Quasithin.Background.Module
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceFixedCodimensions

public section

namespace CFSG.Quasithin.RonanD37

open CFSG.Quasithin

theorem card_le_four_of_card_eight {Q : Type} [CommGroup Q] [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1)
    (h8 : Nat.card Q = 8) {E : Subgroup (MulAut Q)} (hE : IsElemAbelian2 E) :
    Nat.card E ≤ 4 := by
  letI : Module (ZMod 2) (Additive Q) := AddCommGroup.zmodModule (n := 2) fun x => by
    rw [two_nsmul]
    apply Additive.toMul.injective
    rw [toMul_add, ← pow_two]
    exact hQ _
  have hV : Module.finrank (ZMod 2) (Additive Q) = 3 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive Q)
    rw [Nat.card_zmod, show Nat.card (Additive Q) = 8 from h8] at h
    exact Nat.pow_right_injective le_rfl (h.symm.trans (by norm_num))
  let ψ : MulAut Q →* (Additive Q ≃ₗ[ZMod 2] Additive Q) :=
    { toFun := fun g => (MulEquiv.toAdditive g).toLinearEquiv fun c x => ZMod.map_smul _ c x
      map_one' := LinearEquiv.ext fun _ => rfl
      map_mul' := fun _ _ => LinearEquiv.ext fun _ => rfl }
  have hψ : Function.Injective ψ := fun g h hgh => MulEquiv.ext fun x =>
    Additive.ofMul.injective (DFunLike.congr_fun hgh (Additive.ofMul x))
  have : IsMulCommutative E := ⟨⟨fun a b => Subtype.ext (hE.1 a a.2 b b.2)⟩⟩
  have hBe : CFSG.Open.IsElemAbelian 2 (E.map ψ) := by
    refine ⟨inferInstance, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hE.2 a ha, map_one]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, hr⟩ := IsPGroup.iff_card.mp (show IsPGroup 2 E from fun g =>
    ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩)
  rcases eq_or_ne E ⊥ with rfl | hne
  · simp
  have hB : E.map ψ ≠ ⊥ := fun h => hne ((Subgroup.map_eq_bot_iff_of_injective E hψ).mp h)
  rcases (CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.GL3_elementary_abelian_fixed_codimensions
    hV (E.map ψ) hBe hB r ((Subgroup.card_map_of_injective hψ).trans hr)).1 with rfl | rfl <;>
    rw [hr] <;> norm_num

end CFSG.Quasithin.RonanD37
