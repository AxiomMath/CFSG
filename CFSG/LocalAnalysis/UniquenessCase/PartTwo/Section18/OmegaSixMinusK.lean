module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGroupProofsC
public import CFSG.Quasithin.EmptyFaithful.SzN15Nat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def K_Omega6Minus_outIndex : Prop :=
  ∀ {W : Type} [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (n : ℕ),
    2 ≤ n → IsOmegaMinus ↥H 6 n → NatOmegaMinus H ⊤ ⊥ 6 n →
      ∀ E : Subgroup (MulAut W), E ≤ normalizer (H : Set (MulAut W)) → IsElemAbelian2 E →
        E3.mQuot E (E ⊓ H) ≤ 1

theorem isU4_of_isOmegaMinus {X : Type} [Group X] {n : ℕ} (h : IsOmegaMinus X 6 n) :
    IsU4 X n := by
  obtain ⟨-, K, hKf, hKfin, b, c, hcard, hbc, ⟨e⟩⟩ := h
  exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.kOmega6MinusU4_holds
    (X := X) (n := n) (K := K) (b := b) (c := c) hcard hbc ⟨e⟩

theorem exists_natCoords_of_natOmegaMinus {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {n : ℕ} (hN : NatOmegaMinus H ⊤ ⊥ 6 n) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (b c : F), Nat.card F = 2 ^ n ∧
      (∀ s : F, s ^ 2 + b * s + c ≠ 0) ∧
      ∃ (ε : ↥H ≃* ↥(StatedOmega (StatedQuadMinus 3 F b c)))
        (ψ : ↥(⊤ : Subgroup W) ≃* Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F)),
        NatCoordsOmegaMinusOn H ⊤ (fun _ _ s _ => Subgroup.mem_top s) F b c ε ψ := by
  classical
  obtain ⟨-, K, hK, hKf, b, c, hK2, hpoly, π, hπ⟩ := hN
  letI := hK
  haveI : Finite K := hKf
  have hinj : Function.Injective π :=
    CFSG.Quasithin.FFModel.RealizesVia.injective_of_faithful
      (CFSG.Quasithin.FFModel.nat_faithful _) hπ
  obtain ⟨β, hβsurj, hβker, hβe⟩ := (CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ).exists_β
  have hβinj : Function.Injective β := by
    intro a a' hab
    have h1 : β (a * a'⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : ((a * a'⁻¹ : ↥(⊤ : Subgroup W)) : W) ∈ (⊥ : Subgroup W) := (hβker (a * a'⁻¹)).1 h1
    have h3 : a * a'⁻¹ = 1 := Subtype.ext (by simpa using Subgroup.mem_bot.1 h2)
    exact mul_inv_eq_one.1 h3
  let πe : ↥(StatedOmega (StatedQuadMinus 3 K b c)) ≃* ↥H := MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
  refine ⟨K, hK, hKf, b, c, hK2, hpoly, πe.symm, MulEquiv.ofBijective β ⟨hβinj, hβsurj⟩, ?_⟩
  intro l s
  obtain ⟨γ, rfl⟩ : ∃ γ, πe γ = l := πe.surjective l
  rw [MulEquiv.symm_apply_apply]
  exact hβe γ s (Subgroup.mem_top _)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
