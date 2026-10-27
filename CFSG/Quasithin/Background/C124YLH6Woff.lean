module

public import CFSG.Quasithin.Background.FixVLatticeSup
public import CFSG.Quasithin.Background.C124YLH6Ctx

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

public section

namespace CFSG.Quasithin.C124.YL.H6

open Matrix CFSG.Quasithin CFSG.Open

theorem isElemAbelian2_map_iff {Γ : Type*} [Group Γ] {W : Type*} [CommGroup W]
    {φ : Γ →* MulAut W} (hφ : Function.Injective φ) {B : Subgroup Γ} :
    IsElemAbelian2 (B.map φ) ↔
      (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧ ∀ a ∈ B, a * a = 1 :=
  CFSG.Quasithin.FixVLat.isElemAbelian2_map_iff hφ

theorem Z_le_liftFix_real {W : Type*} [CommGroup W] {Ls : Subgroup (MulAut W)} {U Z : Subgroup W}
    {D : FFModel} {π : D.Gam →* ↥Ls} (h : D.RealizesVia Ls U Z π) {B : Subgroup (MulAut W)}
    (hB : B ≤ Ls) : Z ≤ liftFix U Z B := by
  obtain ⟨-, hZU, -, -, hZst, -⟩ := h
  intro z hz
  refine mem_liftFix.2 ⟨hZU hz, fun b hb => ?_⟩
  exact Z.mul_mem (hZst ⟨b, hB hb⟩ z hz) (Z.inv_mem hz)

namespace HatCtx

variable {W : Type*} [CommGroup W] [Finite W] {K : Type} [Field K] [Finite K]
  {Γ₀ : Subgroup (GL (Fin 3) K)} {Ls : Subgroup (MulAut W)} {U Z : Subgroup W}
  (C : HatCtx K Γ₀ Ls U Z)

theorem natAct_eq_iff (γ : ↥Γ₀) (q : Multiplicative (Fin 3 → K)) :
    natAct Γ₀ γ q = q ↔ (mat Γ₀ γ).mulVec (Multiplicative.toAdd q) = Multiplicative.toAdd q := by
  constructor
  · intro h
    exact congrArg Multiplicative.toAdd h
  · intro h
    exact congrArg Multiplicative.ofAdd h

include C in
theorem phi_stab (γ : ↥Γ₀) (u : W) (hu : u ∈ U) : C.phi γ u ∈ U :=
  C.real.2.2.2.1 (C.π γ) u hu

theorem mem_fixImg_iff {c : ↥U →* Multiplicative (Fin 3 → K)} (hc : IsCoord U Z c)
    (hequiv : ∀ (γ : ↥Γ₀) (u : ↥U) (hu : C.phi γ (u : W) ∈ U),
      c ⟨C.phi γ (u : W), hu⟩ = natAct Γ₀ γ (c u))
    (B : Subgroup ↥Γ₀) (q : Multiplicative (Fin 3 → K)) :
    q ∈ fixImg U Z c (B.map C.phi) ↔ Multiplicative.toAdd q ∈ fixS B := by
  rw [hc.mem_fixImg_map C.phi (natAct Γ₀) (fun γ u hu => C.phi_stab γ u hu)
    (fun γ u => hequiv γ u (C.phi_stab γ u u.2)) B q]
  rw [mem_fixS]
  exact forall₂_congr fun γ _ => natAct_eq_iff γ q

theorem card_fixImg {c : ↥U →* Multiplicative (Fin 3 → K)} (hc : IsCoord U Z c)
    (hequiv : ∀ (γ : ↥Γ₀) (u : ↥U) (hu : C.phi γ (u : W) ∈ U),
      c ⟨C.phi γ (u : W), hu⟩ = natAct Γ₀ γ (c u))
    (B : Subgroup ↥Γ₀) : Nat.card (fixImg U Z c (B.map C.phi)) = Nat.card (fixS B) :=
  Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd fun q => C.mem_fixImg_iff hc hequiv B q)

theorem woff_map_iff (B : Subgroup ↥Γ₀) :
    WOff U Z (B.map C.phi) ↔ B ≠ ⊥ ∧ (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧ (∀ a ∈ B, a * a = 1) ∧
      64 ≤ Nat.card B * Nat.card (fixS B) := by
  obtain ⟨c, hc, hequiv⟩ := C.coord
  have hφ := C.phi_injective
  have hle : B.map C.phi ≤ Ls := fun x hx => by
    obtain ⟨g, -, rfl⟩ := Subgroup.mem_map.1 hx
    exact C.phi_mem g
  have hZB := Z_le_liftFix_real C.real hle
  have hbot : B.map C.phi ≠ ⊥ ↔ B ≠ ⊥ := by
    rw [Ne, Ne, Subgroup.map_eq_bot_iff_of_injective B hφ]
  rw [hc.woff_iff hZB, hbot, isElemAbelian2_map_iff hφ, C.card_Q, C.card_fixImg hc hequiv B,
    Subgroup.card_map_of_injective hφ, and_assoc]

end HatCtx

end CFSG.Quasithin.C124.YL.H6
