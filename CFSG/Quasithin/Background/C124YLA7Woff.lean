module

public import CFSG.Quasithin.Background.FixVLatticeSup
public import CFSG.Quasithin.Background.C124YLA7Ctx
public import CFSG.Quasithin.Background.C124YLTrans

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

public section

namespace CFSG.Quasithin.C124.YL.A7

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique.L246.C123

theorem isElemAbelian2_map_iff' {Γ : Type*} [Group Γ] {W : Type*} [CommGroup W]
    {φ : Γ →* MulAut W} (hφ : Function.Injective φ) {B : Subgroup Γ} :
    IsElemAbelian2 (B.map φ) ↔
      (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧ ∀ a ∈ B, a * a = 1 :=
  CFSG.Quasithin.FixVLat.isElemAbelian2_map_iff hφ

theorem Z_le_liftFix_real' {W : Type*} [CommGroup W] {Ls : Subgroup (MulAut W)}
    {U Z : Subgroup W} {D : FFModel} {π : D.Gam →* ↥Ls} (h : D.RealizesVia Ls U Z π)
    {B : Subgroup (MulAut W)} (hB : B ≤ Ls) : Z ≤ liftFix U Z B := by
  obtain ⟨-, hZU, -, -, hZst, -⟩ := h
  intro z hz
  refine mem_liftFix.2 ⟨hZU hz, fun b hb => ?_⟩
  exact Z.mul_mem (hZst ⟨b, hB hb⟩ z hz) (Z.inv_mem hz)

namespace A7Ctx

variable {W : Type*} [CommGroup W] [Finite W] {Ls : Subgroup (MulAut W)} {U Z : Subgroup W}
  (C : A7Ctx Ls U Z)

@[expose] def phi : A7 →* MulAut W := Ls.subtype.comp C.π

theorem phi_range : C.phi.range = Ls := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact (C.π g).2
  · intro hx
    obtain ⟨g, hg⟩ := C.real.1 ⟨x, hx⟩
    exact ⟨g, congrArg Subtype.val hg⟩

theorem phi_mem (g : A7) : C.phi g ∈ Ls := (C.π g).2

theorem map_phi_le (B : Subgroup A7) : B.map C.phi ≤ Ls := fun x hx => by
  obtain ⟨g, -, rfl⟩ := Subgroup.mem_map.1 hx
  exact C.phi_mem g

include C in
theorem coord : ∃ c : ↥U →* Q7, IsCoord U Z c ∧
    ∀ (σ : A7) (u : ↥U) (hu : C.phi σ (u : W) ∈ U),
      c ⟨C.phi σ (u : W), hu⟩ = a7Act C.α σ (c u) := by
  have hsec : ∀ q : (FFModel.a7Four C.α).Amb, q ∈ (FFModel.a7Four C.α).sec :=
    fun _ => Subgroup.mem_top _
  have hker : ∀ q ∈ (FFModel.a7Four C.α).ker, q = 1 := fun q hq => Subgroup.mem_bot.1 hq
  exact coord_of_realizes hsec hker C.real

theorem π_injective : Function.Injective C.π := by
  obtain ⟨c, hc, hequiv⟩ := C.coord
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro σ hσ
  have h1 : C.π σ = 1 := hσ
  have h2 : ∀ q : Q7, a7Act C.α σ q = q := by
    intro q
    obtain ⟨u, rfl⟩ := hc.surj q
    have hu : C.phi σ (u : W) ∈ U := C.real.2.2.2.1 (C.π σ) u u.2
    have e : C.phi σ (u : W) = (u : W) := by
      show ((C.π σ : ↥Ls) : MulAut W) (u : W) = u
      rw [h1]
      rfl
    exact (hequiv σ u hu).symm.trans (congrArg c (Subtype.ext e))
  have : rhoA C.α σ = 1 := MulEquiv.ext h2
  exact Subgroup.mem_bot.2 (rhoA_injective C.α (by rw [this, map_one]))

theorem phi_injective : Function.Injective C.phi := Subtype.val_injective.comp C.π_injective

theorem phi_stab (σ : A7) (u : W) (hu : u ∈ U) : C.phi σ u ∈ U :=
  C.real.2.2.2.1 (C.π σ) u hu

theorem mem_fixImg_iff {c : ↥U →* Q7} (hc : IsCoord U Z c)
    (hequiv : ∀ (σ : A7) (u : ↥U) (hu : C.phi σ (u : W) ∈ U),
      c ⟨C.phi σ (u : W), hu⟩ = a7Act C.α σ (c u))
    (B : Subgroup A7) (q : Q7) :
    q ∈ fixImg U Z c (B.map C.phi) ↔ q ∈ fixU (rhoA C.α) B := by
  have h1 := hc.mem_fixImg_map C.phi (a7Act C.α) (fun γ u hu => C.phi_stab γ u hu)
    (fun γ u => hequiv γ u (C.phi_stab γ u u.2)) B q
  refine h1.trans ?_
  exact (forall₂_congr fun γ _ => Iff.rfl : (∀ γ ∈ B, a7Act C.α γ q = q) ↔
    ∀ γ ∈ B, rhoA C.α γ q = q).trans (mem_fixU (ρ := rhoA C.α) (H := B) (u := q)).symm

theorem card_fixImg {c : ↥U →* Q7} (hc : IsCoord U Z c)
    (hequiv : ∀ (σ : A7) (u : ↥U) (hu : C.phi σ (u : W) ∈ U),
      c ⟨C.phi σ (u : W), hu⟩ = a7Act C.α σ (c u))
    (B : Subgroup A7) :
    Nat.card (fixImg U Z c (B.map C.phi)) = Nat.card (fixU (rhoA C.α) B) :=
  Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) fun q => C.mem_fixImg_iff hc hequiv B q)

theorem woff_map_iff (B : Subgroup A7) :
    WOff U Z (B.map C.phi) ↔ B ≠ ⊥ ∧ (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧ (∀ a ∈ B, a * a = 1) ∧
      16 ≤ Nat.card B * Nat.card (fixU (rhoA C.α) B) := by
  obtain ⟨c, hc, hequiv⟩ := C.coord
  have hφ := C.phi_injective
  have hZB := Z_le_liftFix_real' C.real (C.map_phi_le B)
  have hbot : B.map C.phi ≠ ⊥ ↔ B ≠ ⊥ := by
    rw [Ne, Ne, Subgroup.map_eq_bot_iff_of_injective B hφ]
  rw [hc.woff_iff hZB, hbot, isElemAbelian2_map_iff' hφ, card_Q7, C.card_fixImg hc hequiv B,
    Subgroup.card_map_of_injective hφ, and_assoc]

end A7Ctx

end CFSG.Quasithin.C124.YL.A7
