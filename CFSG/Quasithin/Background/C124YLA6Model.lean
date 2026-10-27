module

public import CFSG.Quasithin.Background.C124YLQuot
public import CFSG.Quasithin.Background.C124YLA6S1
public import CFSG.Quasithin.Background.C124YLA6Grp

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

public section

namespace CFSG.Quasithin.C124.YL.A6

open Equiv CFSG.Quasithin CFSG.Quasithin.G6 CFSG.Open

section Setup

variable {W : Type*} [CommGroup W] {Ls : Subgroup (MulAut W)}

@[expose] def phi (π : Gam →* ↥Ls) : Gam →* MulAut W := Ls.subtype.comp π

@[expose] def up (π : Gam →* ↥Ls) (H : Subgroup P6) : Subgroup (MulAut W) :=
  (H.subgroupOf (alternatingGroup (Fin 6))).map (phi π)

variable {π : Gam →* ↥Ls}

theorem mem_up {H : Subgroup P6} {x : MulAut W} :
    x ∈ up π H ↔ ∃ γ : Gam, (γ : P6) ∈ H ∧ phi π γ = x := by
  simp [up, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem up_le_Ls (H : Subgroup P6) : up π H ≤ Ls := fun x hx => by
  obtain ⟨γ, -, rfl⟩ := mem_up.1 hx
  exact (π γ).2

theorem up_mono {H H' : Subgroup P6} (h : H ≤ H') : up π H ≤ up π H' := fun x hx => by
  obtain ⟨γ, hγ, rfl⟩ := mem_up.1 hx
  exact mem_up.2 ⟨γ, h hγ, rfl⟩

theorem phi_injective (hinj : Function.Injective π) : Function.Injective (phi π) :=
  Subtype.val_injective.comp hinj

theorem card_up (hinj : Function.Injective π) {H : Subgroup P6}
    (hH : H ≤ alternatingGroup (Fin 6)) : Nat.card (up π H) = Nat.card H := by
  unfold up
  rw [Subgroup.card_map_of_injective (phi_injective hinj), card_subgroupOf_A6 hH]

theorem up_eq_bot_iff (hinj : Function.Injective π) {H : Subgroup P6}
    (hH : H ≤ alternatingGroup (Fin 6)) : up π H = ⊥ ↔ H = ⊥ := by
  rw [← Subgroup.card_eq_one, ← Subgroup.card_eq_one, card_up hinj hH]

theorem isElemAbelian2_up_iff (hinj : Function.Injective π) {H : Subgroup P6}
    (hH : H ≤ alternatingGroup (Fin 6)) :
    IsElemAbelian2 (up π H) ↔
      (∀ a ∈ H, ∀ b ∈ H, a * b = b * a) ∧ ∀ a ∈ H, a * a = 1 := by
  have hφ := phi_injective hinj
  constructor
  · rintro ⟨hc, hs⟩
    refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · let γa : Gam := ⟨a, hH ha⟩
      let γb : Gam := ⟨b, hH hb⟩
      have h1 := hc (phi π γa) (mem_up.2 ⟨γa, ha, rfl⟩) (phi π γb) (mem_up.2 ⟨γb, hb, rfl⟩)
      rw [← map_mul, ← map_mul] at h1
      exact congrArg Subtype.val (hφ h1)
    · let γa : Gam := ⟨a, hH ha⟩
      have h1 := hs (phi π γa) (mem_up.2 ⟨γa, ha, rfl⟩)
      rw [← map_pow] at h1
      have h2 : γa ^ 2 = 1 := hφ (by rw [h1, map_one])
      have h3 := congrArg Subtype.val h2
      simpa [pow_two] using h3
  · rintro ⟨hc, hs⟩
    refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
    · obtain ⟨γ, hγ, rfl⟩ := mem_up.1 hx
      obtain ⟨δ, hδ, rfl⟩ := mem_up.1 hy
      rw [← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext (hc _ hγ _ hδ))
    · obtain ⟨γ, hγ, rfl⟩ := mem_up.1 hx
      rw [← map_pow]
      have : γ ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hs _ hγ)
      rw [this, map_one]

end Setup

instance : Finite (FFModel.altDn 6).Amb := inferInstanceAs (Finite (PermMod 6))

section Counting

variable {W : Type*} [CommGroup W] [Finite W] {Ls : Subgroup (MulAut W)} {U Z : Subgroup W}
  {π : Gam →* ↥Ls}

theorem Z_le_liftFix (hR : (FFModel.altDn 6).RealizesVia Ls U Z π) {B : Subgroup (MulAut W)}
    (hB : B ≤ Ls) : Z ≤ liftFix U Z B := by
  obtain ⟨-, hZU, -, -, hZst, -⟩ := hR
  intro z hz
  refine mem_liftFix.2 ⟨hZU hz, fun b hb => ?_⟩
  exact Z.mul_mem (hZst ⟨b, hB hb⟩ z hz) (Z.inv_mem hz)

theorem card_U (hR : (FFModel.altDn 6).RealizesVia Ls U Z π) :
    Nat.card U = Nat.card Z * 16 := by
  obtain ⟨β, hc, -⟩ := coordQuot_of_realizes hR
  obtain ⟨-, -, hkerle, -⟩ := hR
  have h1 := hc.card_U
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((FFModel.altDn 6).ker.subgroupOf (FFModel.altDn 6).sec)
  have h3 : Nat.card ((FFModel.altDn 6).ker.subgroupOf (FFModel.altDn 6).sec) = 2 := by
    rw [← card_ker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerle).toEquiv
  have h4 : Nat.card ↥(FFModel.altDn 6).sec = 32 := card_core
  rw [h3, h4] at h2
  rw [h1]
  congr 1
  omega

theorem liftFix_card_up (hR : (FFModel.altDn 6).RealizesVia Ls U Z π)
    {H : Subgroup P6} (hH : H ≤ alternatingGroup (Fin 6)) {l : List P6}
    (hl : ∀ g, g ∈ l ↔ g ∈ H) :
    Nat.card ↥(liftFix U Z (up π H)) * 2 = Nat.card Z * cntL l := by
  obtain ⟨β, hc, hβ⟩ := coordQuot_of_realizes hR
  have hR' := hR
  obtain ⟨-, -, hkerle, hUst, -, hsec, -⟩ := hR'
  have hZB := Z_le_liftFix hR (up_le_Ls (π := π) H)
  have hfix : Nat.card ↥(liftFix U Z (up π H)) =
      Nat.card Z * Nat.card ↥(fixImg U Z β (up π H)) := hc.card_liftFix hZB
  have hcard := card_fixImg_model hc hβ hsec hUst hkerle (H.subgroupOf (alternatingGroup (Fin 6)))
  have hB : ∀ γ : Gam, γ ∈ H.subgroupOf (alternatingGroup (Fin 6)) ↔ (γ : P6) ∈ l := fun γ => by
    rw [Subgroup.mem_subgroupOf, hl]
  have hlA : ∀ g ∈ l, g ∈ alternatingGroup (Fin 6) := fun g hg => hH ((hl g).1 hg)
  have hcnt := card_fix_eq l hlA (H.subgroupOf (alternatingGroup (Fin 6))) hB
  have h5 : Nat.card ↥(fixImg U Z β (up π H)) * 2 = cntL l := by
    have h6 : Nat.card ↥(fixImg U Z β (up π H)) * Nat.card ↥(FFModel.altDn 6).ker = cntL l :=
      hcard.trans hcnt
    rwa [card_ker] at h6
  rw [hfix, mul_assoc, h5]

theorem woff_up_iff (hR : (FFModel.altDn 6).RealizesVia Ls U Z π) (hinj : Function.Injective π)
    {H : Subgroup P6} (hH : H ≤ alternatingGroup (Fin 6)) {l : List P6}
    (hl : ∀ g, g ∈ l ↔ g ∈ H) :
    WOff U Z (up π H) ↔ H ≠ ⊥ ∧ (∀ a ∈ H, ∀ b ∈ H, a * b = b * a) ∧ (∀ a ∈ H, a * a = 1) ∧
      32 ≤ Nat.card H * cntL l := by
  have hfl := liftFix_card_up hR hH hl
  have hU := card_U hR
  have hcard := card_up hinj hH
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have key : Nat.card Z * 16 ≤ Nat.card H * Nat.card ↥(liftFix U Z (up π H)) ↔
      32 ≤ Nat.card H * cntL l := by
    have h3 : Nat.card H * (Nat.card ↥(liftFix U Z (up π H)) * 2) =
        Nat.card H * (Nat.card Z * cntL l) := by rw [hfl]
    constructor
    · intro h
      have h2 : Nat.card Z * 32 ≤ Nat.card Z * (Nat.card H * cntL l) := by nlinarith
      exact Nat.le_of_mul_le_mul_left h2 hZpos
    · intro h
      have h2 : Nat.card Z * 32 ≤ Nat.card Z * (Nat.card H * cntL l) := Nat.mul_le_mul_left _ h
      nlinarith
  unfold WOff
  rw [Ne, up_eq_bot_iff hinj hH, isElemAbelian2_up_iff hinj hH, hU, hcard, key, and_assoc]

theorem card_Kg : Nat.card Kg = 4 := by
  rw [card_of_list (by decide +kernel : klist.Nodup) (fun g => Iff.rfl)]
  rfl

theorem card_Pg : Nat.card Pg = 8 := by
  rw [card_of_list plist_nodup (fun g => Iff.rfl)]
  rfl

theorem tight_up (hR : (FFModel.altDn 6).RealizesVia Ls U Z π) (hinj : Function.Injective π) :
    Nat.card U = Nat.card (up π Kg) * Nat.card ↥(liftFix U Z (up π Kg)) := by
  have hfl := liftFix_card_up hR Kg_le_A6 (l := klist) (fun g => Iff.rfl)
  rw [cntL_klist] at hfl
  rw [card_U hR, card_up hinj Kg_le_A6, card_Kg]
  omega

theorem card_Ls (hR : (FFModel.altDn 6).RealizesVia Ls U Z π) (hinj : Function.Injective π) :
    Nat.card ↥Ls = 360 := by
  rw [← card_Gam]
  exact (Nat.card_congr (Equiv.ofBijective π ⟨hinj, hR.1⟩)).symm

end Counting

end CFSG.Quasithin.C124.YL.A6
