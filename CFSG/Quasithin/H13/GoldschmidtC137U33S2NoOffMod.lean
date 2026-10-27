module

public import CFSG.Quasithin.H13.GoldschmidtC137U33S2NoOff
public import CFSG.Quasithin.H13.GoldschmidtC137U33S2Cls

public section

namespace CFSG.Quasithin.H13.U3.GC137.S2

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.Orbit
  CFSG.Quasithin.H13.G2Dat
open scoped Pointwise

theorem noOff_Gam {W : Type} [CommGroup W] (ρ : Gam →* MulAut W) (bound : ℕ)
    (hS : ∀ B : Subgroup Gam, B ≤ sSubG → B ≤ g2Derived (ZMod 2) → B ≠ ⊥ →
      (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → (∀ b ∈ B, b ^ 2 = 1) →
        bound ≤ (idx B).card * Nat.card (fixV (B.map ρ)) → False)
    {B : Subgroup Gam} (hBD : B ≤ g2Derived (ZMod 2)) (hB1 : B ≠ ⊥)
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hB2 : ∀ b ∈ B, b ^ 2 = 1)
    (hff : bound ≤ Nat.card B * Nat.card (fixV (B.map ρ))) : False := by
  have hp : IsPGroup 2 ↥B := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hB2 g.1 g.2)⟩
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Gam P sylowSub
  set c := (MulAut.conj g).toMonoidHom with hcdef
  have hcinj : Function.Injective c := (MulAut.conj g).injective
  set B₁ := B.map c with hB₁def
  have hB₁S : B₁ ≤ sSubG := by
    rintro _ ⟨b, hb, rfl⟩
    have h1 : MulAut.conj g • b ∈ MulAut.conj g • (P : Subgroup Gam) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ (hP hb)
    rw [← Sylow.coe_subgroup_smul, hg] at h1
    exact h1
  have hn : (g2Derived (ZMod 2)).Normal := by
    rw [g2Derived_eq_commutator]
    exact Subgroup.commutator_normal ⊤ ⊤
  have hB₁D : B₁ ≤ g2Derived (ZMod 2) := by
    rintro _ ⟨b, hb, rfl⟩
    exact hn.conj_mem _ (hBD hb) g
  have hB₁ne : B₁ ≠ ⊥ := by
    intro h
    exact hB1 ((Subgroup.map_eq_bot_iff_of_injective _ hcinj).1 h)
  have hB₁c : ∀ a ∈ B₁, ∀ b ∈ B₁, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hBc a ha b hb]
  have hB₁2 : ∀ b ∈ B₁, b ^ 2 = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_pow, hB2 b hb, map_one]
  have hmap : B₁.map ρ = (B.map ρ).map (MulAut.congr (ρ g)).toMonoidHom := by
    rw [hB₁def, Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext b m
    change ρ (g * b * g⁻¹) m = MulAut.congr (ρ g) (ρ b) m
    rw [congr_eq_conj, map_mul, map_mul, map_inv]
  have hcardB : Nat.card B₁ = Nat.card B := by
    rw [hB₁def, Subgroup.card_map_of_injective hcinj]
  have hfix : Nat.card (fixV (B₁.map ρ)) = Nat.card (fixV (B.map ρ)) := by
    rw [hmap, fixV_map_congr,
      Subgroup.card_map_of_injective (f := (ρ g).toMonoidHom) (ρ g).injective]
  exact hS B₁ hB₁S hB₁D hB₁ne hB₁c hB₁2
    (by rw [← card_eq_idx hB₁S, hcardB, hfix]; exact hff)

theorem noOff_map {W : Type} [CommGroup W] (ρ : Gam →* MulAut W) (hρ : Function.Injective ρ)
    (bound : ℕ)
    (h : ∀ B : Subgroup Gam, B ≤ g2Derived (ZMod 2) → B ≠ ⊥ →
      (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → (∀ b ∈ B, b ^ 2 = 1) →
        bound ≤ Nat.card B * Nat.card (fixV (B.map ρ)) → False) :
    ∀ B : Subgroup (MulAut W), B ≤ (g2Derived (ZMod 2)).map ρ → B ≠ ⊥ → IsElemAbelian2 B →
      bound ≤ Nat.card ↥B * Nat.card ↥(fixV B) → False := by
  intro B hB hBne hBe hff
  set B' : Subgroup Gam := B.comap ρ with hB'
  have hBB : B'.map ρ = B := Subgroup.map_comap_eq_self (hB.trans (Subgroup.map_le_range _ _))
  have hB'D : B' ≤ g2Derived (ZMod 2) := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hB hx
    rwa [← hρ hyx]
  have hc : Nat.card ↥B = Nat.card ↥B' := by
    conv_lhs => rw [← hBB]
    exact Subgroup.card_map_of_injective hρ
  refine h B' hB'D ?_ ?_ ?_ ?_
  · intro h0
    apply hBne
    rw [← hBB, h0, Subgroup.map_bot]
  · intro a ha b hb
    exact hρ (by rw [map_mul, map_mul]; exact hBe.1 _ (hBB ▸ ⟨a, ha, rfl⟩) _ (hBB ▸ ⟨b, hb, rfl⟩))
  · intro b hb
    exact hρ (by rw [map_pow, map_one]; exact hBe.2 _ (hBB ▸ ⟨b, hb, rfl⟩))
  · rw [hBB, ← hc]
    exact hff

end CFSG.Quasithin.H13.U3.GC137.S2

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.Orbit
  CFSG.Quasithin.H13.U3.GC137.S2

theorem noOff_Q :
    ∀ B : Subgroup (MulAut ModQ), B ≤ (g2Derived (ZMod 2)).map (g2QAct (ZMod 2)) → B ≠ ⊥ →
      IsElemAbelian2 B → Nat.card ModQ ≤ Nat.card ↥B * Nat.card ↥(fixV B) → False := by
  refine noOff_map _ g2QAct_injective _ ?_
  intro B hBD hB1 hBc hB2 hff
  refine noOff_Gam (g2QAct (ZMod 2)) (Nat.card ModQ) ?_ hBD hB1 hBc hB2 hff
  intro B hBS hBD hB1 hBc hB2 hff
  rw [card_ModQ] at hff
  obtain ⟨e, he, hiff, -⟩ := cls_Q hBS hB1 hBc hB2 hff
  exact noOff_S_of_cls hBD he hiff

theorem noOff_O :
    ∀ B : Subgroup (MulAut ModO), B ≤ (g2Derived (ZMod 2)).map (g2OAct (ZMod 2)) → B ≠ ⊥ →
      IsElemAbelian2 B → Nat.card ModO ≤ Nat.card ↥B * Nat.card ↥(fixV B) → False := by
  refine noOff_map _ g2OAct_injective _ ?_
  intro B hBD hB1 hBc hB2 hff
  refine noOff_Gam (g2OAct (ZMod 2)) (Nat.card ModO) ?_ hBD hB1 hBc hB2 hff
  intro B hBS hBD hB1 hBc hB2 hff
  rw [card_ModO] at hff
  obtain ⟨e, he, hiff, -⟩ := cls_O hBS hB1 hBc hB2 hff
  exact noOff_S_of_cls hBD he hiff

end CFSG.Quasithin.H13.U3.GC137
