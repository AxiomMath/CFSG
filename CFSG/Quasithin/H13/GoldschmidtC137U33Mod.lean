module

public import CFSG.Quasithin.H13.GoldschmidtC137U33Hyp
public import CFSG.Quasithin.H13.GoldschmidtC137U33Tr

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H.Mathieu (RealizesBy realizes_iff)

section Frame

variable {W M : Type} [CommGroup W] [CommGroup M] (e : W ≃* M)

theorem map_le_of_normalizer {X₀ L₀ : Subgroup (MulAut W)}
    (hXN : X₀ ≤ normalizer (L₀ : Set (MulAut W))) (Ĝ Ĥ : Subgroup (MulAut M))
    (hL : L₀.map (cg e) = Ĥ)
    (hN : ∀ x : MulAut M, (∀ h, h ∈ Ĥ ↔ x * h * x⁻¹ ∈ Ĥ) → x ∈ Ĝ) : X₀.map (cg e) ≤ Ĝ := by
  rintro _ ⟨a, ha, rfl⟩
  apply hN
  intro h
  have hx := Subgroup.mem_set_normalizer_iff.1 (hXN ha)
  rw [← hL]
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨a * l * a⁻¹, (hx l).1 hl, ?_⟩
    rw [map_mul, map_mul, map_inv]
  · rintro ⟨l, hl, hl'⟩
    refine ⟨a⁻¹ * l * a, ?_, ?_⟩
    · have e1 : a * (a⁻¹ * l * a) * a⁻¹ = l := by group
      exact (hx _).2 (by rw [e1]; exact hl)
    · rw [map_mul, map_mul, map_inv, hl']
      group

theorem eq_of_sandwich {Γ : Type*} [Group Γ] [Finite Γ] {L X G : Subgroup Γ} (hLX : L ≤ X)
    (hXG : X ≤ G) (hGL : Nat.card ↥G = 2 * Nat.card ↥L) (hne : ¬ X ≤ L) : X = G := by
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hLX
  have h2 : Nat.card ↥X ∣ Nat.card ↥G := Subgroup.card_dvd_of_le hXG
  have hLpos : 0 < Nat.card ↥L := Nat.card_pos
  rw [hk, hGL] at h2
  have h3 : k ∣ 2 := by
    have h4 : Nat.card ↥L * k ∣ Nat.card ↥L * 2 := by rwa [mul_comm 2] at h2
    exact (Nat.mul_dvd_mul_iff_left hLpos).1 h4
  rcases (Nat.dvd_prime Nat.prime_two).1 h3 with h1 | h5
  · exfalso
    apply hne
    have h6 : Nat.card ↥X ≤ Nat.card ↥L := by rw [hk, h1, mul_one]
    exact (Subgroup.eq_of_le_of_card_ge hLX h6).symm.le
  · have h6 : Nat.card ↥G ≤ Nat.card ↥X := by rw [hk, h5, hGL, mul_comm]
    exact Subgroup.eq_of_le_of_card_ge hXG h6

theorem facts_of_frame [Finite W] [Finite M] {X₀ L₀ : Subgroup (MulAut W)}
    {Gm Lm : Subgroup (MulAut M)} (hL : L₀.map (cg e) = Lm) (hXle : X₀.map (cg e) ≤ Gm)
    (hLX : L₀ ≤ X₀) (hcard : Nat.card ↥L₀ = 6048) (hoff : ∃ A, IsFFStarOffender X₀ A)
    (h : G2Facts Gm Lm) : G2Facts X₀ L₀ := by
  have hL' : Lm ≤ X₀.map (cg e) := hL ▸ Subgroup.map_mono hLX
  have hGL : Nat.card ↥Gm = 2 * Nat.card ↥Lm := by
    rw [h.card_X, ← hL, card_map_cg, hcard]
  have hne : ¬ X₀.map (cg e) ≤ Lm := by
    intro hle
    obtain ⟨A, hAX, hA1, hAe, hbest⟩ := hoff
    have hAm : A.map (cg e) ≤ Lm := (Subgroup.map_mono hAX).trans hle
    refine h.no_off (A.map (cg e)) hAm
      (fun h0 => hA1 ((Subgroup.map_eq_bot_iff_of_injective A (cg_injective e)).1 h0))
      ((isElemAbelian2_map_cg_iff e).2 hAe) ?_
    have h0 := hbest ⊥ bot_le
    rw [Subgroup.card_bot, B1.fixV_bot, Subgroup.card_top, one_mul] at h0
    rw [card_map_cg, card_fixV_map_cg, ← Nat.card_congr e.toEquiv]
    exact h0
  have hX : X₀.map (cg e) = Gm := eq_of_sandwich hL' hXle hGL hne
  exact G2Facts.of_equiv e hX hL h

end Frame

theorem g2Facts_of_natural (hcov : G2NaturalCover) (hnorm : G2DerivedNormalizerZorn)
    (hfacts : U33G2Facts) {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {X₀ L₀ : Subgroup (MulAut W)} (hLX : L₀ ≤ X₀) (hXN : X₀ ≤ normalizer (L₀ : Set (MulAut W)))
    (hcomm : commV L₀ = ⊤) (hnat : G2NaturalDerived L₀ ⊤ (fixV L₀) 1)
    (hcard : Nat.card ↥L₀ = 6048) (hoff : ∃ A, IsFFStarOffender X₀ A) : G2Facts X₀ L₀ := by
  rcases hcov W hW L₀ (fixV L₀) le_rfl hcomm hnat with hZ | ⟨-, -, hWeyl⟩
  · rw [hZ] at hnat
    obtain ⟨K, _, _, hK, hR⟩ := hnat
    have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
    have := charP_two_of_natCard_two hK2
    obtain ⟨π, β, hβ⟩ := (realizes_iff _ L₀ ⊤ ⊥).1 hR
    let e : W ≃* (FFModel.zornQ (quasithinG2 K)).Mod :=
      realizeEquiv (D := FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆) hβ
    have hL := map_congr_eq_of_equivariant e π hβ.1 (g2QAct K)
      (fun γ => ⟨γ.1, Subgroup.commutator_le_self _ γ.2⟩) (realizeEquiv_zornQ hβ) _
      (mem_map_g2Derived_iff (g2QAct K))
    exact facts_of_frame e hL (map_le_of_normalizer e hXN _ _ hL (hnorm K hK2).1) hLX hcard hoff
      (hfacts K hK2).1
  · obtain ⟨K, _, _, hK2, hR⟩ := hWeyl
    have := charP_two_of_natCard_two hK2
    obtain ⟨π, β, hβ⟩ := (realizes_iff _ L₀ ⊤ ⊥).1 hR
    let e : W ≃* (zornO0Model (quasithinG2 K)).Mod :=
      realizeEquiv (D := zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆) hβ
    have hL := map_congr_eq_of_equivariant e π hβ.1 (g2OAct K)
      (fun γ => ⟨γ.1, Subgroup.commutator_le_self _ γ.2⟩) (realizeEquiv_zornO0 hβ) _
      (mem_map_g2Derived_iff (g2OAct K))
    exact facts_of_frame e hL (map_le_of_normalizer e hXN _ _ hL (hnorm K hK2).2) hLX hcard hoff
      (hfacts K hK2).2

end CFSG.Quasithin.H13.U3.GC137
