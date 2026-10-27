module

public import CFSG.Quasithin.Background.F918Z8Sz6Fd
public import CFSG.Quasithin.Background.F918Z8Su1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge
  CFSG.Blueprint CFSG.LieType.Ree CFSG.Quasithin.SzTorus

theorem suz_order_inj {x y : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y)
    (h : x ^ 2 * (x - 1) * (x ^ 2 + 1) = y ^ 2 * (y - 1) * (y ^ 2 + 1)) : x = y := by
  have key : ∀ x y : ℕ, 2 ≤ x → x < y →
      x ^ 2 * (x - 1) * (x ^ 2 + 1) < y ^ 2 * (y - 1) * (y ^ 2 + 1) := by
    intro x y hx hxy
    have h1 : x ^ 2 < y ^ 2 := Nat.pow_lt_pow_left hxy (by norm_num)
    have h2 : x - 1 < y - 1 := by omega
    have h3 : x ^ 2 + 1 < y ^ 2 + 1 := by omega
    exact Nat.mul_lt_mul'' (Nat.mul_lt_mul'' h1 h2) h3
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact absurd h (key x y hx hlt).ne
  · exact absurd h.symm (key y x hy hlt).ne

section Final

variable {Y : Type} [CommGroup Y] [Finite Y] {Γ Λ S : Subgroup (MulAut Y)} {V : Subgroup Y}

theorem suz_torus_fix_of_natural
    (h : LocCfg Γ Λ S V) {n : ℕ} (hn : IsSz n ↥Λ)
    (hnat : ∃ f, BinaryNaturalSz (autSub Λ V) ⊤ ⊥ f) :
    ∃ (P : Subgroup (MulAut Y)) (t : MulAut Y), IsSylowTwoOf P Λ ∧ t ∈ Λ ∧
      t ∈ Subgroup.normalizer (P : Set (MulAut Y)) ∧ orderOf t = 2 ^ n - 1 ∧
      ∀ U : Subgroup Y, (∀ l ∈ Λ, ∀ u ∈ U, l u ∈ U) →
        Nat.card ↥U = Nat.card ↥(U ⊓ fixV P) ^ 4 ∧
        ∀ k : ℕ, ¬ (2 ^ n - 1 ∣ k) → U ⊓ fixV P ⊓ fixV (Subgroup.zpowers (t ^ k)) = ⊥ := by
  obtain ⟨f, hf⟩ := hnat
  have hLV : Λ ≤ stabSub V := le_stabSub_of_forall_mem (loc_irr_data h).1
  have hfaith := loc_faithful h
  obtain ⟨a, K, _, _, hfa, hK, ⟨C⟩⟩ := szCoord_of_natural hLV hfaith hf
  rw [hfa] at hK
  obtain ⟨-, a₀, -, K₀, _, _, hn', hK₀, ⟨e⟩⟩ := hn
  rw [hn'] at hK₀
  have hc1 : Nat.card ↥Λ = (2 ^ (2 * a₀ + 1)) ^ 2 * (2 ^ (2 * a₀ + 1) - 1) *
      ((2 ^ (2 * a₀ + 1)) ^ 2 + 1) := by
    rw [Nat.card_congr e.toEquiv, suzuki_order hK₀]
  have hc2 : Nat.card ↥Λ = (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) *
      ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
    rw [Nat.card_congr C.θ.toEquiv, suzuki_order hK]
  have h2 : ∀ m : ℕ, 1 ≤ m → 2 ≤ 2 ^ m := fun m hm =>
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hq : 2 ^ (2 * a₀ + 1) = 2 ^ (2 * a + 1) :=
    suz_order_inj (h2 _ (by omega)) (h2 _ (by omega)) (hc1.symm.trans hc2)
  have hn2 : n = 2 * a + 1 := by
    rw [hn']
    exact Nat.pow_right_injective (le_refl 2) hq
  have hΓ : ∀ g ∈ Γ, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ := fun g hg l hl =>
    (Subgroup.mem_normalizer_iff.1 (h.std.hyp.Mp_normal hg) l).1 hl
  have := suz_torus_fix_of_coord C hK hΓ (loc_isIrr h) h.std.hyp.gen
  rw [hn2]
  exact this

theorem suz_torus_fix_proved
    (hB45 : AsB45) (hA21 : AsA21SQTKSection) (hF : Vol2.Ch10.SecA.Facts10_1)
    (hX : Insp5aNonShape) (h : LocCfg Γ Λ S V) {n : ℕ} (hn : IsSz n ↥Λ) :
    ∃ (P : Subgroup (MulAut Y)) (t : MulAut Y), IsSylowTwoOf P Λ ∧ t ∈ Λ ∧
      t ∈ Subgroup.normalizer (P : Set (MulAut Y)) ∧ orderOf t = 2 ^ n - 1 ∧
      ∀ U : Subgroup Y, (∀ l ∈ Λ, ∀ u ∈ U, l u ∈ U) →
        Nat.card ↥U = Nat.card ↥(U ⊓ fixV P) ^ 4 ∧
        ∀ k : ℕ, ¬ (2 ^ n - 1 ∣ k) → U ⊓ fixV P ⊓ fixV (Subgroup.zpowers (t ^ k)) = ⊥ :=
  suz_torus_fix_of_natural h hn (suz_natural hB45 hA21 hF hX h ⟨n, hn⟩)

end Final

end CFSG.Quasithin
