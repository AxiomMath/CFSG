module

public import CFSG.Quasithin.Background.Sp4InfPair
public import CFSG.Quasithin.Background.SmithB42Sp4Nat

public section

namespace CFSG.Quasithin

namespace Sp4Inf

open CFSG.Assembly.LowTwoRank Matrix
open CFSG.Quasithin.H CFSG.Quasithin.H.PairG CFSG.Quasithin.H.Sp4
open CFSG.QuasithinUnique.Lin2.Five (tauSp)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem arith_pair_lt {e c₁ c₂ Q : ℕ} (he : 2 ≤ e) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (h1 : e ^ 2 * c₁ ^ 3 ≤ Q ^ 3) (h2 : e ^ 2 * c₂ ^ 3 ≤ Q ^ 3) : e * (c₁ * c₂) < Q ^ 2 := by
  by_contra hcon
  push Not at hcon
  have h3 : (Q ^ 2) ^ 3 ≤ (e * (c₁ * c₂)) ^ 3 := Nat.pow_le_pow_left hcon 3
  have h4 : (e ^ 2 * c₁ ^ 3) * (e ^ 2 * c₂ ^ 3) ≤ Q ^ 3 * Q ^ 3 := Nat.mul_le_mul h1 h2
  have h5 : (e * (c₁ * c₂)) ^ 3 * e ≤ (e * (c₁ * c₂)) ^ 3 * 1 := by
    calc (e * (c₁ * c₂)) ^ 3 * e = (e ^ 2 * c₁ ^ 3) * (e ^ 2 * c₂ ^ 3) := by ring
      _ ≤ Q ^ 3 * Q ^ 3 := h4
      _ = (Q ^ 2) ^ 3 := by ring
      _ ≤ (e * (c₁ * c₂)) ^ 3 := h3
      _ = (e * (c₁ * c₂)) ^ 3 * 1 := by ring
  have hpos : 0 < (e * (c₁ * c₂)) ^ 3 := by positivity
  have := Nat.le_of_mul_le_mul_left h5 hpos
  omega

theorem card_mul_fixV_lt_pair_lin {n : ℕ} (hK : Nat.card K = 2 ^ n)
    {B : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))} (hlin : B ≤ pairSp K)
    (hB2 : IsElemAbelian2 B) (hB1 : B ≠ ⊥) :
    Nat.card ↥B * Nat.card ↥(fixV B) < Nat.card (PairMod (Fin 2 ⊕ Fin 2) K) := by
  classical
  set f : StatedSp 2 K →* MulAut (PairMod (Fin 2 ⊕ Fin 2) K) :=
    pairHom (StatedSp 2 K) tauSp with hf
  have hfinj : Function.Injective f := by
    intro x y hxy
    rw [hf, pairHom_apply, pairHom_apply] at hxy
    exact natAut_injective (StatedSp 2 K) (pairAut_injective hxy).1
  set E : Subgroup (StatedSp 2 K) := B.comap f with hE
  have hEmap : E.map f = B := Subgroup.map_comap_eq_self hlin
  have hcard : Nat.card ↥B = Nat.card E := by
    rw [← hEmap]
    exact Subgroup.card_map_of_injective hfinj
  have hEsq : ∀ x ∈ E, x * x = 1 := fun x hx => by
    apply hfinj
    rw [map_mul, map_one, ← sq]
    exact hB2.2 _ (Subgroup.mem_comap.mp hx)
  have hE1 : E ≠ ⊥ := by
    intro hb
    apply hB1
    rw [← hEmap, hb, Subgroup.map_bot]
  set Γ₂ : Subgroup (StatedSp 2 K) := E.map tauSp with hΓ₂
  have hΓ₂sq : ∀ y ∈ Γ₂, y * y = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hEsq x hx, map_one]
  have hcard₂ : Nat.card Γ₂ = Nat.card E :=
    Subgroup.card_map_of_injective (CFSG.QuasithinUnique.Lin2.Five.tauSp_bijective (F := K)).1
  have hfix : Nat.card ↥(fixV B) ≤ Nat.card ↥(B42Sp4.fixK E) * Nat.card ↥(B42Sp4.fixK Γ₂) := by
    rw [← Nat.card_prod]
    refine Nat.card_le_card_of_injective
      (fun x => (⟨Multiplicative.toAdd x.1.1, fun γ hγ => ?_⟩,
        ⟨Multiplicative.toAdd x.1.2, fun δ hδ => ?_⟩)) ?_
    · have h := congrArg Prod.fst (x.2 (f γ) (Subgroup.mem_comap.mp hγ))
      exact congrArg Multiplicative.toAdd h
    · obtain ⟨γ, hγ, rfl⟩ := hδ
      have h := congrArg Prod.snd (x.2 (f γ) (Subgroup.mem_comap.mp hγ))
      exact congrArg Multiplicative.toAdd h
    · intro x y hxy
      have h1 := congrArg (fun p => p.1.1) hxy
      have h2 := congrArg (fun p => p.2.1) hxy
      exact Subtype.ext (Prod.ext (Multiplicative.toAdd.injective h1)
        (Multiplicative.toAdd.injective h2))
  have hcube₁ := B42Sp4.card_sq_mul_card_fixK_cube_le E hEsq
  have hcube₂ := B42Sp4.card_sq_mul_card_fixK_cube_le Γ₂ hΓ₂sq
  rw [hcard₂] at hcube₂
  have he : 2 ≤ Nat.card E := by
    have : Nat.card E ≠ 1 := fun h => hE1 (Subgroup.card_eq_one.1 h)
    have := Nat.card_pos (α := E)
    omega
  have hc₁ : 0 < Nat.card ↥(B42Sp4.fixK E) := Nat.card_pos
  have hc₂ : 0 < Nat.card ↥(B42Sp4.fixK Γ₂) := Nat.card_pos
  have hlt := arith_pair_lt he hc₁ hc₂ hcube₁ hcube₂
  have hV : Nat.card (PairMod (Fin 2 ⊕ Fin 2) K) = (Nat.card K ^ 4) ^ 2 := by
    rw [card_pairMod_sp hK, hK, ← pow_mul, ← pow_mul]
    congr 1
    ring
  rw [hV, hcard]
  exact lt_of_le_of_lt (Nat.mul_le_mul_left _ hfix) hlt

theorem card_mul_fixV_lt_pair {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {B : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))} (hBN : B ≤ pairNormSp K)
    (hBs : B ≤ pairSub (Fin 2 ⊕ Fin 2) K) (hB2 : IsElemAbelian2 B) (hB1 : B ≠ ⊥) :
    Nat.card ↥B * Nat.card ↥(fixV B) < Nat.card (PairMod (Fin 2 ⊕ Fin 2) K) := by
  have hV := card_pairMod_sp hK
  have hsq : ∀ x ∈ B, x * x = 1 := fun x hx => by rw [← sq]; exact hB2.2 x hx
  have hV1 : ∀ x ∈ B, (V₁ (Fin 2 ⊕ Fin 2) K).map x.toMonoidHom = V₁ (Fin 2 ⊕ Fin 2) K := by
    intro x hx
    obtain ⟨a, b, rfl⟩ := mem_pairSub_iff.mp (hBs hx)
    exact map_V₁_pairAut a b
  have hfix : ∀ X : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K)), X ≤ B →
      Nat.card ↥(fixV B) ≤ Nat.card ↥(fixV X) := fun X hX =>
    Subgroup.card_le_of_le (fun v hv x hx => hv x (hX hx))
  by_cases hlin : B ≤ pairSp K
  · exact card_mul_fixV_lt_pair_lin hK hlin hB2 hB1
  · obtain ⟨x₀, hx₀B, hx₀⟩ := IsConcreteLE.not_le_iff_exists.mp hlin
    have h1 := card_fixV_le_of_nonlinear hn hK (hBN hx₀B) (hsq x₀ hx₀B) (hV1 x₀ hx₀B) hx₀
    have h2 := hfix (Subgroup.zpowers x₀) (by rw [Subgroup.zpowers_le]; exact hx₀B)
    obtain ⟨c, hcB, hc1, -⟩ := exists_card_le hn hK hBN hsq hV1
    have h3 := card_inf_pairSp_le hK hB2
    have hc2 : c * 2 ^ n ≤ 2 ^ (2 * n - 1) := by rw [← hK]; exact hc1
    have hq : 2 ^ (2 * n - 1) * 2 = 2 ^ (2 * n) := by
      rw [← pow_succ]
      congr 1
      omega
    have hBle : 2 * Nat.card ↥B ≤ 2 ^ (4 * n) := by
      calc 2 * Nat.card ↥B ≤ 2 * (c * Nat.card ↥(B ⊓ pairSp K)) := Nat.mul_le_mul_left 2 hcB
        _ ≤ 2 * (c * 2 ^ (3 * n)) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left c h3)
        _ = 2 * (c * 2 ^ n) * 2 ^ (2 * n) := by
            rw [show 3 * n = n + 2 * n by ring, pow_add]
            ring
        _ ≤ 2 * 2 ^ (2 * n - 1) * 2 ^ (2 * n) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hc2)
        _ = 2 ^ (2 * n) * 2 ^ (2 * n) := by rw [mul_comm 2, hq]
        _ = 2 ^ (4 * n) := by
            rw [← pow_add]
            congr 1
            ring
    have hfx : Nat.card ↥(fixV B) ≤ 2 ^ (4 * n) := h2.trans h1
    have hpos : 0 < Nat.card ↥B * Nat.card ↥(fixV B) := Nat.mul_pos Nat.card_pos Nat.card_pos
    rw [hV]
    calc Nat.card ↥B * Nat.card ↥(fixV B) < 2 * (Nat.card ↥B * Nat.card ↥(fixV B)) := by omega
      _ = (2 * Nat.card ↥B) * Nat.card ↥(fixV B) := by ring
      _ ≤ 2 ^ (4 * n) * 2 ^ (4 * n) := Nat.mul_le_mul hBle hfx
      _ = 2 ^ (8 * n) := by
          rw [← pow_add]
          congr 1
          ring

end Sp4Inf

end CFSG.Quasithin
